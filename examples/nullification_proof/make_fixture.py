"""Both off-chain sides of the TXE fixture, run by run.sh.

`make_fixture.py --vk [--update]` (no TXE needed) derives the owner
circuit's vk with `bb write_vk` and checks that the executor contract pins
its hash (OWNER_CIRCUIT_VK_HASH in executor/src/main.nr) and that
executor/src/owner_vk.nr, the copy the TXE tests pass, holds it. With
--update it rewrites both instead; do that after changing the owner
circuit. The vk is a function of the circuit alone, so both files are
committed.

`make_fixture.py <fixture-output.txt> <work-dir>` reads the FIXTURE lines
the executor's `fixture_values` test printed (the planted note's preimage
and nonce, the owner's nhk_app, the planted leaf and its nullifier, the
owner's registered pin, the executor E's and another executor's
addresses and E's anchor block number, as the TXE derives them), then
plays:

1. the owner B: handoffs (vk, proof, executor, expiry, fields, leaf,
   nullifier), each from prove_nullification with `nargo execute` and
   `bb prove -t noir-recursive` (ZK UltraHonk, the type A verifies).
   Unbound (executor = 0, expiry = 0):
   - honest:         the planted note, B's real key;
   - forged:         the planted note, another key (a proof that
                     verifies, but for public inputs A does not build: its
                     key commitment is not B's pin, its nullifier is not
                     the note's);
   - unsettled:      B's real key over a preimage that was never planted
                     (a proof that verifies for A's public inputs, of a
                     leaf that is not in the note hash tree).
   Bound, of the planted note with B's real key:
   - bound:          executor = E;
   - wrong executor: executor = the other executor;
   - expired:        expiry = E's anchor block number (anchor < expiry
                     fails: the window closed);
   - live:           expiry = E's anchor block number + 1;
   - claimed unbound: the bound proof handed over claiming executor = 0
                     (a proof for other public inputs);
2. the executor E: the off-chain pre-check (README.md, "The executor's
   pre-check"), of which this is the reference implementation:
   a. build the public-input array itself, in the layout of
      nullification_public_inputs, from A's address, the slot, the owner,
      B's claimed executor, expiry, fields, leaf and nullifier, and
      pin_of(owner) read from A; B's own public_inputs.json is input to
      nothing;
   b. take the vk A pins: E derives the owner circuit's vk itself
      (`bb write_vk`) and checks its hash equals A's OWNER_CIRCUIT_VK_HASH;
   c. `bb verify` B's proof against E's vk and E's array; pass the
      withheld handoff if it fails;
   then, as predictions of A's flags (A reads each failure as
   ok = false in-circuit):
   d. the binding, with A's flags: executor_ok (executor is 0 or E's own
      address, the msg_sender of E's call to A) and expiry_ok (expiry is
      0 or above the anchor block number E's PXE will use); pass the
      withheld handoff if either fails;
   e. settledness (the leaf in the note hash tree; E then adds its
      index and sibling path to the handoff) and freshness (the nullifier
      not yet in the nullifier tree). A deployment asks an Aztec node (findLeavesIndexes on the
      note hash and nullifier trees, and the block number its PXE
      anchors to); here the trees are the TXE's, whose settled leaves for
      this contract are the one planted leaf and which holds no nullifier
      of this note yet, and the anchor is fixture_values' value;
3. write target/fixture/fixture.json (gitignored) with the values, E's
   vk, each handoff and the pre-check's verdicts, for outer_check.py.

Exits nonzero unless the honest proof's leaf, nullifier and key
commitment are the ones aztec-nr computes in the TXE, and the pre-check
verdicts are the expected ones: honest, bound and live passed; forged and
claimed unbound fail at step c; unsettled verifies but is not settled;
wrong executor and expired verify but fail step d. The TXE tests pass
handoffs as E would after these verdicts (the TXE does not check proofs,
so they pass zero proof bytes).

Usage: make_fixture.py --vk [--update]
       make_fixture.py <fixture-output.txt> <work-dir>
"""
import json, os, re, subprocess, sys, tempfile

P = 0x30644E72E131A029B85045B68181585D2833E84879B9709143E1F593F0000001
here = os.path.dirname(os.path.abspath(__file__))
owner_dir = os.path.join(here, "prove_nullification")
circuit = os.path.join(owner_dir, "target", "prove_nullification.json")
main_nr = os.path.join(here, "executor", "src", "main.nr")
vk_nr = os.path.join(here, "executor", "src", "owner_vk.nr")
fixture_json = os.path.join(here, "target", "fixture", "fixture.json")


def run(cmd, cwd=None, check=True):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if check and r.returncode != 0:
        sys.exit(f"{' '.join(cmd)} failed:\n{r.stdout}\n{r.stderr}")
    return r


def h64(x):
    return "0x" + format(int(x, 16) if isinstance(x, str) else x, "064x")


def owner_prove(work, tag, vals, randomness, nhk_app, executor="0x00", expiry="0x00"):
    """B's side: prove prove_nullification and return B's handoff."""
    prover = os.path.join(work, f"Prover-{tag}.toml")
    with open(prover, "w") as f:
        for k in ["contract_address", "storage_slot", "owner"]:
            f.write(f'{k} = "{vals[k]}"\n')
        f.write(f'executor = "{executor}"\nexpiry = "{expiry}"\n')
        f.write(f'fields = ["{vals["value"]}"]\n')
        f.write(f'randomness = "{randomness}"\nnonce = "{vals["nonce"]}"\nnhk_app = "{nhk_app}"\n')
    run(["nargo", "execute", "--silence-warnings", "-p", prover, f"owner_{tag}"], cwd=owner_dir)
    d = os.path.join(work, f"owner-{tag}")
    run(["bb", "prove", "-t", "noir-recursive", "--output_format", "json", "--write_vk",
         "-b", circuit, "-w", os.path.join(owner_dir, "target", f"owner_{tag}.gz"), "-o", d])
    pis = json.load(open(f"{d}/public_inputs.json"))["public_inputs"]
    vk = json.load(open(f"{d}/vk.json"))["vk"]
    proof = json.load(open(f"{d}/proof.json"))["proof"]
    if len(vk) != 115 or len(proof) != 458 or len(pis) != 9:
        sys.exit(f"{tag}: unexpected sizes: vk {len(vk)}, proof {len(proof)}, public inputs {len(pis)}")
    # What B hands E: the vk and proof, and the bound values A cannot
    # compute (executor, expiry, fields, leaf, nullifier). The rest of B's
    # public-input list is not handed over: E rebuilds it.
    return dict(vk=vk, proof=proof, proof_file=f"{d}/proof.json", executor=pis[3], expiry=pis[4],
                fields=pis[5:6], leaf=pis[6], nullifier=pis[7], npk_app_hash=pis[8])


def executor_vk(work, update=False):
    """Pre-check step b: E's own vk of the owner circuit, pinned by A.

    Also checks the copy in executor/src/owner_vk.nr, which the TXE tests
    pass. With update, rewrites that file and A's pin instead of failing.
    """
    d = os.path.join(work, "executor")
    run(["bb", "write_vk", "-t", "noir-recursive", "--output_format", "json", "-b", circuit, "-o", d])
    vk = json.load(open(f"{d}/vk.json"))
    if len(vk["vk"]) != 115:
        sys.exit(f"unexpected vk size {len(vk['vk'])}")
    main_src = open(main_nr).read()
    pin_re = r"(OWNER_CIRCUIT_VK_HASH: Field =\s*)(0x[0-9a-f]+)"
    pinned = re.search(pin_re, main_src)
    vk_src = owner_vk_source(vk["vk"])
    stale_pin = not pinned or int(pinned.group(2), 16) != int(vk["hash"], 16)
    stale_vk = not os.path.exists(vk_nr) or open(vk_nr).read() != vk_src
    if update:
        if stale_pin:
            open(main_nr, "w").write(re.sub(pin_re, lambda m: m.group(1) + h64(vk["hash"]), main_src))
            print(f"make_fixture: OWNER_CIRCUIT_VK_HASH set to {vk['hash']}")
        if stale_vk:
            open(vk_nr, "w").write(vk_src)
            print("make_fixture: wrote executor/src/owner_vk.nr")
    elif stale_pin or stale_vk:
        sys.exit(f"the owner circuit's vk (hash {vk['hash']}) is not the one "
                 + ("executor/src/main.nr pins" if stale_pin else "executor/src/owner_vk.nr holds")
                 + ": rerun with --vk --update after changing the owner circuit")
    return vk, f"{d}/vk.json"


def owner_vk_source(vk):
    """executor/src/owner_vk.nr, laid out as nargo fmt leaves it."""
    return ("//! The owner circuit's verification key, `bb write_vk -t noir-recursive\n"
            "//! --output_format json` on prove_nullification (bb 6.0.0), for the TXE\n"
            "//! tests to stage: A checks its hash against OWNER_CIRCUIT_VK_HASH.\n"
            "//! Written and checked by make_fixture.py (--vk --update rewrites it).\n\n"
            "pub global OWNER_VK: [Field; 115] = [\n"
            + "".join(f"    {h64(x)},\n" for x in vk) + "];\n")


def executor_ok(executor, me):
    """total_aztec's executor_ok, with E's own address as A's msg_sender."""
    return executor == 0 or executor == me


def expiry_ok(expiry, anchor):
    """total_aztec's expiry_ok: Field values compare as integers 0..p-1."""
    return expiry == 0 or anchor < expiry


def precheck(work, tag, a, handoff, vk_file, settled_leaves, spent_nullifiers):
    """E's pre-check on one handoff: (verifies, binding, settled, fresh)."""
    # step a: E's own public-input array (nullification_public_inputs)
    pis = [a["contract_address"], a["storage_slot"], a["owner"], handoff["executor"],
           handoff["expiry"], *handoff["fields"], handoff["leaf"], handoff["nullifier"], a["pin"]]
    pis_file = os.path.join(work, "executor", f"public_inputs-{tag.replace(' ', '_')}.json")
    json.dump({"public_inputs": [h64(x) for x in pis]}, open(pis_file, "w"))
    # step c: native verify against E's vk and E's array
    verifies = run(["bb", "verify", "-t", "noir-recursive", "-k", vk_file,
                    "-p", handoff["proof_file"], "-i", pis_file], check=False).returncode == 0
    # liveness conveniences: step d, the binding as A checks it; step e
    binding = (executor_ok(int(handoff["executor"], 16), int(a["executor"], 16))
               and expiry_ok(int(handoff["expiry"], 16), int(a["anchor"], 16)))
    settled = int(handoff["leaf"], 16) in settled_leaves
    fresh = int(handoff["nullifier"], 16) not in spent_nullifiers
    passed = verifies and binding
    print(f"make_fixture: pre-check {tag:15} native verify against E's inputs "
          f"{'passes' if verifies else 'FAILS'}; binding {'admits E' if binding else 'REFUSES E'}"
          f"; settled {settled}; fresh {fresh}; {'pass it' if passed else 'pass the withheld handoff'}")
    return verifies, binding, settled, fresh


def main():
    if sys.argv[1:2] == ["--vk"]:
        with tempfile.TemporaryDirectory() as work:
            executor_vk(work, update="--update" in sys.argv[2:])
        return
    fixture_txt, work = sys.argv[1], sys.argv[2]
    vals = {}
    for line in open(fixture_txt):
        m = re.match(r"FIXTURE (\w+) (?:AztecAddress \{ inner: )?(0x[0-9a-f]+)", line.strip())
        if m:
            vals[m.group(1)] = m.group(2)
    need = ["contract_address", "storage_slot", "owner", "value", "randomness", "nonce", "nhk_app",
            "leaf", "nullifier", "pin", "executor", "other", "anchor"]
    missing = [k for k in need if k not in vals]
    if missing:
        sys.exit(f"fixture output lacks {missing}")
    os.makedirs(os.path.join(work, "executor"), exist_ok=True)
    vk, vk_file = executor_vk(work)

    nhk = int(vals["nhk_app"], 16)
    anchor = int(vals["anchor"], 16)
    real = (vals["randomness"], vals["nhk_app"])
    handoffs = {
        "honest": owner_prove(work, "honest", vals, *real),
        "forged": owner_prove(work, "forged", vals, vals["randomness"], hex((nhk + 1) % P)),
        "unsettled": owner_prove(work, "unsettled", vals, hex(int(vals["randomness"], 16) + 1),
                                 vals["nhk_app"]),
        "bound": owner_prove(work, "bound", vals, *real, executor=vals["executor"]),
        "wrong executor": owner_prove(work, "wrong_executor", vals, *real, executor=vals["other"]),
        "expired": owner_prove(work, "expired", vals, *real, expiry=hex(anchor)),
        "live": owner_prove(work, "live", vals, *real, expiry=hex(anchor + 1)),
    }
    handoffs["claimed unbound"] = dict(handoffs["bound"], executor="0x00")
    hon = handoffs["honest"]
    # The owner circuit's formulas against aztec-nr's, as the TXE computes them.
    for name, got, want in [("leaf", hon["leaf"], vals["leaf"]),
                            ("nullifier", hon["nullifier"], vals["nullifier"]),
                            ("npk_app_hash", hon["npk_app_hash"], vals["pin"])]:
        if int(got, 16) != int(want, 16):
            sys.exit(f"owner circuit {name} {got} differs from aztec-nr's {want}")
    for t in ["forged", "bound", "wrong executor", "expired", "live"]:
        if handoffs[t]["leaf"] != hon["leaf"]:
            sys.exit(f"{t} handoff should claim the planted leaf")
    for t in ["bound", "wrong executor", "expired", "live"]:
        if handoffs[t]["nullifier"] != hon["nullifier"]:
            sys.exit(f"{t} handoff should carry the note's nullifier: the binding changes no output")

    a = {k: vals[k] for k in ["contract_address", "storage_slot", "owner", "pin", "executor", "anchor"]}
    settled_leaves = {int(vals["leaf"], 16)}
    spent_nullifiers = set()
    verdict = {t: precheck(work, t, a, h, vk_file, settled_leaves, spent_nullifiers)
               for t, h in handoffs.items()}
    want = {"honest": (True, True, True, True), "forged": (False, True, True, True),
            "unsettled": (True, True, False, True), "bound": (True, True, True, True),
            "wrong executor": (True, False, True, True), "expired": (True, False, True, True),
            "live": (True, True, True, True), "claimed unbound": (False, True, True, True)}
    if verdict != want:
        sys.exit(f"pre-check verdicts {verdict}, expected {want}")

    os.makedirs(os.path.dirname(fixture_json), exist_ok=True)
    keep = ["proof", "executor", "expiry", "fields", "leaf", "nullifier", "npk_app_hash"]
    json.dump({"values": {k: h64(v) for k, v in vals.items()}, "vk": vk["vk"], "vk_hash": vk["hash"],
               "handoffs": {t: {k: h[k] for k in keep} for t, h in handoffs.items()},
               "verdicts": {t: dict(zip(["verifies", "binding", "settled", "fresh"], v))
                            for t, v in verdict.items()}},
              open(fixture_json, "w"), indent=1)
    print(f"make_fixture: wrote {os.path.relpath(fixture_json, here)}")


main()
