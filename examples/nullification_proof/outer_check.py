"""Prove and verify executor_outer with bb on the owner's real proof.

Reads target/fixture/fixture.json, which make_fixture.py writes (the
owner's proofs, what they bind, and the TXE's values), and runs these
cases through nargo execute, bb prove and bb verify (-t noir-recursive,
the circuit's own vk). The caller is the executor E and the anchor block
is E's unless stated:

- consume:         present, real proof, A's real public inputs  -> ok = 1
- withheld:        present = false, garbage vk and proof          -> ok = 0
- forged pin:      present, real proof, pin = a different key's   -> no proof
- other contract:  present, real proof, another contract address  -> no proof
- forged key:      present, B's proof made with another key, its
                   nullifier, A's real pin                        -> no proof
- bound:           B's proof bound to E                           -> ok = 1
- wrong executor:  B's proof bound to another executor            -> ok = 0
- named executor:  the same proof, called by that executor        -> ok = 1
- expired:         B's proof expiring at E's anchor block         -> ok = 0
- live:            B's proof expiring one block later             -> ok = 1
- claimed unbound: the proof bound to E, passed as executor = 0   -> no proof

Witness generation succeeds in all (the ACVM does not check recursive
proofs). The "no proof" cases fail at bb prove: a proof checked against
public inputs it was not made for, which is the executor's case "a
proof valid for other public inputs" seen from inside A (make_fixture.py's
pre-check rejects each such handoff). A binding that does not admit the
call proves with ok = 0: it is a flag, so E's transaction stays
provable. Exits nonzero if any case behaves otherwise.

Usage: outer_check.py <work-dir>
"""
import json, os, subprocess, sys

here = os.path.dirname(os.path.abspath(__file__))
pkg = os.path.join(here, "executor_outer")
fixture = os.path.join(here, "target", "fixture", "fixture.json")
if not os.path.exists(fixture):
    sys.exit(f"{os.path.relpath(fixture, here)} missing: run.sh (with the TXE) writes it")
fx = json.load(open(fixture))
val, ho = fx["values"], fx["handoffs"]


def proof(tag):
    return ho[tag]["proof"]


base = dict(present="true", vk=fx["vk"], proof=proof("honest"), fields=ho["honest"]["fields"],
            leaf=ho["honest"]["leaf"], nullifier=ho["honest"]["nullifier"],
            contract_address=val["contract_address"], storage_slot=val["storage_slot"],
            owner=val["owner"], pinned_npk_app_hash=val["pin"], expected_vk_hash=fx["vk_hash"],
            executor="0x00", expiry="0x00", msg_sender=val["executor"],
            anchor_block_number=str(int(val["anchor"], 16)))
# (name, changes, expected ok: 1 or 0 for a proof, None for no proof)
cases = [
    ("consume", {}, 1),
    ("withheld", dict(present="false", vk=[hex(0x1000 + i) for i in range(115)],
                      proof=[hex(0xabc000 + 7 * i) for i in range(458)]), 0),
    ("forged pin", dict(pinned_npk_app_hash="0x1234"), None),
    ("other contract", dict(contract_address="0x0c0ffee"), None),
    ("forged key", dict(proof=proof("forged"), nullifier=ho["forged"]["nullifier"]), None),
    ("bound", dict(proof=proof("bound"), executor=ho["bound"]["executor"]), 1),
    ("wrong executor", dict(proof=proof("wrong executor"), executor=ho["wrong executor"]["executor"]), 0),
    ("named executor", dict(proof=proof("wrong executor"), executor=ho["wrong executor"]["executor"],
                            msg_sender=val["other"]), 1),
    ("expired", dict(proof=proof("expired"), expiry=ho["expired"]["expiry"]), 0),
    ("live", dict(proof=proof("live"), expiry=ho["live"]["expiry"]), 1),
    ("claimed unbound", dict(proof=proof("bound")), None),
]


def toml(values):
    out = []
    for k, v in values.items():
        if isinstance(v, list):
            out.append(f"{k} = [" + ", ".join(f'"{x}"' for x in v) + "]")
        elif v in ("true", "false"):
            out.append(f"{k} = {v}")
        else:
            out.append(f'{k} = "{v}"')
    return "\n".join(out) + "\n"


work = sys.argv[1]
os.makedirs(work, exist_ok=True)
circuit = os.path.join(pkg, "target", "executor_outer.json")
bad = 0
for name, change, want_ok in cases:
    want_proof = want_ok is not None
    tag = name.replace(" ", "_")
    prover = os.path.join(work, f"Prover-{tag}.toml")
    open(prover, "w").write(toml({**base, **change}))
    ex = subprocess.run(["nargo", "execute", "--silence-warnings", "-p", prover, f"w_{tag}"],
                        cwd=pkg, capture_output=True, text=True)
    executed = ex.returncode == 0
    d = os.path.join(work, tag)
    pr = subprocess.run(["bb", "prove", "-t", "noir-recursive", "--output_format", "json", "--write_vk",
                         "-b", circuit, "-w", os.path.join(pkg, "target", f"w_{tag}.gz"), "-o", d],
                        capture_output=True, text=True) if executed else None
    proved = bool(pr) and pr.returncode == 0
    verified = proved and subprocess.run(
        ["bb", "verify", "-t", "noir-recursive", "-k", f"{d}/vk.json", "-p", f"{d}/proof.json",
         "-i", f"{d}/public_inputs.json"], capture_output=True, text=True).returncode == 0
    got_ok = int(json.load(open(f"{d}/public_inputs.json"))["public_inputs"][-1], 16) if verified else None
    ok = executed and (proved and verified) == want_proof and got_ok == want_ok
    bad += not ok
    print(f"{name:15} execute {'ok' if executed else 'FAIL'}  prove {'ok' if proved else 'fails'}"
          f"  verify {'ok' if verified else '-'}"
          f"  {'ok = ' + str(got_ok) if verified else '':6}"
          f"  expected {'ok = ' + str(want_ok) if want_proof else 'no proof'}"
          f"  {'PASS' if ok else 'UNEXPECTED'}")
    if pr is not None and not proved:
        reason = [l for l in (pr.stdout + pr.stderr).splitlines() if "fail" in l.lower() or "assert" in l.lower()]
        print(f"{'':15} bb: {reason[-1].strip() if reason else 'nonzero exit'}")
sys.exit(1 if bad else 0)
