import json, sys
inner, case, out = sys.argv[1], sys.argv[2], sys.argv[3]
vk = json.load(open(f"{inner}/vk.json"))
pf = json.load(open(f"{inner}/proof.json"))
pi = json.load(open(f"{inner}/public_inputs.json"))["public_inputs"]
present, data = case.split("-")
if data == "valid":
    v, p, h, y = vk["vk"], pf["proof"], vk["hash"], pi[0]
elif data == "garbage":
    # deterministic garbage: small distinct field elements, no structure
    v = [hex(0x1000 + i) for i in range(115)]
    p = [hex(0xabc000 + 7 * i) for i in range(458)]
    h, y = "0x1234", "0x9"
elif data == "zero":
    v, p, h, y = ["0x0"] * 115, ["0x0"] * 458, "0x0", "0x0"
elif data == "tampered":
    # the real vk and proof with one proof field changed
    v, p, h, y = vk["vk"], list(pf["proof"]), vk["hash"], pi[0]
    p[200] = hex(int(p[200], 16) ^ 1)
elif data == "wrongpi":
    v, p, h, y = vk["vk"], pf["proof"], vk["hash"], "0xa"
elif data == "wronghash":
    v, p, h, y = vk["vk"], pf["proof"], "0x1234", pi[0]
q = lambda xs: "[" + ", ".join(f'"{x}"' for x in xs) + "]"
with open(out, "w") as f:
    f.write(f'present = {"true" if present == "true" else "false"}\n')
    f.write(f"vk = {q(v)}\nproof = {q(p)}\nkey_hash = \"{h}\"\ny = \"{y}\"\n")
