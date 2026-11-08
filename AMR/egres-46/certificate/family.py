# Generalised tricycles: three cycles C_i (length L_i, v_i^- = c_i0,
# v_i^+ = c_i p_i), transition paths v_i^+ -> v_{i+1}^- of length t_i, and
# spokes of length s from a centre to the six transition vertices.  For each,
# compute dgon(G) and dgon(sigma_k G) for k in KS with ./dgon, and report any
# k (odd) with a drop.  Usage: python3 family.py
import itertools, subprocess, sys
def graph(Ls, ps, ts, s):
    n = 1; edges = []; tv = []
    def path(a, b, length):
        nonlocal n
        prev = a
        for _ in range(length - 1):
            edges.append((prev, n)); prev = n; n += 1
        edges.append((prev, b))
    cyc = []
    for L, p in zip(Ls, ps):
        vs = list(range(n, n + L)); n += L
        for j in range(L): edges.append((vs[j], vs[(j + 1) % L]))
        cyc.append((vs[0], vs[p]))
    for i in range(3):
        path(cyc[i][1], cyc[(i + 1) % 3][0], ts[i])
    for a, b in cyc:
        path(0, a, s); path(0, b, s)
    return n, edges
def dgon(n, edges, k, dmax):
    inp = f"{n} {len(edges)} {k} {dmax}\n" + "\n".join(f"{a} {b}" for a, b in edges) + "\n"
    out = subprocess.run(["./dgon"], input=inp, capture_output=True, text=True, timeout=600).stdout
    return int(out.split("dgon=")[1].split()[0]) if "dgon=" in out else None
KS = [int(x) for x in sys.argv[1:]] or [2, 3]
seen = set()
for Ls in itertools.product((2, 3, 4), repeat=3):
    for ps in itertools.product(*[range(1, L // 2 + 1) for L in Ls]):
        for ts in itertools.product((1, 2, 3), repeat=3):
            for s in (1, 2):
                key = (Ls, ps, ts, s)
                n, E = graph(Ls, ps, ts, s)
                g = dgon(n, E, 1, 7)
                res = {k: dgon(n, E, k, g - 1) for k in KS}
                flag = [k for k in KS if res[k] is not None and k % 2 == 1]
                print(key, "dgon", g, {k: (res[k] if res[k] is not None else f">={g}") for k in KS}, "ODD-DROP" if flag else "", flush=True)
