# All connected simple graphs on <= 7 vertices (networkx atlas): compare
# dgon(G) with dgon(sigma_3 G) (search only below dgon(G)); graphs with
# dgon(G) <= DMAX only.  Usage: python3 atlas.py DMAX
import sys, subprocess, networkx as nx
DMAX = int(sys.argv[1])
def dgon(n, E, k, dmax):
    inp = f"{n} {len(E)} {k} {dmax}\n" + "\n".join(f"{a} {b}" for a, b in E) + "\n"
    out = subprocess.run(["./dgon"], input=inp, capture_output=True, text=True, timeout=600).stdout
    return int(out.split("dgon=")[1].split()[0]) if "dgon=" in out else None
tot = drops = skipped = 0
for G in nx.graph_atlas_g()[1:]:
    if not nx.is_connected(G) or G.number_of_nodes() < 2: continue
    E = list(G.edges()); n = G.number_of_nodes()
    g = dgon(n, E, 1, DMAX)
    if g is None: skipped += 1; continue
    tot += 1
    if g >= 2:
        for k in (3,):
            r = dgon(n, E, k, g - 1)
            if r is not None:
                drops += 1; print("DROP k", k, "n", n, E, g, r, flush=True)
print("tested", tot, "odd drops", drops, "skipped (dgon >", DMAX, ")", skipped)
