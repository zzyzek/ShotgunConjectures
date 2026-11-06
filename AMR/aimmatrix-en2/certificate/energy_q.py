# max of E(G-e)-E(G) and of E(G)-E(G-e) over all graphs on <= 7 vertices and edges e
import networkx as nx, numpy as np
from networkx.generators.atlas import graph_atlas_g
def E(G): return float(np.abs(np.linalg.eigvalsh(nx.to_numpy_array(G))).sum()) if G.number_of_nodes() else 0.0
best_up=(-9,None); best_dn=(-9,None)
for G in graph_atlas_g():
    if G.number_of_edges()==0: continue
    e0=E(G)
    for e in list(G.edges()):
        H=G.copy(); H.remove_edge(*e); d=E(H)-e0
        if d>best_up[0]: best_up=(d,(G.number_of_nodes(),sorted(G.edges()),e))
        conn=nx.is_connected(G)
        if conn and G.number_of_nodes()>2 and -d>best_dn[0]: best_dn=(-d,(G.number_of_nodes(),sorted(G.edges()),e))
print("max E(G-e)-E(G):",best_up)
print("max E(G)-E(G-e), connected G != K2:",best_dn)
