"""MO q/263706. Replace every vertex of a cubic skeleton K by a copy of K_{2,3} (= K_{3,3} minus a vertex):
the three degree-2 vertices p1,p2,p3 take the three skeleton edges. Check: cubic, Hamiltonian, non-bipartite,
and no cycle of length n-1 (i.e. G - v non-Hamiltonian for every v), by exhaustive search."""
import sys
import networkx as nx

def inflate(K: nx.Graph) -> nx.Graph:
    G = nx.Graph(); port = {}
    for v in K:
        P = [(v, "p", i) for i in range(3)]; Q = [(v, "q", j) for j in range(2)]
        G.add_edges_from((p, q) for p in P for q in Q)
        for i, u in enumerate(sorted(K[v])): port[(v, u)] = P[i]
    for u, v in K.edges(): G.add_edge(port[(u, v)], port[(v, u)])
    return nx.convert_node_labels_to_integers(G)

def ham_cycle(G: nx.Graph, nodes) -> bool:
    """Exhaustive DFS for a Hamiltonian cycle on the induced subgraph `nodes`."""
    nodes = set(nodes); N = len(nodes); s = min(nodes)
    adj = {v: [w for w in G[v] if w in nodes] for v in nodes}
    path, seen = [s], {s}
    def dfs(v):
        if len(path) == N: return s in adj[v]
        for w in adj[v]:
            if w not in seen:
                seen.add(w); path.append(w)
                if dfs(w): return True
                seen.discard(w); path.pop()
        return False
    return dfs(s)

def report(name: str, G: nx.Graph) -> None:
    n = G.number_of_nodes()
    assert all(d == 3 for _, d in G.degree())
    ham = ham_cycle(G, G.nodes)
    n1 = [v for v in G if ham_cycle(G, set(G) - {v})]
    print(f"{name}: n={n} cubic, connected={nx.is_connected(G)}, bipartite={nx.is_bipartite(G)}, "
          f"hamiltonian={ham}, vertices v with G-v hamiltonian (i.e. (n-1)-cycles): {len(n1)}")

if __name__ == "__main__":
    # controls: the cube (bipartite, no (n-1)-cycle) and K4, Petersen-free prism (has (n-1)-cycles)
    report("control cube Q3", nx.hypercube_graph(3))
    report("control prism K3xK2", nx.circular_ladder_graph(3))
    report("K4 inflated", inflate(nx.complete_graph(4)))
    report("prism inflated", inflate(nx.circular_ladder_graph(3)))
