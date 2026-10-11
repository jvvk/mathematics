# Lean formalisation: every number except three is a best-pair path count

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that 10 wrong variants fail.

A simple path is a list of distinct vertices, consecutive ones adjacent (`IsPathL`); `paths` is the finite set
of them between two vertices and `N` its size in `G_a` (`gadj`: base graph on `Fin h` plus `a` new vertices
joined to `x` and `y`). `IsMax h E x y a k` says the largest count over pairs `u ≠ v` is exactly `k`; `IsSimple`
says the adjacency is symmetric and loopless.

| Paper | Lean (namespace `MaxPaths`) |
|---|---|
| The path generator lists every simple path exactly once (used to evaluate counts) | `mem_ext`, `nodup_ext`, `mem_paths`, `countFast_eq` |
| Paths transfer along adjacency-preserving injections | `card_pullback` |
| Lemma 1, core: a path has at most one interior new vertex | `interior`, `at_most_one` |
| Splitting the paths by the new vertex they use | `card_decomp` |
| Lemma 1: `N_a(u,v) = N_b(s,t) + (a − b)·T(s,t)`, and `N_{b+1} = N_b + T` | `affine`, `N_succ` |
| From the finite check of every line to a bound for every `a ≥ 1` | `okAt`, `okAt_spec`, `line_le`, `bound` |
| A best pair on each line | `witness0`, `witness1` |
| Table 1: `f(G_a) = 2a, 6a + 1, 6a + 9, 6a + 11` | `fam2`, `fam61`, `fam69`, `fam611` |
| `f(K_2) = 1`, `f(K_4) = 5`, `f(W_4) = 9`, the 11-graph | `K2_max`, `K4_max`, `W4_max`, `G11_max` |
| Theorem 1 | `every_k` |

## What is not formalised

Proposition 1 (no graph has `f(G) = 3`), proved by hand in the note from the block decomposition and a theta
subgraph.
