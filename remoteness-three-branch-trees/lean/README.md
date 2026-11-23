# Lean formalisation: what is and is not proved

Lean 4 + Mathlib, namespace `Remoteness`, files in `LeanProofs/Remoteness/`. Build: `lake exe cache get && lake build`;
`lake env lean CheckClaims.lean` prints the axioms of every result below (recorded in `axiom-validation.txt`). Axioms of every result
below: propext, Classical.choice, Quot.sound. No sorry, no native_decide.

## Proved
| Note | Lean | Scope |
|---|---|---|
| Lemma 3.2 (R(D) = 3892) | `obstruction`, `attained` | every multiset splitting of D' |
| Lemma 3.1 arithmetic | `leafValues`, `T_beats_brooms` | arithmetic of the leaf values |
| Lemma 4.3 | `Family.three_branch_loses`, `Family.X_add_Z` | all L >= p >= h >= 1, a, c >= 2, b >= 1; inequality between the leaf-value formulas |
| Lemma 4.2 | `Prune.prune` | any finite acyclic graph with no degree-2 vertex (the tree with segments contracted to edges) in which at most two edges have length other than h and some edge of length h has no end of degree 1 |
| Lemmas 2.1, 2.2 for caterpillars | `two_trans_leaf`, `trans_spine_le`, `trans_armL_le`, `trans_armR_le` | spine-with-arms trees, on Mathlib's graph distance (`Cat.dist_eq`) |
| Theorem 1.2, comparison part | `headline` | T has maximum transmission 5962; every starlike or two-hub caterpillar with segments D has a vertex with transmission >= 5971 |
| Branch vertices | `T_branch`, `Starlike.branch`, `TwoHub.branch` | T has exactly 3; the two compared classes have exactly 1 and 2 |

## Not formalised
- Segment decomposition of an arbitrary `SimpleGraph` tree, i.e. that every tree with segment sequence D and one or
  two branch vertices is a `Starlike` / `TwoHub` caterpillar. Allie et al. define these classes by their number of
  branch vertices; the equivalence with these models is an elementary structural fact, not formalised here.
- Lemma 4.1 (starring), cited from Allie et al., Lemma 4.1; hence the graph-level assembly of Theorem 1.3.
- Proposition 3.3, rows h = 3 (lower bound), 4 and 5: an enumeration of 42 skeletons x 110,880 assignments,
  checked by two independent programs in `../verify/`.
- The scaling step of Theorem 1.2 (multiply all lengths by s).

## Mutation tests
`scripts/mutants.toml`, run with `cd scripts && python3 mutate.py mutants.toml` (runner included): 10 mutants, all rejected, all controls
pass (`mutation-validation.log`, one diagnostic per mutant). Eight are false strengthenings of a stated result (a bound,
a branch-vertex set, a degree formula, a hypothesis such as h >= 1). Two are perturbations: "D' with a seventh unit
segment" changes the data, and "Lemma 4.2 allowing degree-2 vertices" replaces the hypothesis degree != 2 by
degree != 4, which gives a false statement (two adjacent degree-2 vertices joined by an h-edge, each joined by a
long edge to a degree-3 vertex carrying two pendant edges).

Pinned versions: `lean-toolchain` (Lean v4.34.0) and `lake-manifest.json` (Mathlib 5ed29652).
