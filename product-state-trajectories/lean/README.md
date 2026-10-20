# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 scripts/mutants.py

The first command fetches the pinned Mathlib cache, the second compiles the proofs, the third prints the
statements and axioms of the results below, and the last runs the 26 mutation tests: each weakens one
hypothesis, strengthens one conclusion or changes one constant, and checks that the module no longer compiles.

| Paper | Lean (namespace `ProductTrajectory`) |
|---|---|
| Lemma 5 (frequencies in a lattice) | `Characters.lean`: `exists_lattice` |
| Lemma 6 (Dedekind: distinct characters are independent; an exponential sum vanishing for all `t` has zero polynomial) | `Characters.lean`: `chi_injective`, `eq_zero_of_eval_zt` |
| Lemma 7 (a matrix over a GCD domain with vanishing 2×2 minors is a column times a row) | `RankOne.lean`: `exists_vecMulVec_of_minors` |
| Lemma 8 (factors of a weighted-homogeneous polynomial are weighted-homogeneous) | `Graded.lean`: `isWeightedHomogeneous_of_mul` |
| Proposition 9 (orthogonality from the grading) | `Core.lean`: `orthogonal_of_homogeneous` |
| Theorem 4 (rank-one exponential sums factor with orthogonal components) | `Main.lean`: `main` |
| Section 6, single-frequency lemma for constant-modulus sums | `ExpSums.lean`: `const_modulus_single` |
| Section 6, the involution `τ` and the splitting of so(4) | `SO4.lean`: `SO4.tau_fixed`, `SO4.split_basis` |
| Section 6, evolution of eigenvectors of `X ↦ AX + XC`; the generator | `MaxEnt.lean`: `MaxEnt.evolve_eigen`, `MaxEnt.generator` |
| Theorem 10 (two qubits staying maximally entangled), exponential-sum form | `MaxEnt.lean`: `MaxEnt.maxent` |
| The Example: eigen-equations of `H`, the expansion of `M(t)`, orthogonality, `det M(t) = 1`, `‖M(t)‖² = 6` | `Heisenberg.lean`: `Heisenberg.H_mulVec`, `M_eq_sum`, `V_orth`, `det_M`, `normSq_M` |
| The Example: no Hermitian `A`, `C` with `M(t) = e^{-itA} M(0) e^{-itC}` (Mathlib's matrix exponential) | `Heisenberg.lean`: `Heisenberg.not_local` |

Theorem 4 is stated from the hypotheses of equation (1): an arbitrary finite family of reals `λ_j` (repeats
allowed), pairwise orthogonal matrices `V_j`, and `M(t)` a column times a row for every real `t`. Dedekind's
lemma, unique factorisation of polynomial rings and bases of finitely generated free abelian groups come from
Mathlib.

Not formalised: the spectral decomposition at the start of Section 2, the construction of `h_A`, `h_B` from
orthogonal vectors in the proof of Theorem 1, the induction of Corollary 2 and Corollary 3 (standard linear
algebra, in the paper). Every result above uses only propext, Classical.choice and Quot.sound
(axiom-validation.txt). The folder was compiled in an isolated build without the development cache
(build-validation.log).
