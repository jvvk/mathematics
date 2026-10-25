# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 scripts/mutants.py

The first command fetches the pinned Mathlib cache, the second compiles the proofs, the third prints the
statements and axioms of the headline results, and the last runs the mutation tests: each plants one wrong
definition, statement or constant and checks that the file no longer compiles.

**Scope.** The paper's main theorem is conditional and rests on the `p`-adic Frobenius structures of
Beukers and Vlasenko, which Mathlib does not have; Theorem 5.2, the change-of-lift lemma, the compactness
criterion and Hypothesis F are not formalised. Lean checks the elementary algebra the argument uses. The
symbolic identities (the symmetric square and the hypergeometric pullback) and all numerical evidence are
checked in exact arithmetic by `verify/run_all.py`.

| Paper | Lean (namespace `StrangeOperator`, file `Basic.lean`) |
|---|---|
| Proposition 2.1: the recurrence of `L` gives that of `P = I ⋆ L` for `binom(2n, n) u_n` | `hadamard_rec` |
| Proposition 5.5: `c_p = (2/p) 2^((p-1)/2) ≡ 1 (mod p)` and `c_p⁴ = 4^(p-1)` | `cp_mod`, `cp_fourth` |
| Lemma 5.3, equation (4): `w_d(pk) = c_p^(dk) w_d(k)` | `w_mul` |
| Propositions 6.2, 6.4: `p ∣ binom(2p - 2, p - 1)`, the vanishing Hasse-Witt entry | `choose_vanish` |
| Proposition 5.6: the reductions modulo 9 and the contradiction at `p = 3` | `prime3_reductions`, `prime3_contradiction` |

`cp p` uses Mathlib's Jacobi symbol; for an odd prime it is the Legendre symbol, and `cp_mod` is Euler's
criterion. `w d k` is the weight of Section 4 with the Jacobi symbol `(2/k)`.

Every result uses at most propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log). `scripts/mutants.py` plants nine wrong
variants (recurrence coefficients, the sign of `c_p`, the weights, the prime-3 arithmetic); a variant counts as
rejected only for a proof error located in the mutated file, and a timeout, crash, resource limit or import failure
fails the run. All nine were rejected (mutants.log).
