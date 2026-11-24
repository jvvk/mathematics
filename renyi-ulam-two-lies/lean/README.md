# Lean formalisation: what is and is not proved

Lean 4 + Mathlib, namespace `UlamHalving` (two lies) and `UlamHalving.Three` (three lies, file `Three.lean`), files in `LeanProofs/UlamHalving/`. Build: `lake exe cache get && lake build`;
`lake env lean CheckClaims.lean` prints the axioms of every result below (recorded in `axiom-validation.txt`). Axioms:
propext, Classical.choice, Quot.sound for every result, except `V_conserve` and `Three.V_conserve` (propext only),
`Solv.mono` (propext, Quot.sound) and `Three.h_eq_halving` (none). No sorry, no native_decide, no brute-force decide.

The game is modelled directly: a position `St` is a triple `(a, b, c)`, `yes` and `no` give the children of a question
`(u, v, w)`, and `Solv n x` (inductive: a position with at most one candidate is won; otherwise some legal question has
both children in `Solv (n - 1)`) says that `x` can be won in `n` questions.

## Proved
| Paper | Lean | Scope |
|---|---|---|
| Section 2, conservation of volume | `V_conserve` | `V (n+1) x = V n (yes x u v w) + V n (no x u v w)` for every legal question |
| Section 2, Berlekamp's bound | `V_le` | `Solv n x → V n x ≤ 2^n` |
| Section 2, deleting candidates never hurts | `Solv.mono` | componentwise smaller positions stay winnable |
| Lemma 2.1 (direction used) | `padding`, `padding'`, `pad`, `small` | adding last-class candidates keeps a winnable position winnable while the volume bound holds |
| Lemma 3.1 | `lemma2` | every `n ≥ 12`, given the depth-12 hypothesis `base12` below |
| Lemma 4.1, sufficiency | `lemma3`, `choose_u` | depth `n + 1 ≥ 15`, given `base12` |
| Section 5, key step | `key` | a winnable even parent `(2a, 2b, 0)` at depth `n + 2` forces the criterion of Lemma 4.1 for every `g` dividing `n` and `C(n, 2)` |
| Theorem 1.2 | `halving_child` | parent depth `n + 2 ≥ 16`: `Solv (n+2) (2a, 2b, 2c) → Solv (n+1) (a, a+b, b+c)`, given `base12` |
| Theorem 1.2, optimality | `halving_optimal` | the parent is winnable iff both children of the even-splitting question are |
| growth inequalities | `growth9`, `growth_cube`, `growth13` | the numerical estimates used in Lemmas 3.1 and 4.1 |

### Three lies (`UlamHalving.Three`)
A position is `(a, b, c, d)`; `yes`, `no` and `Solv` are defined as for two lies, with one more class.

| Paper | Lean | Scope |
|---|---|---|
| Section 7, conservation of volume | `Three.V_conserve` | for every legal question |
| Section 7, Berlekamp's bound | `Three.V_le` | `Solv n x → V n x ≤ 2^n` |
| Theorem 1.3, the halving child | `Three.h_eq_halving` | both children of the even-splitting question from `(2A, 52, 120, 0)` equal `h = (A, A+26, 86, 60)` |
| Section 7, slack | `Three.V_h` | `V 105 h = 2^105 - 28` |
| Theorem 1.3, losing half | `Three.not_solv_105` | `¬ Solv 105 h`, by the two-level argument: `first_level` (mod 5356, a case split over the 87 values of `w`, as in the paper's "only possibilities"), `second_level` (Lemma 7.1 with `g = 103`), `yes_fails`, `no_fails` |

## Not formalised
- `base12`: every position `(a, b, c)` with `a ≤ b`, `c ≥ 66` and `V 12 (a, b, c) ≤ 2^12` can be won in 12 questions. It is
  an explicit hypothesis of `lemma2`, `lemma3`, `halving_child` and `halving_optimal`, and is checked by the certificate
  (the 44 boundary cases at depth 12) in `../verify/`.
- Theorem 1.2 for parent depth at most 15: the certificate of Section 6, checked by `../verify/verify_proof.py` and
  independently by `../verify/recheck_frontiers.py`.
- The necessity halves of Lemma 2.1 and Lemma 4.1, which the proof of Theorem 1.2 does not use.
- Theorem 1.3, winning half (`(2A, 52, 120, 0)` is winnable in 106 questions): the certificate of 2,126 questions in
  `../verify/three-lies/`, checked by two independent programs. Replaying it in Lean would be a computation, not a proof.

## Mutation tests
`scripts/mutants.toml`, run with `cd scripts && python3 mutate.py mutants.toml` (runner included): 20 mutants (19 false statements and one
hypothesis-dependence check), all rejected, all controls pass (`mutation-validation.log`). Thirteen are false strengthenings of a stated result: the
volume bound made strict, `Solv.mono` without its last-class restriction, `small`, `padding` and `lemma2` with volume
bound `2^n + 1`, `pad` without its volume hypothesis, the three growth inequalities one step earlier, `choose_u` with
`u = ⌊a/2⌋` only, `lemma3` with the criterion modulus 1 (false at the exceptional child `(15141, 15151, 10)`, depth 22),
`halving_child` one question faster, and `halving_optimal` with a question that ignores the last class. The fourteenth raises the
threshold of `base12` from 66 to 67, a stronger statement not known to be false; its rejection shows only that the
hypothesis is used at exactly 66. Six more target the three-lie file: `not_solv_105` with 106 questions (false: `h`
is 106-winnable), the volume bound strict, the slack 27 instead of 28, `first_level` without its `w = 17` case, and
`yes_fails` and `no_fails` with allowance 69 instead of 35.

Pinned versions: `lean-toolchain` and `lake-manifest.json`.
