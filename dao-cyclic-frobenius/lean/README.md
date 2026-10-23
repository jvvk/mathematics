# Lean formalisation: The Frobenius number of Dao's cyclic semigroups

Lean 4 (v4.34.0) with Mathlib. Every theorem below depends only on `propext`, `Classical.choice` and
`Quot.sound`; `LeanProofs/Frobenius292507/Report.lean` prints the axioms of the headline results when it is
compiled, and `CheckClaims.lean` restates them. Nothing is computed about the semigroup itself: the example
follows from the general theorem.

Indexing: Lean counts from `0` and reads `a : ℕ → ℕ` with period `n` (`a (i + n) = a i`), so the paper's
`a_1, …, a_n` are `a 0, …, a (n - 1)`. Membership in the semigroup is `InS n a m`: some coefficients `c i ≥ 0`
with `∑_{i < n} c i * x n a i = m`. The digit bound of the paper's `d_i ≤ a_{i-1} - 1` is `d i < b n a i` with
`b n a i = a (i + n - 1)`.

| Paper | Lean | File |
|---|---|---|
| `x_i`, `P`, `N`, the semigroup `S` | `x`, `P`, `N`, `InS` | `Defs.lean` |
| Carry identity (1) | `carry`, `carry_b` | `Carry.lean` |
| Sum identity (2) | `sum_identity` | `Carry.lean` |
| `N ≥ 1` and `gcd(x_n, N) = 1`, identity (3) | `N_pos`, `coprime_x0_N` | `Carry.lean` |
| Place values, congruence (4) | `pi`, `x_cong` | `Carry.lean` |
| Lemma 1 (mixed radix: bound `P − 1`, attained only by the maximal vector; every `0 ≤ t ≤ N` occurs) | `v_le`, `v_eq_N`, `v_surj` | `Digits.lean` |
| Digit values: residues, `w(d) ≤ nN`, `w(max) = nN` | `w_cong`, `w_le`, `w_max` | `Semigroup.lean` |
| Carrying up: `s + kN ∈ S` | `InS_add_N`, `InS_add_mul_N` | `Semigroup.lean` |
| Carrying down to a digit vector, (5) | `carry_down` | `Semigroup.lean` |
| **Theorem 1**: `(n − 1)N ∉ S` and every larger integer is in `S` | `not_InS`, `InS_of_gt`, `frobenius` | `Main.lean` |
| The first case `(1, 2, 3)`: generators `4, 9, 7`, Frobenius number `10` | `generators123`, `example123` | `Main.lean` |

Route: the formalisation follows the paper step by step. Two differences in form, not substance: positivity
`0 < s` stands for "a nonzero representation" (the two are equivalent), and in the case of a nonzero residue the
bound `w(d) ≤ m` is derived from `w(d) ≤ nN` directly, without first noting that `d` is not the maximal vector.
Remarks 1 and 2 (minimality, pseudo-Frobenius sets) are computations, checked by `../verify/remarks.py`, not here.

## Build

```
lake exe cache get                                  # Mathlib build cache
lake build                                          # compiles every module and prints the axiom audit
lake env lean CheckClaims.lean                      # restates each headline result and its axioms
python3 scripts/mutate.py scripts/mutants.toml      # fourteen mutants, each rejected (rebuilds per mutant)
```
