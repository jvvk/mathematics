# Lean formalisation: prime squares and half-turns

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that 9 wrong variants fail.

The orientation argument is proved once, for any unique factorisation domain `A` with an involutive ring
automorphism `σ` fixing `R = q₁ q₂` (`q₁, q₂` prime) and a ring map `ε : A → ℤ` with `ε ∘ σ = ε`. With `σ` the
half-turn or one reflection and `ε` evaluation at `(1,1)` it covers Theorems 1 and 2 of the note.

| Paper | Lean (namespace `PrimeSquares`) |
|---|---|
| A nonunit factor of `R = Q_p(x) Q_p(y)` is divisible by one of the two primes | `prime_dvd_of_dvd_mul` |
| Proof of Theorems 1 and 2 (odd `p`): from identity (1), `Q_p(x) ∣ F` or `Q_p(y) ∣ F` | `orientation_dichotomy` |
| `Q_p` is irreducible over `ℤ` and `Q_p(1) = p` | `cyclotomic_prime_irreducible`, `cyclotomic_prime_eval_one` |
| Lemma 1, one row: a `0/1` polynomial of degree `< p` divisible by `Q_p` is `0` or `Q_p` | `row_eq` |
| Lemma 1: a `p`-cell tile in `ℤ[x][y]` with `Q_p(x) ∣ F` is `Q_p(x) y^j`, a bar | `bar_of_dvd` |

## What is not formalised

- That the Laurent ring `ℤ[x^±1, y^±1]` is a unique factorisation domain in which `Q_p(x)` and `Q_p(y)` are
  prime (a localisation of `ℤ[x, y]`; Eisenstein at `p`), and the step in Lemma 1 from divisibility in the
  Laurent ring to divisibility in `ℤ[x, y]`. Both are quoted in the note.
- The encoding of a tiling as identity (1), which the Python programs in `verify/` audit.
- The case `p = 2`, which the note handles in two lines.
