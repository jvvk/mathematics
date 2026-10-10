# Lean formalisation: the easiest dice to tell apart

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` and `python3 scripts/mutants_equality.py` check that 10 and 9
wrong variants fail.

A die on `k` faces is `Fin k → ℝ`; `Adm r p` says every face is in `[0, r]` and the faces sum to `1`. A sequence
of `n` rolls with die `D j` at roll `j` is `D : Fin n → (Fin k → ℝ) × (Fin k → ℝ)`; `overlap D` is
`∑_w min(P(w), Q(w))`, `g p q u v = ∑ (u pᵢ - v qᵢ)⁺` and `G D u v` is the same over words.

| Paper | Lean (namespace `CappedDice`) |
|---|---|
| Lemma 1, bounds for any set of `a` faces | `excess_le` |
| Lemma 1, the staircase meets them on its first `a` faces | `stair_sum`, `rev_sum`, `pstar_adm`, `qstar_adm`, `stair_excess_ge` |
| Proposition 1 | `dominates` |
| Identity (2), both forms | `G_succ`, `G_succ'` |
| Theorem 1 (dice may change from roll to roll) | `G_le`, `overlap_eq`, `overlap_ge_of_dominant`, `overlap_ge` |
| Corollary 1: the asker's pair has the least overlap | `g_asker`, `asker_adm`, `asker_optimal` |
| Lemma 2 | `head_eq`, `tight_rates`, `tight_rates2` |
| Lemma 3 and the five values `B(a)` | `tight`, `tight4`, `bnd_vals` |
| Theorem 2(b): high, low and middle rates | `face_r0`, `face_0r`, `mid_card`, `P_balanced`, `rate_gap`, `pin_odd`, `pin_even`, `equality_ge3` |
| Relabellings reach the bound, every `n` | `relabel_attains` |
| Theorem 2(a) | `overlap_one`, `equality_one` |
| Theorem 2, the `n = 2` family | `family_adm`, `family_g`, `family_G`, `equality_two_family` |

## What is not formalised

The closed form of Corollary 1 (the asker's evaluation of their pair) is checked by `verify/check.py` for
`n ≤ 6` in exact arithmetic. Whether the `n = 2` family is the whole answer for `n = 2` is not claimed.
