import LeanProofs.Frobenius292507.Defs
import LeanProofs.Frobenius292507.Carry
import LeanProofs.Frobenius292507.Digits
import LeanProofs.Frobenius292507.Semigroup
import LeanProofs.Frobenius292507.Main
import LeanProofs.Frobenius292507.Report

/-!
# The Frobenius number of Dao's cyclic semigroups (MO 292507)

For `n ≥ 2`, positive `a₀, …, aₙ₋₁` (indices mod `n`), `P = a₀⋯aₙ₋₁`, `N = P - 1` and
`xᵢ = 1 + aᵢ + aᵢaᵢ₊₁ + ⋯ + aᵢ⋯aᵢ₊ₙ₋₂`: if `gcd (x₀, …, xₙ₋₁) = 1` then `(n - 1) N ∉ ⟨x₀, …, xₙ₋₁⟩`
and every `m > (n - 1) N` lies in it. Proved along the answer's route.

* `Frobenius292507.Defs`: the statement's definitions `x`, `P`, `N`, `InS`.
* `Frobenius292507.Carry`: steps 1 to 5 (carry identity `carry`, sum identity `sum_identity`,
  `N_pos`, `coprime_x0_N`, the congruence `x_cong`).
* `Frobenius292507.Digits`: step 6, digit vectors and the mixed radix (`v_le`, `v_eq_N`, `v_surj`).
* `Frobenius292507.Semigroup`: steps 7 to 9 (`w_cong`, `w_le`, `w_max`, the upward step
  `InS_add_mul_N`, carrying down `carry_down`).
* `Frobenius292507.Main`: steps 10 and 11, the headline `frobenius`, and `example123`
  (`a = (1, 2, 3)`: generators `4, 9, 7`, Frobenius number `10`).
-/
