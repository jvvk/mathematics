import SymmetricRatio.Convex
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# MO 467261: `Ψ_{i,n}` is strictly increasing on `(1, ∞)`

`H N ℓ t x = ∑_{k ≤ ℓ} C(N+ℓ, ℓ-k) · multichoose(t, k) · (x-1)^k`, which is
`h_ℓ(1^{[n-t]}, x^{[t]})` with `n = N + 1` (bridge to `MvPolynomial.hsymm` in `Bridge.lean`).
Key identity: `(x-1) ∂ₓ H_{ℓ+1} = (ℓ+1) H_{ℓ+1} - (N+ℓ+1) H_ℓ`, so
`(x-1) ∂ₓ log Ψ = (N+ℓ+1) · (second difference of H_ℓ/H_{ℓ+1} at i) > 0`.
-/

open Polynomial Finset

namespace Haddou

/-- `H_t` as a polynomial in `x`. -/
noncomputable def HP (N ℓ t : ℕ) : ℝ[X] :=
  ∑ k ∈ range (ℓ + 1), C (((N + ℓ).choose (ℓ - k) : ℝ) * (t.multichoose k : ℝ)) * (X - C 1) ^ k

/-- `H_t(x) = h_ℓ(1^{[n-t]}, x^{[t]})` in its `(x-1)`-expanded form. -/
noncomputable def H (N ℓ t : ℕ) (x : ℝ) : ℝ := (HP N ℓ t).eval x

lemma b_eval_nat (k t : ℕ) : (b k).eval (t : ℝ) = (t.multichoose k : ℝ) := by
  unfold b
  rw [eval_mul, eval_C, ascPochhammer_nat_eq_natCast_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose', ← Nat.multichoose_eq]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma H_eq_P (N ℓ t : ℕ) (x : ℝ) : H N ℓ t x = (P N (x - 1) ℓ).eval (t : ℝ) := by
  simp only [H, HP, P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, b_eval_nat]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [a, show k ≤ ℓ from Nat.lt_succ_iff.1 (mem_range.1 hk), ite_true]
  ring

lemma H_pos (N ℓ t : ℕ) {x : ℝ} (hx : 1 ≤ x) : 0 < H N ℓ t x := by
  rw [H_eq_P]; exact P_eval_pos N (by linarith) ℓ (Nat.cast_nonneg t)

/-- Coefficientwise `(x-1)`-derivative identity. -/
lemma HP_deriv (N ℓ t : ℕ) :
    (X - C 1) * derivative (HP N (ℓ + 1) t) =
      C ((ℓ : ℝ) + 1) * HP N (ℓ + 1) t - C ((N : ℝ) + ℓ + 1) * HP N ℓ t := by
  simp only [HP, derivative_sum, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_X_sub_C_pow, Finset.mul_sum]
  rw [Finset.sum_range_succ _ (ℓ + 1), Finset.sum_range_succ (fun k => C ((ℓ:ℝ) + 1) * _) (ℓ + 1),
    add_sub_right_comm, ← Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ ℓ := Nat.lt_succ_iff.1 (mem_range.1 hk)
    have hc : (((N + ℓ + 1 : ℕ)) : ℝ) * ((N + ℓ).choose (ℓ - k) : ℝ) =
        ((N + (ℓ + 1)).choose (ℓ + 1 - k) : ℝ) * (((ℓ - k + 1 : ℕ)) : ℝ) := by
      have := Nat.add_one_mul_choose_eq (N + ℓ) (ℓ - k)
      rw [show ℓ + 1 - k = ℓ - k + 1 by omega, show N + (ℓ + 1) = N + ℓ + 1 by ring]
      exact_mod_cast this
    have hc' : ((N : ℝ) + ℓ + 1) * ((N + ℓ).choose (ℓ - k) : ℝ) =
        ((N + (ℓ + 1)).choose (ℓ + 1 - k) : ℝ) * ((ℓ : ℝ) + 1 - k) := by
      rw [show ((N : ℝ) + ℓ + 1) = (((N + ℓ + 1 : ℕ)) : ℝ) by push_cast; ring, hc,
        show (((ℓ - k + 1 : ℕ)) : ℝ) = (ℓ : ℝ) + 1 - k by
          rw [Nat.cast_add, Nat.cast_sub hk']; push_cast; ring]
    set c1 : ℝ := ((N + (ℓ + 1)).choose (ℓ + 1 - k) : ℝ)
    set c0 : ℝ := ((N + ℓ).choose (ℓ - k) : ℝ)
    set m : ℝ := (t.multichoose k : ℝ)
    have hR : C ((ℓ : ℝ) + 1) * (C (c1 * m) * (X - C 1) ^ k) -
        C ((N : ℝ) + ℓ + 1) * (C (c0 * m) * (X - C 1) ^ k) = C ((k : ℝ) * c1 * m) * (X - C 1) ^ k := by
      rw [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, ← sub_mul, ← C_sub]
      congr 2
      linear_combination (-m) * hc'
    rw [hR]
    rcases k with _ | k
    · simp
    · rw [show k + 1 - 1 = k by omega, pow_succ]; push_cast
      simp only [C_mul, C_add, C_1, map_natCast]; ring
  · rw [show ℓ + 1 - 1 = ℓ by omega, pow_succ]; push_cast; ring

lemma H_deriv_id (N ℓ t : ℕ) (x : ℝ) :
    (x - 1) * (derivative (HP N (ℓ + 1) t)).eval x =
      ((ℓ : ℝ) + 1) * H N (ℓ + 1) t x - ((N : ℝ) + ℓ + 1) * H N ℓ t x := by
  have := congrArg (eval x) (HP_deriv N ℓ t)
  simpa [H, eval_mul, eval_sub, eval_C, eval_X] using this

/-- **Main theorem (MO 467261).** For `n = N + 1`, `ℓ = m + 1 ≥ 1` and `1 ≤ i`,
`Ψ(x) = H_i(x)^2 / (H_{i+1}(x) H_{i-1}(x))` is strictly increasing on `(1, ∞)`. -/
theorem psi_strictMonoOn (N m i : ℕ) (hi : 1 ≤ i) :
    StrictMonoOn (fun x => H N (m + 1) i x ^ 2 / (H N (m + 1) (i + 1) x * H N (m + 1) (i - 1) x))
      (Set.Ioi 1) := by
  have hpos : ∀ t, ∀ x ∈ Set.Ioi (1 : ℝ), 0 < H N (m + 1) t x :=
    fun t x hx => H_pos N (m + 1) t (le_of_lt hx)
  apply strictMonoOn_of_deriv_pos (convex_Ioi 1)
  · refine ContinuousOn.div ((HP N (m + 1) i).continuous.pow 2).continuousOn
      ((HP N (m + 1) (i + 1)).continuous.mul (HP N (m + 1) (i - 1)).continuous).continuousOn
      fun x hx => (mul_pos (hpos _ x hx) (hpos _ x hx)).ne'
  intro x hx
  rw [interior_Ioi] at hx
  have hx1 : 0 < x - 1 := sub_pos.2 hx
  set A := HP N (m + 1) i
  set B := HP N (m + 1) (i + 1)
  set Cc := HP N (m + 1) (i - 1)
  have ha : 0 < A.eval x := hpos i x hx
  have hb : 0 < B.eval x := hpos (i + 1) x hx
  have hc : 0 < Cc.eval x := hpos (i - 1) x hx
  have hd := HasDerivAt.div ((A.hasDerivAt x).mul (A.hasDerivAt x))
    ((B.hasDerivAt x).mul (Cc.hasDerivAt x)) (mul_pos hb hc).ne'
  have hfun : (fun x => H N (m + 1) i x ^ 2 / (H N (m + 1) (i + 1) x * H N (m + 1) (i - 1) x)) =
      (fun x => A.eval x * A.eval x / (B.eval x * Cc.eval x)) := by
    funext z; simp only [H, A, B, Cc, sq]
  have hd' : HasDerivAt (fun x => A.eval x * A.eval x / (B.eval x * Cc.eval x))
      ((((derivative A).eval x * A.eval x + A.eval x * (derivative A).eval x) * (B.eval x * Cc.eval x)
        - A.eval x * A.eval x * ((derivative B).eval x * Cc.eval x + B.eval x * (derivative Cc).eval x))
        / (B.eval x * Cc.eval x) ^ 2) x := hd
  rw [hfun, hd'.deriv]
  refine div_pos ?_ (by positivity)
  -- derivative identities
  have ea := H_deriv_id N m i x
  have eb := H_deriv_id N m (i + 1) x
  have ec := H_deriv_id N m (i - 1) x
  simp only [H] at ea eb ec
  -- second difference
  have hsd := second_difference_pos N hx1 m (t := (i : ℝ)) (by exact_mod_cast hi)
  simp only at hsd
  have ci1 : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by rw [Nat.cast_sub hi]; simp
  have ci2 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  rw [← ci1, ← ci2, ← H_eq_P, ← H_eq_P, ← H_eq_P, ← H_eq_P, ← H_eq_P, ← H_eq_P] at hsd
  simp only [H] at hsd
  set a := A.eval x; set b := B.eval x; set c := Cc.eval x
  set am := (HP N m i).eval x; set bm := (HP N m (i + 1)).eval x; set cm := (HP N m (i - 1)).eval x
  have hsdN : 0 < cm * a * b + bm * a * c - 2 * am * b * c := by
    have : cm * a * b + bm * a * c - 2 * am * b * c = (a * b * c) * (cm / c + bm / b - 2 * (am / a)) := by
      field_simp
    rw [this]; positivity
  have hK : 0 < (N : ℝ) + m + 1 := by positivity
  set a' := (derivative A).eval x; set b' := (derivative B).eval x; set c' := (derivative Cc).eval x
  have key : (x - 1) * ((a' * a + a * a') * (b * c) - a * a * (b' * c + b * c')) =
      ((N : ℝ) + m + 1) * a * (cm * a * b + bm * a * c - 2 * am * b * c) := by
    linear_combination (2 * a * b * c) * ea - (a ^ 2 * c) * eb - (a ^ 2 * b) * ec
  have : 0 < (x - 1) * ((a' * a + a * a') * (b * c) - a * a * (b' * c + b * c')) := by
    rw [key]; positivity
  exact pos_of_mul_pos_right this hx1.le

end Haddou
