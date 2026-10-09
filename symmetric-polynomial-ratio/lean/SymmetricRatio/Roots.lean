import SymmetricRatio.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# MO 467261: real-rootedness of `P_ℓ` by interlacing

`P_ℓ` has `ℓ` distinct real roots, all negative. Induction on `ℓ`: at the roots
`r_0 < ⋯ < r_{ℓ-1}` of `P_ℓ`, the Wronskian `W_ℓ > 0` forces `P_{ℓ+1}(r_j)` to have sign
`(-1)^{ℓ-j}`; together with a far-left point and `P_{ℓ+1}(0) > 0` this gives `ℓ+1`
sign changes, hence `ℓ+1` roots by the intermediate value theorem.
-/

open Polynomial Finset

namespace Haddou

/-- Roots in consecutive sign-change intervals. -/
lemma roots_between (f : ℝ → ℝ) (hf : Continuous f) (q : ℕ → ℝ) (m : ℕ)
    (hq : ∀ i < m, q i < q (i + 1)) (hs : ∀ i < m, f (q i) * f (q (i + 1)) < 0) :
    ∃ s : ℕ → ℝ, ∀ i < m, q i < s i ∧ s i < q (i + 1) ∧ f (s i) = 0 := by
  have key : ∀ i < m, ∃ x, q i < x ∧ x < q (i + 1) ∧ f x = 0 := by
    intro i hi
    have hc : ContinuousOn f (Set.Icc (q i) (q (i + 1))) := hf.continuousOn
    rcases lt_or_gt_of_ne (show f (q i) ≠ 0 by
        intro h; have := hs i hi; rw [h, zero_mul] at this; exact lt_irrefl 0 this) with h0 | h0
    · have h1 : 0 < f (q (i + 1)) := by
        by_contra h; have h := not_lt.mp h; nlinarith [hs i hi]
      obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (hq i hi).le hc ⟨h0, h1⟩
      exact ⟨x, hx.1, hx.2, hfx⟩
    · have h1 : f (q (i + 1)) < 0 := by
        by_contra h; have h := not_lt.mp h; nlinarith [hs i hi]
      obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' (hq i hi).le hc ⟨h1, h0⟩
      exact ⟨x, hx.1, hx.2, hfx⟩
  choose! s hs using key
  exact ⟨s, hs⟩

lemma mono_of_succ (q : ℕ → ℝ) (m : ℕ) (hq : ∀ i < m, q i < q (i + 1)) :
    ∀ i j, i ≤ j → j ≤ m → q i ≤ q j := by
  intro i j hij hjm
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hq j (by omega)).le

/-- A polynomial of positive degree with positive leading coefficient has, far to the left,
the sign `(-1)^deg`. -/
lemma exists_far_left (p : ℝ[X]) (hd : 0 < p.natDegree) (hlc : 0 < p.leadingCoeff) (A : ℝ) :
    ∃ M < A, 0 < (-1) ^ p.natDegree * p.eval M := by
  set d := p.natDegree
  set q : ℝ[X] := C ((-1) ^ d) * p.comp (-X)
  have hnegX : (-X : ℝ[X]).natDegree = 1 := by rw [natDegree_neg, natDegree_X]
  have hcomp_deg : (p.comp (-X)).natDegree = d := by rw [natDegree_comp, hnegX, mul_one]
  have hcomp_lc : (p.comp (-X)).leadingCoeff = p.leadingCoeff * (-1) ^ d := by
    rw [leadingCoeff_comp (by rw [hnegX]; norm_num), leadingCoeff_neg, leadingCoeff_X]
  have hu : ((-1 : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hq_deg : 0 < q.degree := by
    rw [degree_C_mul hu, degree_eq_natDegree, hcomp_deg]
    · exact_mod_cast hd
    · intro h; rw [h, natDegree_zero] at hcomp_deg; omega
  have hq_lc : 0 ≤ q.leadingCoeff := by
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.2 hu), hcomp_lc, mul_comm, mul_assoc,
      ← mul_pow, show ((-1 : ℝ) * -1) = 1 by norm_num, one_pow, mul_one]
    exact hlc.le
  have ht := (Polynomial.tendsto_atTop_of_leadingCoeff_nonneg q hq_deg hq_lc).eventually
    (Filter.eventually_gt_atTop 0)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 ht
  refine ⟨-(max T (|A| + 1)), ?_, ?_⟩
  · have := le_max_right T (|A| + 1); have := neg_abs_le A; linarith
  · have := hT (max T (|A| + 1)) (le_max_left _ _)
    simpa [q, eval_comp] using this

/-- Sign of `∏_{i ≠ j} (r_j - r_i)` for increasing nodes: `(-1)^{ℓ-1-j}`. -/
lemma sign_prod_erase (r : ℕ → ℝ) : ∀ ℓ, (∀ i k, i < k → k < ℓ → r i < r k) → ∀ j < ℓ,
    0 < (-1) ^ (ℓ - 1 - j) * ∏ i ∈ (range ℓ).erase j, (r j - r i) := by
  intro ℓ
  induction ℓ with
  | zero => intro _ j hj; omega
  | succ ℓ ih =>
    intro hr j hj
    rcases Nat.lt_or_ge j ℓ with hjl | hjl
    · have hne : ℓ ≠ j := by omega
      rw [Finset.range_add_one, Finset.erase_insert_of_ne hne,
        Finset.prod_insert (by simp)]
      have h1 := ih (fun i k hik hk => hr i k hik (by omega)) j hjl
      have h2 : r j - r ℓ < 0 := by linarith [hr j ℓ hjl (by omega)]
      rw [show ℓ + 1 - 1 - j = (ℓ - 1 - j) + 1 by omega, pow_succ]
      nlinarith
    · have hjeq : j = ℓ := by omega
      subst hjeq
      rw [Finset.range_add_one, Finset.erase_insert (by simp), show j + 1 - 1 - j = 0 by omega,
        pow_zero, one_mul]
      exact Finset.prod_pos fun i hi => by
        have := hr i j (Finset.mem_range.1 hi) (by omega); linarith

lemma P_ne_zero (N : ℕ) {y : ℝ} (hy : 0 ≤ y) (ℓ : ℕ) : P N y ℓ ≠ 0 := by
  intro h; have := P_eval_pos N hy ℓ (le_refl 0); rw [h, eval_zero] at this; exact lt_irrefl 0 this

/-- With `ℓ` distinct roots, `P_ℓ = lc · ∏ (X - r_i)`. -/
lemma P_factor (N : ℕ) {y : ℝ} (hy : 0 < y) (ℓ : ℕ) (r : ℕ → ℝ)
    (hr : ∀ i k, i < k → k < ℓ → r i < r k) (hroot : ∀ j < ℓ, (P N y ℓ).eval (r j) = 0) :
    P N y ℓ = C (P N y ℓ).leadingCoeff * Lagrange.nodal (range ℓ) r := by
  have hinj : Set.InjOn r (range ℓ : Set ℕ) := by
    intro i hi k hk hik
    simp only [coe_range, Set.mem_Iio] at hi hk
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hr i k h hk).ne hik
    · exact (hr k i h hi).ne hik.symm
  have hP0 := P_ne_zero N hy.le ℓ
  have hlc0 : (P N y ℓ).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
  have hdegP : (P N y ℓ).degree = ℓ := by
    rw [degree_eq_natDegree hP0, natDegree_P N hy.ne' ℓ]
  have hdegQ : (C (P N y ℓ).leadingCoeff * Lagrange.nodal (range ℓ) r).degree = ℓ := by
    rw [degree_C_mul hlc0, Lagrange.degree_nodal, card_range]
  have hlt : (P N y ℓ - C (P N y ℓ).leadingCoeff * Lagrange.nodal (range ℓ) r).degree <
      #(range ℓ) := by
    rw [card_range, ← hdegP]
    refine degree_sub_lt_left (by rw [hdegP, hdegQ]) hP0 ?_
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.2 hlc0), Lagrange.nodal_monic.leadingCoeff,
      mul_one]
  have := Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (range ℓ) hinj hlt (fun i hi => by
    rw [eval_sub, hroot i (mem_range.1 hi), eval_mul, Lagrange.eval_nodal_at_node hi, mul_zero,
      sub_zero])
  exact sub_eq_zero.1 this

lemma P_deriv_at_root (N : ℕ) {y : ℝ} (hy : 0 < y) (ℓ : ℕ) (r : ℕ → ℝ)
    (hr : ∀ i k, i < k → k < ℓ → r i < r k) (hroot : ∀ j < ℓ, (P N y ℓ).eval (r j) = 0)
    {j : ℕ} (hj : j < ℓ) :
    (derivative (P N y ℓ)).eval (r j) =
      (P N y ℓ).leadingCoeff * ∏ i ∈ (range ℓ).erase j, (r j - r i) := by
  conv_lhs => rw [P_factor N hy ℓ r hr hroot]
  rw [derivative_C_mul, eval_mul, eval_C, Lagrange.eval_nodal_derivative_eval_node_eq
    (mem_range.2 hj), Lagrange.eval_nodal]

lemma leadingCoeff_P_pos (N : ℕ) {y : ℝ} (hy : 0 < y) (ℓ : ℕ) : 0 < (P N y ℓ).leadingCoeff := by
  rw [leadingCoeff_P N hy.ne' ℓ]; positivity

/-- **Real-rootedness.** `P_ℓ` has `ℓ` distinct real roots, all negative. -/
theorem real_rooted (N : ℕ) {y : ℝ} (hy : 0 < y) : ∀ ℓ, ∃ r : ℕ → ℝ,
    (∀ i k, i < k → k < ℓ → r i < r k) ∧ (∀ j < ℓ, (P N y ℓ).eval (r j) = 0) ∧
      (∀ j < ℓ, r j < 0) := by
  intro ℓ
  induction ℓ with
  | zero => exact ⟨fun _ => 0, by intros; omega, by intros; omega, by intros; omega⟩
  | succ ℓ ih =>
    obtain ⟨r, hr, hroot, hneg⟩ := ih
    set f : ℝ → ℝ := fun t => (P N y (ℓ + 1)).eval t with hf
    have hlc := leadingCoeff_P_pos N hy ℓ
    -- sign of `P_{ℓ+1}` at the roots of `P_ℓ`
    have hsign_r : ∀ j < ℓ, 0 < (-1) ^ (ℓ - j) * f (r j) := by
      intro j hj
      have hW := W_pos N hy ℓ (r j)
      simp only [W, eval_sub, eval_mul, hroot j hj, mul_zero, zero_sub] at hW
      rw [P_deriv_at_root N hy ℓ r hr hroot hj] at hW
      have hA := sign_prod_erase r ℓ hr j hj
      set Pr := ∏ i ∈ (range ℓ).erase j, (r j - r i)
      have hσ : ((-1 : ℝ) ^ (ℓ - 1 - j)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [show ℓ - j = (ℓ - 1 - j) + 1 by omega, pow_succ]
      have h1 : 0 < -(f (r j) * Pr) := by
        have : 0 < (P N y ℓ).leadingCoeff * -(f (r j) * Pr) := by
          simp only [hf]; nlinarith
        exact pos_of_mul_pos_right this hlc.le
      have h2 : 0 < ((-1) ^ (ℓ - 1 - j) * -1 * f (r j)) * ((-1) ^ (ℓ - 1 - j) * Pr) := by
        have : ((-1) ^ (ℓ - 1 - j) * -1 * f (r j)) * ((-1) ^ (ℓ - 1 - j) * Pr) =
            ((-1 : ℝ) ^ (ℓ - 1 - j)) ^ 2 * -(f (r j) * Pr) := by ring
        rw [this, hσ, one_mul]; exact h1
      exact pos_of_mul_pos_left h2 hA.le
    -- far-left point
    have hdeg : (P N y (ℓ + 1)).natDegree = ℓ + 1 := natDegree_P N hy.ne' (ℓ + 1)
    obtain ⟨M, hM, hMsign⟩ := exists_far_left (P N y (ℓ + 1)) (by rw [hdeg]; omega)
      (leadingCoeff_P_pos N hy (ℓ + 1)) (min (r 0) 0)
    rw [hdeg] at hMsign
    set q : ℕ → ℝ := fun i => if i = 0 then M else if i ≤ ℓ then r (i - 1) else 0 with hq
    have hsign : ∀ i ≤ ℓ + 1, 0 < (-1) ^ (ℓ + 1 - i) * f (q i) := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simpa [q, hf] using hMsign
      rcases Nat.lt_or_ge ℓ i with hil | hil
      · have : i = ℓ + 1 := by omega
        subst this
        simp only [q, show ℓ + 1 ≠ 0 by omega, ite_false, show ¬ (ℓ + 1 ≤ ℓ) by omega,
          Nat.sub_self, pow_zero, one_mul, hf]
        exact P_eval_pos N hy.le (ℓ + 1) le_rfl
      · have := hsign_r (i - 1) (by omega)
        simp only [q, show i ≠ 0 by omega, ite_false, hil, ite_true]
        rwa [show ℓ + 1 - i = ℓ - (i - 1) by omega]
    have hqinc : ∀ i < ℓ + 1, q i < q (i + 1) := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp only [q, ite_true, show (0 + 1 ≠ 0) by omega, ite_false]
        split_ifs with h
        · exact lt_of_lt_of_le hM (min_le_left _ _)
        · exact lt_of_lt_of_le hM (min_le_right _ _)
      · simp only [q, show i ≠ 0 by omega, show i + 1 ≠ 0 by omega, ite_false,
          show i ≤ ℓ by omega, ite_true]
        split_ifs with h
        · exact hr (i - 1) (i + 1 - 1) (by omega) (by omega)
        · exact hneg (i - 1) (by omega)
    have hprod : ∀ i < ℓ + 1, f (q i) * f (q (i + 1)) < 0 := by
      intro i hi
      have h1 := hsign i (by omega)
      have h2 := hsign (i + 1) (by omega)
      rw [show ℓ + 1 - i = (ℓ + 1 - (i + 1)) + 1 by omega, pow_succ] at h1
      set σ : ℝ := (-1) ^ (ℓ + 1 - (i + 1))
      have hσ : σ ^ 2 = 1 := by simp only [σ]; rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have : 0 < (σ * -1 * f (q i)) * (σ * f (q (i + 1))) := mul_pos h1 h2
      nlinarith
    obtain ⟨s, hs⟩ := roots_between f (P N y (ℓ + 1)).continuous q (ℓ + 1) hqinc hprod
    have hmono := mono_of_succ q (ℓ + 1) hqinc
    refine ⟨s, fun i k hik hk => ?_, fun j hj => (hs j hj).2.2, fun j hj => ?_⟩
    · exact lt_of_lt_of_le (hs i (by omega)).2.1
        (le_trans (hmono (i + 1) k (by omega) (by omega)) (hs k hk).1.le)
    · have h1 := (hs j hj).2.1
      have h2 := hmono (j + 1) (ℓ + 1) (by omega) le_rfl
      have h3 : q (ℓ + 1) = 0 := by simp [q]
      linarith

end Haddou
