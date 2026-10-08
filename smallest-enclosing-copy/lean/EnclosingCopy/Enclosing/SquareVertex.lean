import EnclosingCopy.Enclosing.RegularArea
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The square: the vertex term `1/12`, and `p₄ = 1/4`

Theorem 8 writes `p = V(K) T_nd(K) + (segment term)`. For the square in the normalisation of
Section 7 (sides `s ∈ [-1, 1]`, `h = 1`), `V = q tan(π/q)/(4q⁴) = 1/256` (`V_regular_full`) and the
segment term is `1/6` (`segment_term_square`). Here we compute

  `T_nd = (1/24) ∑_{k : Fin 4 → Fin 4} ∫_{[-1,1]⁴} |det A(k, σ)| 1{KKT(k, σ)} dσ = 64/3`,

where row `i` of `A(k, σ)` is `(1, u_{k i}, -σ i)` and `KKT` says `e₁ = ∑ λᵢ (row i)` with all
`λᵢ > 0`. The steps:

1. `integrand_zero_of_not_bij`: if KKT holds and `det A ≠ 0`, every side is used once. From
   `∑ λ u = 0` with `λ > 0`, side 0 is used iff side 2 is, and side 1 iff side 3; `det ≠ 0` forces
   both pairs to appear.
2. `integrand_perm`: for a bijection `k`, reordering the rows gives the identity tuple at `σ ∘ k⁻¹`.
3. `integrand_id`: for one point per side, `det A = 2 (A - B)` with `A = σ₀ + σ₂`,
   `B = σ₁ + σ₃`, and KKT holds iff `A B < 0` or `A = B = 0`; so the integrand is
   `2 |A - B| 1{A B < 0}`.
4. `integral_id`: that integral factorises over the pairs `(σ₀, σ₂)`, `(σ₁, σ₃)`:
   `2 · 4 · (4/3) · 2 = 64/3`.

Then `1/256 · 64/3 = 1/12` and `p₄ = 1/12 + 1/6 = 1/4` (`p_square`).
-/

namespace Enclosing

open MeasureTheory Set Real Matrix

/-- Normals of the square: `u_j = (ux j, uy j)`. -/
def ux : Fin 4 → ℝ := ![1, 0, -1, 0]
def uy : Fin 4 → ℝ := ![0, 1, 0, -1]

lemma un_four (j : Fin 4) : un 4 j = (ux j, uy j) := by
  have c1 : cos (2 * π / 4) = 0 := by rw [show 2 * π / 4 = π / 2 by ring, cos_pi_div_two]
  have s1 : sin (2 * π / 4) = 1 := by rw [show 2 * π / 4 = π / 2 by ring, sin_pi_div_two]
  have c2 : cos (2 * π * 2 / 4) = -1 := by rw [show 2 * π * 2 / 4 = π by ring, cos_pi]
  have s2 : sin (2 * π * 2 / 4) = 0 := by rw [show 2 * π * 2 / 4 = π by ring, sin_pi]
  have c3 : cos (2 * π * 3 / 4) = 0 := by
    rw [show 2 * π * 3 / 4 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two, neg_zero]
  have s3 : sin (2 * π * 3 / 4) = -1 := by
    rw [show 2 * π * 3 / 4 = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]
  fin_cases j <;> simp [un, ux, uy, c1, s1, c2, s2, c3, s3]

/-- The matrix of Theorem 8: row `i` is `(h, u_{k i}, -σ i)` with `h = 1`. -/
noncomputable def Amat (k : Fin 4 → Fin 4) (σ : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i => ![1, (un 4 (k i)).1, (un 4 (k i)).2, -σ i]

/-- The KKT condition: `e₁` is a positive combination of the rows. -/
def KKT (k : Fin 4 → Fin 4) (σ : Fin 4 → ℝ) : Prop :=
  ∃ l : Fin 4 → ℝ, (∀ i, 0 < l i) ∧ ∀ c, ∑ i, l i * Amat k σ i c = if c = 0 then 1 else 0

/-- The integrand of `T_nd`. -/
noncomputable def integrand (k : Fin 4 → Fin 4) (σ : Fin 4 → ℝ) : ℝ :=
  {σ | KKT k σ}.indicator (fun σ => |(Amat k σ).det|) σ

lemma Amat_apply (k : Fin 4 → Fin 4) (σ : Fin 4 → ℝ) (i : Fin 4) :
    Amat k σ i 0 = 1 ∧ Amat k σ i 1 = ux (k i) ∧ Amat k σ i 2 = uy (k i) ∧ Amat k σ i 3 = -σ i := by
  simp [Amat, un_four]

/-! ### Step 1: only one point per side counts -/

lemma integrand_zero_of_not_bij {k : Fin 4 → Fin 4} (hk : ¬ Function.Bijective k)
    (σ : Fin 4 → ℝ) : integrand k σ = 0 := by
  unfold integrand
  by_cases hK : KKT k σ
  swap; · exact indicator_of_notMem (show σ ∉ {σ | KKT k σ} from hK) _
  rw [indicator_of_mem (show σ ∈ {σ | KKT k σ} from hK), abs_eq_zero]
  obtain ⟨l, hl, hc⟩ := hK
  have hx : ∑ i, l i * ux (k i) = 0 := by
    have h := hc 1
    simp only [fun i => (Amat_apply k σ i).2.1] at h
    rw [h, if_neg (by decide)]
  have hy : ∑ i, l i * uy (k i) = 0 := by
    have h := hc 2
    simp only [fun i => (Amat_apply k σ i).2.2.1] at h
    rw [h, if_neg (by decide)]
  -- a side used with positive weight forces its opposite side to be used
  have opp : ∀ j : Fin 4, (∃ i, k i = j) → ∃ i, k i = j + 2 := by
    intro j ⟨i₀, hi₀⟩
    by_contra hno
    push Not at hno
    have hl0 := hl i₀
    fin_cases j
    · have : 0 < ∑ i, l i * ux (k i) := by
        apply Finset.sum_pos'
        · intro i _
          have h1 := hno i; have h2 := hl i
          revert h1; generalize k i = m; intro h1
          fin_cases m <;> simp [ux] at h1 ⊢ <;> linarith [hl i]
        · exact ⟨i₀, Finset.mem_univ _, by simp [hi₀, ux, hl0]⟩
      linarith
    · have : 0 < ∑ i, l i * uy (k i) := by
        apply Finset.sum_pos'
        · intro i _
          have h1 := hno i; have h2 := hl i
          revert h1; generalize k i = m; intro h1
          fin_cases m <;> simp [uy] at h1 ⊢ <;> linarith [hl i]
        · exact ⟨i₀, Finset.mem_univ _, by simp [hi₀, uy, hl0]⟩
      linarith
    · have : ∑ i, l i * ux (k i) < 0 := by
        apply Finset.sum_neg'
        · intro i _
          have h1 := hno i; have h2 := hl i
          revert h1; generalize k i = m; intro h1
          fin_cases m <;> simp [ux] at h1 ⊢ <;> linarith [hl i]
        · exact ⟨i₀, Finset.mem_univ _, by simp [hi₀, ux, hl0]⟩
      linarith
    · have : ∑ i, l i * uy (k i) < 0 := by
        apply Finset.sum_neg'
        · intro i _
          have h1 := hno i; have h2 := hl i
          revert h1; generalize k i = m; intro h1
          fin_cases m <;> simp [uy] at h1 ⊢ <;> linarith [hl i]
        · exact ⟨i₀, Finset.mem_univ _, by simp [hi₀, uy, hl0]⟩
      linarith
  by_contra hdet
  apply hk
  -- `det ≠ 0`: the `ux` column and the `uy` column are both nonzero
  have hxcol : ∃ i, k i = 0 ∨ k i = 2 := by
    by_contra h
    push Not at h
    apply hdet
    apply det_eq_zero_of_column_eq_zero 1
    intro i
    rw [(Amat_apply k σ i).2.1]
    have := h i
    generalize k i = m at *
    fin_cases m <;> simp_all [ux]
  have hycol : ∃ i, k i = 1 ∨ k i = 3 := by
    by_contra h
    push Not at h
    apply hdet
    apply det_eq_zero_of_column_eq_zero 2
    intro i
    rw [(Amat_apply k σ i).2.2.1]
    have := h i
    generalize k i = m at *
    fin_cases m <;> simp_all [uy]
  have hsurj : Function.Surjective k := by
    have h0 : ∃ i, k i = 0 := by
      obtain ⟨i, hi | hi⟩ := hxcol
      · exact ⟨i, hi⟩
      · obtain ⟨i', hi'⟩ := opp 2 ⟨i, hi⟩; exact ⟨i', by simpa using hi'⟩
    have h1 : ∃ i, k i = 1 := by
      obtain ⟨i, hi | hi⟩ := hycol
      · exact ⟨i, hi⟩
      · obtain ⟨i', hi'⟩ := opp 3 ⟨i, hi⟩; exact ⟨i', by simpa using hi'⟩
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · simpa using opp 0 h0
    · simpa using opp 1 h1
  exact (Finite.injective_iff_surjective.2 hsurj) |> fun hi => ⟨hi, hsurj⟩

/-! ### Step 2: a bijective tuple is the identity tuple in another order -/

lemma integrand_perm (e : Equiv.Perm (Fin 4)) (σ : Fin 4 → ℝ) :
    integrand e σ = integrand id (σ ∘ e.symm) := by
  have hA : Amat e σ = (Amat id (σ ∘ e.symm)).submatrix e id := by
    funext i c; simp [Amat]
  have hK : KKT e σ ↔ KKT id (σ ∘ e.symm) := by
    rw [KKT, KKT, hA]
    constructor
    · rintro ⟨l, hl, hc⟩
      refine ⟨l ∘ e.symm, fun i => hl _, fun c => ?_⟩
      rw [← hc c, ← Equiv.sum_comp e]
      simp
    · rintro ⟨l, hl, hc⟩
      refine ⟨l ∘ e, fun i => hl _, fun c => ?_⟩
      rw [← hc c]
      exact Equiv.sum_comp e (fun j => l j * Amat id (σ ∘ e.symm) j c)
  unfold integrand
  by_cases h : KKT e σ
  · rw [indicator_of_mem (show σ ∈ {σ | KKT e σ} from h),
      indicator_of_mem (show σ ∘ e.symm ∈ {σ | KKT id σ} from hK.1 h), hA, det_permute, abs_mul]
    have hs : |((Equiv.Perm.sign e : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]
    rw [hs, one_mul]
  · rw [indicator_of_notMem (show σ ∉ {σ | KKT e σ} from h),
      indicator_of_notMem (show σ ∘ e.symm ∉ {σ | KKT id σ} from fun h' => h (hK.2 h'))]

/-! ### Step 3: one point per side -/

/-- The integrand for one point per side, as a function of `A = σ₀ + σ₂`, `B = σ₁ + σ₃`. -/
noncomputable def Fsq (A B : ℝ) : ℝ := if A * B < 0 then 2 * |A - B| else 0

lemma det_id (σ : Fin 4 → ℝ) : (Amat id σ).det = 2 * ((σ 0 + σ 2) - (σ 1 + σ 3)) := by
  have hM : Amat id σ = !![1, 1, 0, -σ 0; 1, 0, 1, -σ 1; 1, -1, 0, -σ 2; 1, 0, -1, -σ 3] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Amat, un_four, ux, uy]
  rw [hM, Matrix.det_succ_row_zero]
  have e1 : Fin.succAbove (1 : Fin 4) 2 = 3 := by decide
  have e3 : Fin.succAbove (3 : Fin 4) 2 = 2 := by decide
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, e1, e3]
  ring

lemma KKT_id_iff (σ : Fin 4 → ℝ) :
    KKT id σ ↔ (σ 0 + σ 2) * (σ 1 + σ 3) < 0 ∨ (σ 0 + σ 2 = 0 ∧ σ 1 + σ 3 = 0) := by
  set A := σ 0 + σ 2
  set B := σ 1 + σ 3
  simp only [KKT, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.sum_univ_zero, Amat, un_four, id,
    ux, uy]
  simp
  constructor
  · rintro ⟨l, ⟨hl0, hl1, hl2, hl3⟩, h0, h1, h2, h3⟩
    have e02 : l 0 = l 2 := by linarith
    have e13 : l 1 = l 3 := by linarith
    have hAB : l 0 * A + l 1 * B = 0 := by
      simp only [A, B]; linear_combination -h3 + σ 2 * e02 + σ 3 * e13
    by_cases hB : B = 0
    · right; refine ⟨?_, hB⟩
      rw [hB, mul_zero, add_zero] at hAB
      exact (mul_eq_zero.1 hAB).resolve_left hl0.ne'
    · left
      have : l 0 * (A * B) = -(l 1 * B ^ 2) := by linear_combination B * hAB
      have hB2 : 0 < B ^ 2 := by positivity
      nlinarith
  · rintro (h | ⟨hA, hB⟩)
    · have hne : B - A ≠ 0 := by
        intro h'; have hBA : B = A := by linarith
        rw [hBA] at h; nlinarith [sq_nonneg A]
      have hsgn : (0 < A ∧ B < 0) ∨ (A < 0 ∧ 0 < B) := by
        rcases lt_trichotomy A 0 with ha | ha | ha
        · right; exact ⟨ha, by nlinarith⟩
        · simp [ha] at h
        · left; exact ⟨ha, by nlinarith⟩
      let a := B / (2 * (B - A))
      let b := -A / (2 * (B - A))
      have ha : 0 < a := by
        rcases hsgn with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact div_pos_of_neg_of_neg h2 (by linarith)
        · exact div_pos h2 (by linarith)
      have hb : 0 < b := by
        rcases hsgn with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
        · exact div_pos (by linarith) (by linarith)
      refine ⟨![a, b, a, b], by simp [ha, hb], ?_, ?_, ?_, ?_⟩
      · simp [a, b]; field_simp; ring
      · simp
      · simp
      · simp [a, b, A, B] at *; field_simp; ring
    · refine ⟨fun _ => 1 / 4, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
      simp only [A, B] at hA hB
      linarith

lemma integrand_id (σ : Fin 4 → ℝ) : integrand id σ = Fsq (σ 0 + σ 2) (σ 1 + σ 3) := by
  unfold integrand Fsq
  by_cases h : KKT id σ
  · rw [indicator_of_mem (show σ ∈ {σ | KKT id σ} from h), det_id]
    rcases (KKT_id_iff σ).1 h with h' | ⟨h1, h2⟩
    · rw [if_pos h', abs_mul, abs_two]
    · rw [h1, h2]; simp
  · rw [indicator_of_notMem (show σ ∉ {σ | KKT id σ} from h), if_neg]
    exact fun h' => h ((KKT_id_iff σ).2 (Or.inl h'))

/-! ### Step 4: the integral factorises over the two pairs of opposite sides -/

/-- Uniform (Lebesgue) measure on a side `[-1, 1]`. -/
noncomputable def nu1 : Measure ℝ := volume.restrict (Icc (-1 : ℝ) 1)

instance : IsFiniteMeasure nu1 := isFiniteMeasure_restrict.2 (by simp)

/-- The four pair functions, of `w = x + y` for the two points on a pair of opposite sides. -/
noncomputable def Pp (p : ℝ × ℝ) : ℝ := max 0 (p.1 + p.2)
noncomputable def Pn (p : ℝ × ℝ) : ℝ := max 0 (-(p.1 + p.2))
noncomputable def Ip (p : ℝ × ℝ) : ℝ := {p : ℝ × ℝ | 0 < p.1 + p.2}.indicator 1 p
noncomputable def In (p : ℝ × ℝ) : ℝ := {p : ℝ × ℝ | p.1 + p.2 < 0}.indicator 1 p

lemma Fsq_decomp (p q : ℝ × ℝ) :
    Fsq (p.1 + p.2) (q.1 + q.2) = 2 * (Pp p * In q + Ip p * Pn q + Pn p * Ip q + In p * Pp q) := by
  simp only [Fsq, Pp, Pn, Ip, In, indicator, mem_setOf_eq, Pi.one_apply, max_def]
  generalize p.1 + p.2 = A
  generalize q.1 + q.2 = B
  rcases lt_trichotomy A 0 with hA | rfl | hA <;> rcases lt_trichotomy B 0 with hB | rfl | hB <;>
  split_ifs <;> first
    | (exfalso; linarith)
    | ring1
    | (rw [abs_of_pos (by linarith)]; ring1)
    | (rw [abs_of_neg (by linarith)]; ring1)
    | (exfalso; nlinarith)

lemma integral_nu1 (g : ℝ → ℝ) : ∫ y, g y ∂nu1 = ∫ y in (-1 : ℝ)..1, g y := by
  rw [nu1, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num)]

lemma prod_nu1 : nu1.prod nu1 = volume.restrict (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := by
  rw [nu1, Measure.prod_restrict, Measure.volume_eq_prod]

lemma integrable_cont {f : ℝ × ℝ → ℝ} (hf : Continuous f) : Integrable f (nu1.prod nu1) := by
  rw [prod_nu1]
  exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma integrable_Pp : Integrable Pp (nu1.prod nu1) := integrable_cont (by unfold Pp; fun_prop)
lemma integrable_Pn : Integrable Pn (nu1.prod nu1) := integrable_cont (by unfold Pn; fun_prop)
lemma integrable_Ip : Integrable Ip (nu1.prod nu1) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_lt measurable_const (by fun_prop))
lemma integrable_In : Integrable In (nu1.prod nu1) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_lt (by fun_prop) measurable_const)

/-- A 2-dimensional integral over `[-1,1]²`, given the inner integral on `[-1, 1]`. -/
lemma pair_integral {f : ℝ × ℝ → ℝ} (hf : Integrable f (nu1.prod nu1)) {g : ℝ → ℝ}
    (hg : ∀ x ∈ Icc (-1 : ℝ) 1, ∫ y, f (x, y) ∂nu1 = g x) :
    ∫ z, f z ∂(nu1.prod nu1) = ∫ x in (-1 : ℝ)..1, g x := by
  rw [integral_prod _ hf]
  show ∫ x in Icc (-1 : ℝ) 1, (∫ y, f (x, y) ∂nu1) = _
  rw [setIntegral_congr_fun measurableSet_Icc hg, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num)]

lemma inner_Pp {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : ∫ y, Pp (x, y) ∂nu1 = (x + 1) ^ 2 / 2 := by
  obtain ⟨hx1, hx2⟩ := hx
  rw [integral_nu1]
  simp only [Pp]
  have hc : Continuous fun y : ℝ => max 0 (x + y) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := -x) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_congr (a := -1) (b := -x) (g := fun _ => (0 : ℝ)) fun y hy => by
      rw [uIcc_of_le (by linarith)] at hy; exact max_eq_left (show x + y ≤ 0 by linarith [(mem_Icc.1 hy).2]),
    intervalIntegral.integral_congr (a := -x) (b := 1) (g := fun y => x + y) fun y hy => by
      rw [uIcc_of_le (by linarith)] at hy; exact max_eq_right (show 0 ≤ x + y by linarith [(mem_Icc.1 hy).1])]
  rw [intervalIntegral.integral_add intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  simp [integral_id]
  ring

lemma inner_Pn {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : ∫ y, Pn (x, y) ∂nu1 = (1 - x) ^ 2 / 2 := by
  obtain ⟨hx1, hx2⟩ := hx
  rw [integral_nu1]
  simp only [Pn]
  have hc : Continuous fun y : ℝ => max 0 (-(x + y)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := -x) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_congr (a := -1) (b := -x) (g := fun y => -x - y) fun y hy => by
      rw [uIcc_of_le (by linarith)] at hy
      simp only; rw [max_eq_right (show 0 ≤ -(x + y) by linarith [(mem_Icc.1 hy).2])]; ring,
    intervalIntegral.integral_congr (a := -x) (b := 1) (g := fun _ => (0 : ℝ)) fun y hy => by
      rw [uIcc_of_le (by linarith)] at hy; exact max_eq_left (show -(x + y) ≤ 0 by linarith [(mem_Icc.1 hy).1])]
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  simp [integral_id]
  ring

lemma inner_Ip {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : ∫ y, Ip (x, y) ∂nu1 = x + 1 := by
  have : (fun y => Ip (x, y)) = (Ioi (-x)).indicator 1 := by
    funext y; simp only [Ip, indicator, mem_setOf_eq, mem_Ioi]
    congr 1; exact propext ⟨fun h => by linarith, fun h => by linarith⟩
  rw [this, integral_indicator_one measurableSet_Ioi, nu1, measureReal_restrict_apply measurableSet_Ioi,
    show Ioi (-x) ∩ Icc (-1) 1 = Ioc (-x) 1 by
      ext y; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith [hx.2], h3⟩,
    Real.volume_real_Ioc_of_le (by linarith [hx.1])]
  ring

lemma inner_In {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : ∫ y, In (x, y) ∂nu1 = 1 - x := by
  have : (fun y => In (x, y)) = (Iio (-x)).indicator 1 := by
    funext y; simp only [In, indicator, mem_setOf_eq, mem_Iio]
    congr 1; exact propext ⟨fun h => by linarith, fun h => by linarith⟩
  rw [this, integral_indicator_one measurableSet_Iio, nu1, measureReal_restrict_apply measurableSet_Iio,
    show Iio (-x) ∩ Icc (-1) 1 = Ico (-1) (-x) by
      ext y; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨h1, h2, by linarith [hx.1]⟩,
    Real.volume_real_Ico_of_le (by linarith [hx.2])]
  ring

lemma integral_Pp : ∫ z, Pp z ∂(nu1.prod nu1) = 4 / 3 := by
  rw [pair_integral integrable_Pp fun x hx => inner_Pp hx,
    intervalIntegral.integral_comp_add_right (fun t => t ^ 2 / 2) 1, intervalIntegral.integral_div]
  simp [integral_pow]
  norm_num

lemma integral_Pn : ∫ z, Pn z ∂(nu1.prod nu1) = 4 / 3 := by
  rw [pair_integral integrable_Pn fun x hx => inner_Pn hx,
    intervalIntegral.integral_comp_sub_left (fun t => t ^ 2 / 2) 1, intervalIntegral.integral_div]
  simp [integral_pow]
  norm_num

lemma integral_Ip : ∫ z, Ip z ∂(nu1.prod nu1) = 2 := by
  rw [pair_integral integrable_Ip fun x hx => inner_Ip hx,
    intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id intervalIntegrable_const]
  simp [integral_id]
  norm_num

lemma integral_In : ∫ z, In z ∂(nu1.prod nu1) = 2 := by
  rw [pair_integral integrable_In fun x hx => inner_In hx,
    intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  simp [integral_id]
  norm_num

/-! ### Step 4b: from `[-1,1]⁴` to the product of the two pairs -/

/-- The law of four positions, one per coordinate. -/
noncomputable def mu4 : Measure (Fin 4 → ℝ) := Measure.pi fun _ => nu1

/-- `Fin 4 ≃ Fin 2 ⊕ Fin 2`, pairing the opposite sides `{0, 2}` and `{1, 3}`. -/
def pairing : Fin 4 ≃ Fin 2 ⊕ Fin 2 where
  toFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  invFun := Sum.elim ![0, 2] ![1, 3]
  left_inv := by decide
  right_inv := by decide

/-- `σ ↦ ((σ₀, σ₂), (σ₁, σ₃))`. -/
noncomputable def toPairs : (Fin 4 → ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) pairing).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)).trans
      (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow))

lemma toPairs_apply (σ : Fin 4 → ℝ) : toPairs σ = ((σ 0, σ 2), (σ 1, σ 3)) := by
  have h : ∀ i : Fin 4, (MeasurableEquiv.piCongrLeft (fun _ => ℝ) pairing σ) (pairing i) = σ i :=
    fun i => Equiv.piCongrLeft_apply_apply _ _ _ _
  simp only [toPairs, MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr,
    MeasurableEquiv.sumPiEquivProdPi]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · exact h 0
  · exact h 2
  · exact h 1
  · exact h 3

lemma toPairs_mp : MeasurePreserving toPairs mu4 ((nu1.prod nu1).prod (nu1.prod nu1)) :=
  ((measurePreserving_finTwoArrow nu1).prod (measurePreserving_finTwoArrow nu1)).comp
    ((measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => nu1)).comp
      (measurePreserving_piCongrLeft (fun _ : Fin 2 ⊕ Fin 2 => nu1) pairing))

/-- **The identity tuple integrates to `64/3`.** -/
theorem integral_id : ∫ σ, integrand id σ ∂mu4 = 64 / 3 := by
  simp_rw [integrand_id]
  have h := toPairs_mp.integral_comp' (g := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
    Fsq (z.1.1 + z.1.2) (z.2.1 + z.2.2))
  simp only [toPairs_apply] at h
  rw [h]
  simp_rw [Fsq_decomp]
  have i1 := integrable_Pp.mul_prod integrable_In
  have i2 := integrable_Ip.mul_prod integrable_Pn
  have i3 := integrable_Pn.mul_prod integrable_Ip
  have i4 := integrable_In.mul_prod integrable_Pp
  rw [integral_const_mul,
    integral_add (f := fun a : (ℝ × ℝ) × (ℝ × ℝ) => Pp a.1 * In a.2 + Ip a.1 * Pn a.2 + Pn a.1 * Ip a.2)
      (g := fun a => In a.1 * Pp a.2) ((i1.add i2).add i3) i4,
    integral_add (f := fun a : (ℝ × ℝ) × (ℝ × ℝ) => Pp a.1 * In a.2 + Ip a.1 * Pn a.2)
      (g := fun a => Pn a.1 * Ip a.2) (i1.add i2) i3,
    integral_add (f := fun a : (ℝ × ℝ) × (ℝ × ℝ) => Pp a.1 * In a.2)
      (g := fun a => Ip a.1 * Pn a.2) i1 i2,
    integral_prod_mul Pp In, integral_prod_mul Ip Pn, integral_prod_mul Pn Ip,
    integral_prod_mul In Pp, integral_Pp, integral_Pn, integral_Ip, integral_In]
  norm_num

/-! ### Step 5: `T_nd = 64/3`, and `p₄ = 1/4` -/

lemma integral_bij {k : Fin 4 → Fin 4} (hk : Function.Bijective k) :
    ∫ σ, integrand k σ ∂mu4 = 64 / 3 := by
  set e := Equiv.ofBijective k hk
  have hke : k = ⇑e := rfl
  have hmp := measurePreserving_piCongrLeft (fun _ : Fin 4 => nu1) e
  have happ : ∀ σ : Fin 4 → ℝ, MeasurableEquiv.piCongrLeft (fun _ => ℝ) e σ = σ ∘ e.symm := by
    intro σ; funext j
    rw [← e.apply_symm_apply j]
    simp only [MeasurableEquiv.coe_piCongrLeft, Function.comp_apply, Equiv.symm_apply_apply]
    exact Equiv.piCongrLeft_apply_apply _ _ _ _
  rw [hke]
  simp_rw [integrand_perm e]
  have h := hmp.integral_comp' (g := fun τ => integrand id τ)
  simp only [happ] at h
  rw [show (Measure.pi fun _ : Fin 4 => nu1) = mu4 from rfl] at h
  rw [h, integral_id]

lemma card_bij :
    (Finset.univ.filter fun k : Fin 4 → Fin 4 => Function.Bijective k).card = 24 := by
  decide

/-- **`T_nd` for the square is `64/3`.** -/
theorem Tnd_square : (1 / 24) * ∑ k : Fin 4 → Fin 4, ∫ σ, integrand k σ ∂mu4 = 64 / 3 := by
  have hk : ∀ k : Fin 4 → Fin 4,
      ∫ σ, integrand k σ ∂mu4 = if Function.Bijective k then 64 / 3 else 0 := by
    intro k
    split_ifs with hb
    · exact integral_bij hb
    · simp [integrand_zero_of_not_bij hb]
  simp_rw [hk]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, card_bij]
  norm_num

/-- **The square: `p₄ = V · T_nd + (segment term) = 1/256 · 64/3 + 1/6 = 1/4`.** The first factor
is the vertex integral of `V_regular_full`, the last term is `segment_term_square`. -/
theorem p_square :
    (∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * ((4 : ℕ) : ℝ) * t)) * (volume (Rreg 4 t Θ)).toReal) *
        ((1 / 24) * ∑ k : Fin 4 → Fin 4, ∫ σ, integrand k σ ∂mu4) +
      4 * (∫ x in (-1 : ℝ)..1, ∫ s₁ in (-1 : ℝ)..x, ∫ s₂ in x..1, (s₂ - s₁)) *
        (2 * (∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * 4 * t)) *
            (volume ((fun C : ℝ × ℝ => C.1) '' Rreg 4 t Θ)).toReal)
          + 2 * (∑ j ∈ Finset.Ico (1 : ℕ) 2, 2 * sin (2 * π * j / 4)) *
            ∫ Θ, ∫ t in Ioi |Θ|, exp (-(2 * 4 * t)) * (volume (Rreg 4 t Θ)).toReal)
      = 1 / 4 := by
  rw [V_regular_full (q := 4) (by norm_num), Tnd_square, segment_term_square]
  norm_num [show π / 4 = π / 4 from rfl, tan_pi_div_four]

end Enclosing
