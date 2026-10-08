import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Order.Field

/-!
# Corollary 2: triangles

For a triangle with sides `L₁, L₂, L₃`,
`p = (1 / (2 ∑ Lᵢ²)) ∑_k L_k² g(L_i²/L_k², L_j²/L_k²)`, with
`g(α, β) = E[(1 - (α U₁ + β U₂)²)₊]`, `U₁, U₂` independent uniform on `[-1, 1]`, that is
`g(α, β) = ¼ ∫_{-1}^{1} ∫_{-1}^{1} (1 - (α u + β v)²)₊ dv du`.

The paper evaluates `g(1,1) = 13/24` through the density of `U₁ + U₂`. Here we prove a closed form
for every `α, β > 0` (`g_closed`): with `f(x) = (1 - x²)₊`, `Ψ(x) = ∫₀ˣ f` and `Φ(x) = ∫₀ˣ Ψ`,

  `g(α, β) = (Φ(α + β) - Φ(α - β)) / (2 α β)`,

and `Φ(x) = x²/2 - x⁴/12` for `|x| ≤ 1`, `Φ(x) = 2|x|/3 - 1/4` for `|x| ≥ 1`. Integrating `U₂` first
turns the inner integral into a difference of `Ψ`, integrating `U₁` turns that into differences of
`Φ`, and `Φ` is even. The paper's values follow: equilateral `13/48`, right isosceles `7/24`,
`30-60-90` `29/96`, and the obtuse/right case `g = 1 - (α² + β²)/3` when `α + β ≤ 1`.
-/

namespace Enclosing

open intervalIntegral Real

/-- `f(x) = (1 - x²)₊`. -/
noncomputable def fpos (x : ℝ) : ℝ := max 0 (1 - x ^ 2)

/-- `g(α, β) = E[(1 - (α U₁ + β U₂)²)₊]`. -/
noncomputable def gfun (α β : ℝ) : ℝ :=
  (1 / 4) * ∫ u in (-1 : ℝ)..1, ∫ v in (-1 : ℝ)..1, fpos (α * u + β * v)

/-- `Ψ(x) = ∫₀ˣ f`. -/
noncomputable def Psi (x : ℝ) : ℝ := ∫ w in (0 : ℝ)..x, fpos w

/-- `Φ(x) = ∫₀ˣ Ψ`. -/
noncomputable def Phi (x : ℝ) : ℝ := ∫ w in (0 : ℝ)..x, Psi w

lemma fpos_cont : Continuous fpos := by unfold fpos; fun_prop

lemma fpos_even (x : ℝ) : fpos (-x) = fpos x := by simp [fpos]

lemma Psi_cont : Continuous Psi := by
  unfold Psi
  exact continuous_primitive (fun a b => fpos_cont.intervalIntegrable a b) 0

lemma Psi_odd (x : ℝ) : Psi (-x) = -Psi x := by
  unfold Psi
  rw [← neg_zero, ← intervalIntegral.integral_comp_neg]
  simp only [fpos_even, neg_zero]
  rw [intervalIntegral.integral_symm]

lemma Phi_even (x : ℝ) : Phi (-x) = Phi x := by
  unfold Phi
  rw [← neg_zero, ← intervalIntegral.integral_comp_neg]
  simp only [Psi_odd, neg_zero, intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_symm, neg_neg]

/-- `∫_a^b f = Ψ(b) - Ψ(a)`. -/
lemma integral_fpos (a b : ℝ) : ∫ w in a..b, fpos w = Psi b - Psi a := by
  unfold Psi
  rw [intervalIntegral.integral_interval_sub_left (fpos_cont.intervalIntegrable _ _)
    (fpos_cont.intervalIntegrable _ _)]

/-- `∫_a^b Ψ = Φ(b) - Φ(a)`. -/
lemma integral_Psi (a b : ℝ) : ∫ w in a..b, Psi w = Phi b - Phi a := by
  unfold Phi
  rw [intervalIntegral.integral_interval_sub_left (Psi_cont.intervalIntegrable _ _)
    (Psi_cont.intervalIntegrable _ _)]

/-- **Closed form of `g`.** -/
theorem g_closed {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    gfun α β = (Phi (α + β) - Phi (α - β)) / (2 * α * β) := by
  unfold gfun
  -- inner integral over `v`: substitute `w = α u + β v`
  have inner : ∀ u : ℝ, ∫ v in (-1 : ℝ)..1, fpos (α * u + β * v)
      = (Psi (α * u + β) - Psi (α * u + -β)) / β := by
    intro u
    have := intervalIntegral.integral_comp_mul_add (a := -1) (b := 1) fpos hβ.ne' (α * u)
    simp only [smul_eq_mul] at this
    rw [show (fun v => fpos (α * u + β * v)) = fun v => fpos (β * v + α * u) by
      funext v; ring_nf, this, integral_fpos]
    rw [show β * -1 + α * u = α * u + -β by ring, show β * 1 + α * u = α * u + β by ring]
    field_simp
  simp_rw [inner]
  -- outer integral over `u`
  have hsub : ∀ c : ℝ, ∫ u in (-1 : ℝ)..1, Psi (α * u + c) = (Phi (α + c) - Phi (-α + c)) / α := by
    intro c
    have := intervalIntegral.integral_comp_mul_add (a := -1) (b := 1) Psi hα.ne' c
    simp only [smul_eq_mul] at this
    rw [this, integral_Psi, show α * -1 + c = -α + c by ring, show α * 1 + c = α + c by ring]
    field_simp
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (f := fun u => Psi (α * u + β)) (g := fun u => Psi (α * u + -β))
    ((Psi_cont.comp (by fun_prop : Continuous fun u : ℝ => α * u + β)).intervalIntegrable _ _)
    ((Psi_cont.comp (by fun_prop : Continuous fun u : ℝ => α * u + -β)).intervalIntegrable _ _)]
  · rw [hsub β, hsub (-β)]
    have e1 : Phi (-α + -β) = Phi (α + β) := by rw [← Phi_even]; ring_nf
    have e2 : Phi (-α + β) = Phi (α - β) := by rw [← Phi_even]; ring_nf
    rw [e1, e2, show α + -β = α - β by ring]
    field_simp
    ring

/-! ### Evaluating `Ψ` and `Φ` -/

lemma fpos_of_abs_le {x : ℝ} (hx : |x| ≤ 1) : fpos x = 1 - x ^ 2 := by
  unfold fpos
  apply max_eq_right
  nlinarith [abs_nonneg x, sq_abs x]

lemma fpos_of_one_le {x : ℝ} (hx : 1 ≤ x) : fpos x = 0 := by
  unfold fpos; apply max_eq_left; nlinarith

lemma Psi_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Psi x = x - x ^ 3 / 3 := by
  unfold Psi
  rw [intervalIntegral.integral_congr (g := fun w => 1 - w ^ 2) fun w hw => by
    rw [Set.uIcc_of_le h0] at hw
    exact fpos_of_abs_le (abs_le.2 ⟨by linarith [hw.1], by linarith [hw.2]⟩)]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((continuous_pow 2).intervalIntegrable _ _)]
  simp [integral_pow]
  ring

lemma Psi_one : Psi 1 = 2 / 3 := by rw [Psi_of_mem zero_le_one le_rfl]; norm_num

lemma Psi_of_one_le {x : ℝ} (hx : 1 ≤ x) : Psi x = 2 / 3 := by
  have h := integral_fpos 1 x
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun w hw => by
    rw [Set.uIcc_of_le hx] at hw; exact fpos_of_one_le hw.1] at h
  simp at h
  linarith [Psi_one]

lemma Phi_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Phi x = x ^ 2 / 2 - x ^ 4 / 12 := by
  unfold Phi
  rw [intervalIntegral.integral_congr (g := fun w => w - w ^ 3 / 3) fun w hw => by
    rw [Set.uIcc_of_le h0] at hw; exact Psi_of_mem hw.1 (hw.2.trans h1)]
  rw [intervalIntegral.integral_sub intervalIntegrable_id
    (((continuous_pow 3).div_const 3).intervalIntegrable _ _), intervalIntegral.integral_div]
  simp [integral_pow, integral_id]
  ring

lemma Phi_of_one_le {x : ℝ} (hx : 1 ≤ x) : Phi x = 2 * x / 3 - 1 / 4 := by
  have h := integral_Psi 1 x
  rw [intervalIntegral.integral_congr (g := fun _ => (2 / 3 : ℝ)) fun w hw => by
    rw [Set.uIcc_of_le hx] at hw; exact Psi_of_one_le hw.1] at h
  rw [Phi_of_mem zero_le_one le_rfl] at h
  simp at h
  linarith

/-- The obtuse or right case: if `α + β ≤ 1` the positive part is inactive. -/
theorem g_small {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (h : α + β ≤ 1) :
    gfun α β = 1 - (α ^ 2 + β ^ 2) / 3 := by
  rw [g_closed hα hβ, Phi_of_mem (by linarith) h]
  rcases le_total β α with hab | hab
  · rw [Phi_of_mem (by linarith) (by linarith)]
    field_simp; ring
  · rw [← Phi_even, Phi_of_mem (by linarith) (by linarith)]
    field_simp; ring

/-- The triangle formula of Corollary 2, as a function of the squared side lengths. -/
noncomputable def ptri (A B C : ℝ) : ℝ :=
  (1 / (2 * (A + B + C))) * (A * gfun (B / A) (C / A) + B * gfun (A / B) (C / B) +
    C * gfun (A / C) (B / C))

theorem g_one_one : gfun 1 1 = 13 / 24 := by
  rw [g_closed one_pos one_pos, Phi_of_one_le (by norm_num : (1 : ℝ) ≤ 1 + 1), sub_self,
    show Phi 0 = 0 by simp [Phi]]
  norm_num

/-- Equilateral triangle: `p = 13/48`. -/
theorem p_equilateral : ptri 1 1 1 = 13 / 48 := by
  simp only [ptri, div_one, g_one_one]; norm_num

/-- Right isosceles triangle (squared sides `1, 1, 2`): `p = 7/24`. -/
theorem p_right_isosceles : ptri 1 1 2 = 7 / 24 := by
  have g12 : gfun 1 2 = 1 / 3 := by
    rw [g_closed one_pos two_pos, Phi_of_one_le (by norm_num : (1 : ℝ) ≤ 1 + 2),
      show (1 : ℝ) - 2 = -1 by norm_num, Phi_even, Phi_of_mem zero_le_one le_rfl]
    norm_num
  have ghalf : gfun (1 / 2) (1 / 2) = 5 / 6 := by
    rw [g_small (by norm_num) (by norm_num) (by norm_num)]; norm_num
  simp only [ptri, div_one]
  rw [g12, ghalf]
  norm_num

/-- `30-60-90` triangle (squared sides `1, 3, 4`): `p = 29/96`. -/
theorem p_30_60_90 : ptri 1 3 4 = 29 / 96 := by
  have g34 : gfun 3 4 = 1 / 6 := by
    rw [g_closed (by norm_num) (by norm_num), Phi_of_one_le (by norm_num : (1 : ℝ) ≤ 3 + 4),
      show (3 : ℝ) - 4 = -1 by norm_num, Phi_even, Phi_of_mem zero_le_one le_rfl]
    norm_num
  have g_mid : gfun (1 / 3) (4 / 3) = 1 / 2 := by
    rw [g_closed (by norm_num) (by norm_num),
      Phi_of_one_le (by norm_num : (1 : ℝ) ≤ 1 / 3 + 4 / 3),
      show (1 / 3 : ℝ) - 4 / 3 = -1 by norm_num, Phi_even, Phi_of_mem zero_le_one le_rfl]
    norm_num
  have g_hyp : gfun (1 / 4) (3 / 4) = 19 / 24 := by
    rw [g_small (by norm_num) (by norm_num) (by norm_num)]; norm_num
  simp only [ptri, div_one]
  rw [g34, show (1 : ℝ) / 3 = 1 / 3 from rfl, g_mid, g_hyp]
  norm_num

/-! ### The limiting shapes of Corollary 2

Squared sides `(1, 1, c)`: `c → 4` is the flat isosceles triangle (apex angle `→ π`), `c → 0` the
needle. Squared sides `(1, c, 1 + c)` with `c → 0` is the thin right triangle. On each range the
formula is an explicit rational function of `c`, and the limits follow by continuity. -/

lemma g_one_large {c : ℝ} (hc : 2 ≤ c) : gfun 1 c = 2 / (3 * c) := by
  rw [g_closed one_pos (by linarith), Phi_of_one_le (by linarith : (1 : ℝ) ≤ 1 + c),
    show 1 - c = -(c - 1) by ring, Phi_even, Phi_of_one_le (by linarith : (1 : ℝ) ≤ c - 1)]
  field_simp; ring

/-- Flat isosceles triangles: `p → 25/72`. -/
theorem p_flat_isosceles :
    Filter.Tendsto (fun c => ptri 1 1 c) (nhds 4) (nhds (25 / 72)) := by
  have heq : ∀ᶠ c in nhds (4 : ℝ), (c + 2 / (3 * c)) / (2 * (2 + c)) = ptri 1 1 c := by
    filter_upwards [Ioi_mem_nhds (show (2 : ℝ) < 4 by norm_num)] with c hc
    have hc' : (2 : ℝ) ≤ c := le_of_lt hc
    have hpos : 0 < c := by linarith
    simp only [ptri, div_one]
    rw [g_one_large hc', g_small (by positivity) (by positivity)
      (by rw [← add_div, div_le_one hpos]; linarith)]
    field_simp; ring
  refine Filter.Tendsto.congr' heq ?_
  have : ContinuousAt (fun c : ℝ => (c + 2 / (3 * c)) / (2 * (2 + c))) 4 := by
    fun_prop (disch := norm_num)
  convert this.tendsto using 2
  norm_num

lemma g_one_small {c : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) : gfun 1 c = 2 / 3 - c ^ 2 / 6 + c ^ 3 / 24 := by
  rw [g_closed one_pos h0, Phi_of_one_le (by linarith : (1 : ℝ) ≤ 1 + c),
    Phi_of_mem (by linarith) (by linarith)]
  field_simp; ring

/-- Needle-shaped isosceles triangles: `p → 1/3`. -/
theorem p_needle :
    Filter.Tendsto (fun c => ptri 1 1 c) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 3)) := by
  have heq : ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (2 * (2 / 3 - c ^ 2 / 6 + c ^ 3 / 24) + (2 * c ^ 2 / 3 - c ^ 3 / 8)) / (2 * (2 + c))
        = ptri 1 1 c := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with c hc
    obtain ⟨h0, h1⟩ := hc
    simp only [ptri, div_one]
    rw [g_one_small h0 h1.le, g_closed (by positivity) (by positivity), sub_self,
      show Phi 0 = 0 by simp [Phi], Phi_of_one_le (by
        rw [← add_div, le_div_iff₀ h0]; linarith)]
    field_simp; ring
  refine Filter.Tendsto.congr' heq (tendsto_nhdsWithin_of_tendsto_nhds ?_)
  have : Continuous (fun c : ℝ => 2 * (2 / 3 - c ^ 2 / 6 + c ^ 3 / 24) + (2 * c ^ 2 / 3 - c ^ 3 / 8)) := by
    fun_prop
  have h := (this.tendsto 0).div ((by fun_prop : Continuous fun c : ℝ => 2 * (2 + c)).tendsto 0)
    (by norm_num)
  convert h using 2
  norm_num

/-- Thin right triangles (squared sides `1, c, 1 + c`): `p → 1/3`. -/
theorem p_thin_right :
    Filter.Tendsto (fun c => ptri 1 c (1 + c)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 3)) := by
  have heq : ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (2 / (3 * (1 + c)) + 2 * c ^ 2 / (3 * (1 + c)) + (1 + c) * (1 - (1 + c ^ 2) / (3 * (1 + c) ^ 2)))
        / (2 * (2 + 2 * c)) = ptri 1 c (1 + c) := by
    filter_upwards [self_mem_nhdsWithin] with c (h0 : 0 < c)
    simp only [ptri, div_one]
    have hA : gfun c (1 + c) = 2 / (3 * (1 + c)) := by
      rw [g_closed h0 (by positivity), Phi_of_one_le (by linarith : (1 : ℝ) ≤ c + (1 + c)),
        show c - (1 + c) = -1 by ring, Phi_even, Phi_of_mem zero_le_one le_rfl]
      field_simp; ring
    have hB : gfun (1 / c) ((1 + c) / c) = 2 * c / (3 * (1 + c)) := by
      rw [g_closed (by positivity) (by positivity), Phi_of_one_le (by
          rw [← add_div, le_div_iff₀ h0]; linarith),
        show 1 / c - (1 + c) / c = -1 by field_simp; ring, Phi_even,
        Phi_of_mem zero_le_one le_rfl]
      field_simp; ring
    have hC : gfun (1 / (1 + c)) (c / (1 + c)) = 1 - (1 + c ^ 2) / (3 * (1 + c) ^ 2) := by
      rw [g_small (by positivity) (by positivity) (by rw [← add_div, div_le_one (by positivity)])]
      field_simp
    rw [hA, hB, hC]
    field_simp; ring
  refine Filter.Tendsto.congr' heq (tendsto_nhdsWithin_of_tendsto_nhds ?_)
  have hc : ContinuousAt (fun c : ℝ => (2 / (3 * (1 + c)) + 2 * c ^ 2 / (3 * (1 + c)) +
      (1 + c) * (1 - (1 + c ^ 2) / (3 * (1 + c) ^ 2))) / (2 * (2 + 2 * c))) 0 := by
    fun_prop (disch := norm_num)
  convert hc.tendsto using 2
  norm_num

end Enclosing
