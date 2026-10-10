import Mathlib

/-!
# A random circle and the centroid (MSE 5101873)

The angular calculus behind the note. A convex body `K` with a marked interior point at the origin gives the
angular density `ρ θ = r(θ)² / (2|K|)` of a uniform point (polar coordinates; `r` is the radial function). The
probability that the circle on a random diameter `XY` contains the origin is `P = ∫ ρ(θ) a(θ) dθ`, where `a θ` is
the mass of the half-turn of directions facing away from `θ` (Euclid III.31). Everything below is about such
densities: continuous, `2π`-periodic, total mass `1`.

The geometric inputs are hypotheses, quoted in the paper:
* Grünbaum: every half-plane through the centroid holds at most `5/9` of the area, i.e. `∫ θ..θ+π, ρ ≤ 5/9`;
* Minkowski–Radon: the centroid divides each chord in ratio at most `2 : 1`, i.e. `ρ θ ≤ 4 ρ (θ + π)`;
* Stewart (Pacific J. Math. 8 (1958) 335–337): `|K ∩ (2G - K)| ≥ (2/3)|K|`, i.e. `2/3 ≤ s ρ`;
* six crossings: the sign of `ρ θ - ρ (θ + π)` changes only at three lines `t₀, t₁, t₂`.
-/

namespace CentroidCircle

open intervalIntegral Real MeasureTheory

/-- A continuous `2π`-periodic angular density of total mass `1`. -/
structure Dens (ρ : ℝ → ℝ) : Prop where
  cont : Continuous ρ
  per : Function.Periodic ρ (2 * π)
  mass : ∫ x in (0 : ℝ)..2 * π, ρ x = 1

variable {ρ : ℝ → ℝ}

/-- Mass of the directions making an obtuse angle with `θ`. -/
noncomputable def a (ρ : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ x in θ + π / 2..θ + 3 * π / 2, ρ x

/-- Imbalance of the half-plane bounded by the line through the origin perpendicular to `θ`. -/
noncomputable def b (ρ : ℝ → ℝ) (θ : ℝ) : ℝ := a ρ θ - 1 / 2

/-- The probability that the random circle contains the origin. -/
noncomputable def P (ρ : ℝ → ℝ) : ℝ := ∫ θ in (0 : ℝ)..2 * π, ρ θ * a ρ θ

/-- Odd part of the density. -/
noncomputable def ρo (ρ : ℝ → ℝ) (θ : ℝ) : ℝ := (ρ θ - ρ (θ + π)) / 2

/-- Mass of the central symmetral `K ∩ (-K)`, as a fraction of `|K|`. -/
noncomputable def s (ρ : ℝ → ℝ) : ℝ := ∫ θ in (0 : ℝ)..2 * π, min (ρ θ) (ρ (θ + π))

/-- The derivative of `b` (Lemma `hasDerivAt_b`). -/
noncomputable def db (ρ : ℝ → ℝ) (θ : ℝ) : ℝ := ρ (θ + 3 * π / 2) - ρ (θ + π / 2)

lemma cont_shift {g : ℝ → ℝ} (hg : Continuous g) (c : ℝ) : Continuous fun θ => g (θ + c) :=
  hg.comp (continuous_id.add continuous_const)

section basic

variable (hρ : Dens ρ)
include hρ

lemma ii (x y : ℝ) : IntervalIntegrable ρ volume x y := hρ.cont.intervalIntegrable x y

lemma period_mass (t : ℝ) : ∫ x in t..t + 2 * π, ρ x = 1 := by
  rw [hρ.per.intervalIntegral_add_eq t 0, zero_add, hρ.mass]

omit hρ in
lemma shift_mass (x y c : ℝ) (hc : Function.Periodic ρ c) :
    ∫ u in x + c..y + c, ρ u = ∫ u in x..y, ρ u := by
  rw [← intervalIntegral.integral_comp_add_right]
  exact intervalIntegral.integral_congr fun u _ => hc u

lemma mass_shift_pi : ∫ θ in (0 : ℝ)..2 * π, ρ (θ + π) = 1 := by
  rw [intervalIntegral.integral_comp_add_right]
  have := period_mass hρ π
  rwa [show 2 * π + π = π + 2 * π by ring, show (0 : ℝ) + π = π by ring]

omit hρ in
/-- Splitting a period into two half-turns. -/
lemma halfsplit (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ θ in (0 : ℝ)..2 * π, g θ = ∫ θ in (0 : ℝ)..π, (g θ + g (θ + π)) := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hg.intervalIntegrable 0 π)
    (hg.intervalIntegrable π (2 * π))
  have h2 : ∫ θ in (0 : ℝ)..π, g (θ + π) = ∫ θ in π..2 * π, g θ := by
    rw [intervalIntegral.integral_comp_add_right]; congr 1 <;> ring
  have hi : IntervalIntegrable (fun θ => g (θ + π)) volume 0 π := (cont_shift hg π).intervalIntegrable 0 π
  rw [intervalIntegral.integral_add (hg.intervalIntegrable _ _) hi, h2, h1]

lemma a_add_pi (θ : ℝ) : a ρ (θ + π) = 1 - a ρ θ := by
  unfold a
  have h := intervalIntegral.integral_add_adjacent_intervals (ii hρ (θ + π / 2) (θ + 3 * π / 2))
    (ii hρ (θ + 3 * π / 2) (θ + π / 2 + 2 * π))
  rw [period_mass hρ] at h
  rw [show θ + π + π / 2 = θ + 3 * π / 2 by ring, show θ + π + 3 * π / 2 = θ + π / 2 + 2 * π by ring]
  linarith

lemma b_add_pi (θ : ℝ) : b ρ (θ + π) = - b ρ θ := by
  unfold b; rw [a_add_pi hρ]; ring

lemma ρo_add_pi (θ : ℝ) : ρo ρ (θ + π) = - ρo ρ θ := by
  unfold ρo
  rw [show θ + π + π = θ + 2 * π by ring, hρ.per θ]; ring

lemma a_eq (θ : ℝ) : a ρ θ = (∫ x in (0 : ℝ)..θ + 3 * π / 2, ρ x) - ∫ x in (0 : ℝ)..θ + π / 2, ρ x := by
  unfold a
  rw [intervalIntegral.integral_interval_sub_left (ii hρ _ _) (ii hρ _ _)]

lemma hasDerivAt_a (θ : ℝ) : HasDerivAt (a ρ) (db ρ θ) θ := by
  have F := fun c : ℝ => ((hρ.cont.integral_hasStrictDerivAt 0 (θ + c)).hasDerivAt).comp θ
    ((hasDerivAt_id θ).add_const c)
  have h := (F (3 * π / 2)).sub (F (π / 2))
  simp only [mul_one, id] at h
  have e : (a ρ) = fun t => (∫ x in (0 : ℝ)..t + 3 * π / 2, ρ x) - ∫ x in (0 : ℝ)..t + π / 2, ρ x :=
    funext (a_eq hρ)
  rw [e]; exact h

lemma continuous_a : Continuous (a ρ) :=
  continuous_iff_continuousAt.2 fun θ => (hasDerivAt_a hρ θ).continuousAt

lemma hasDerivAt_b (θ : ℝ) : HasDerivAt (b ρ) (db ρ θ) θ := (hasDerivAt_a hρ θ).sub_const _

lemma continuous_b : Continuous (b ρ) := (continuous_a hρ).sub continuous_const

lemma continuous_ρo : Continuous (ρo ρ) :=
  ((hρ.cont.sub (hρ.cont.comp (continuous_id.add continuous_const))).div_const 2)

end basic

/-! ## The key identity: `P - 1/2 = ∫ ρo · b` (Proposition 1) -/

theorem key (hρ : Dens ρ) : P ρ - 1 / 2 = ∫ θ in (0 : ℝ)..2 * π, ρo ρ θ * b ρ θ := by
  have ca := continuous_a hρ
  have cb := continuous_b hρ
  have co := continuous_ρo hρ
  have cρπ : Continuous fun θ => ρ (θ + π) := hρ.cont.comp (continuous_id.add continuous_const)
  unfold P
  rw [halfsplit (fun θ => ρ θ * a ρ θ) (hρ.cont.mul ca),
    halfsplit (fun θ => ρo ρ θ * b ρ θ) (co.mul cb)]
  have h1 : ∫ θ in (0 : ℝ)..π, (ρ θ * a ρ θ + ρ (θ + π) * a ρ (θ + π)) =
      ∫ θ in (0 : ℝ)..π, ((ρ θ + ρ (θ + π)) / 2 + (ρo ρ θ * b ρ θ + ρo ρ (θ + π) * b ρ (θ + π))) := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [a_add_pi hρ, b_add_pi hρ, ρo_add_pi hρ]; simp only [b, ρo]; ring
  have hf1 : IntervalIntegrable (fun θ => (ρ θ + ρ (θ + π)) / 2) volume 0 π :=
    ((hρ.cont.add cρπ).div_const 2).intervalIntegrable 0 π
  have hf2 : IntervalIntegrable (fun θ => ρo ρ θ * b ρ θ + ρo ρ (θ + π) * b ρ (θ + π)) volume 0 π :=
    ((co.mul cb).add ((cont_shift co π).mul (cont_shift cb π))).intervalIntegrable 0 π
  rw [h1, intervalIntegral.integral_add hf1 hf2]
  have h2 : ∫ θ in (0 : ℝ)..π, (ρ θ + ρ (θ + π)) / 2 = 1 / 2 := by
    rw [intervalIntegral.integral_div, ← halfsplit _ hρ.cont, hρ.mass]
  rw [h2]; ring

/-- Centrally symmetric bodies give exactly `1/2`. -/
theorem symmetric_half (hρ : Dens ρ) (hs : ∀ θ, ρ (θ + π) = ρ θ) : P ρ = 1 / 2 := by
  have := key hρ
  have h0 : ∫ θ in (0 : ℝ)..2 * π, ρo ρ θ * b ρ θ = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun θ _ => by simp [ρo, hs θ]]
    simp
  linarith

/-- The signed-area form: `P - 1/2 = ½ ∫ b(θ) · (b(· + π/2))'(θ)`, the area swept by `(b θ, b (θ + π/2))`. -/
theorem signed_area (hρ : Dens ρ) :
    (∀ θ, HasDerivAt (fun t => b ρ (t + π / 2)) (db ρ (θ + π / 2)) θ) ∧
    P ρ - 1 / 2 = (1 / 2) * ∫ θ in (0 : ℝ)..2 * π, b ρ θ * db ρ (θ + π / 2) := by
  refine ⟨fun θ => by
    have h := (hasDerivAt_b hρ (θ + π / 2)).comp θ ((hasDerivAt_id θ).add_const (π / 2))
    simpa [Function.comp_def] using h, ?_⟩
  rw [key hρ, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [db, ρo]
  rw [show θ + π / 2 + 3 * π / 2 = θ + 2 * π by ring, hρ.per θ,
    show θ + π / 2 + π / 2 = θ + π by ring]
  ring

/-! ## The product bound (Proposition 2) -/

lemma abs_ρo_eq (θ : ℝ) : |ρo ρ θ| = (ρ θ + ρ (θ + π)) / 2 - min (ρ θ) (ρ (θ + π)) := by
  unfold ρo
  rcases le_total (ρ θ) (ρ (θ + π)) with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

theorem integral_abs_ρo (hρ : Dens ρ) : ∫ θ in (0 : ℝ)..2 * π, |ρo ρ θ| = 1 - s ρ := by
  have cρπ := cont_shift hρ.cont π
  have hf : IntervalIntegrable (fun x => (ρ x + ρ (x + π)) / 2) volume 0 (2 * π) :=
    ((hρ.cont.add cρπ).div_const 2).intervalIntegrable _ _
  have hg : IntervalIntegrable (fun x => min (ρ x) (ρ (x + π))) volume 0 (2 * π) :=
    (hρ.cont.min cρπ).intervalIntegrable _ _
  have hp : IntervalIntegrable (fun x => ρ (x + π)) volume 0 (2 * π) := cρπ.intervalIntegrable _ _
  rw [intervalIntegral.integral_congr fun θ _ => abs_ρo_eq θ, intervalIntegral.integral_sub hf hg,
    intervalIntegral.integral_div, intervalIntegral.integral_add (hρ.cont.intervalIntegrable _ _) hp,
    hρ.mass, mass_shift_pi hρ, s]
  ring

/-- `|P - 1/2| ≤ G (1 - s)` whenever every half-plane imbalance is at most `G`. -/
theorem product_bound (hρ : Dens ρ) (G : ℝ) (hb : ∀ θ, |b ρ θ| ≤ G) :
    |P ρ - 1 / 2| ≤ G * (1 - s ρ) := by
  have co := continuous_ρo hρ
  rw [key hρ, ← integral_abs_ρo hρ, ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.abs_integral_le_integral_abs (by positivity)).trans
    (intervalIntegral.integral_mono_on (by positivity) ((co.mul (continuous_b hρ)).abs.intervalIntegrable _ _)
      ((continuous_const.mul co.abs).intervalIntegrable _ _) fun θ _ => ?_)
  rw [abs_mul, mul_comm G]
  exact mul_le_mul_of_nonneg_left (hb θ) (abs_nonneg _)

/-! ## Grünbaum and Minkowski–Radon as hypotheses -/

/-- Grünbaum's inequality, in angular form. -/
def Grunbaum (ρ : ℝ → ℝ) : Prop := ∀ θ, ∫ x in θ..θ + π, ρ x ≤ 5 / 9

lemma abs_b_le (hρ : Dens ρ) (hG : Grunbaum ρ) (θ : ℝ) : |b ρ θ| ≤ 1 / 18 := by
  have h1 : a ρ θ ≤ 5 / 9 := by
    have := hG (θ + π / 2); unfold a; rwa [show θ + π / 2 + π = θ + 3 * π / 2 by ring] at this
  have h2 : a ρ (θ + π) ≤ 5 / 9 := by
    have := hG (θ + π + π / 2); unfold a
    rwa [show θ + π + π / 2 + π = θ + π + 3 * π / 2 by ring] at this
  rw [a_add_pi hρ] at h2
  rw [abs_le]; unfold b; constructor <;> linarith

/-- Minkowski–Radon, in angular form (`r θ ≤ 2 r (θ + π)`). -/
def MinkRadon (ρ : ℝ → ℝ) : Prop := ∀ θ, ρ θ ≤ 4 * ρ (θ + π)

theorem one_sub_s_le (hρ : Dens ρ) (hM : MinkRadon ρ) : 1 - s ρ ≤ 3 / 5 := by
  have cρπ : Continuous fun θ => ρ (θ + π) := hρ.cont.comp (continuous_id.add continuous_const)
  rw [← integral_abs_ρo hρ]
  have hle : ∫ θ in (0 : ℝ)..2 * π, |ρo ρ θ| ≤ ∫ θ in (0 : ℝ)..2 * π, (3 / 10) * (ρ θ + ρ (θ + π)) := by
    refine intervalIntegral.integral_mono_on (by positivity) ((continuous_ρo hρ).abs.intervalIntegrable _ _)
      ((continuous_const.mul (hρ.cont.add cρπ)).intervalIntegrable _ _) fun θ _ => ?_
    have h1 := hM θ
    have h2 := hM (θ + π)
    rw [show θ + π + π = θ + 2 * π by ring, hρ.per θ] at h2
    unfold ρo; rw [abs_le]; constructor <;> nlinarith
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hρ.cont.intervalIntegrable _ _)
    (cρπ.intervalIntegrable _ _), hρ.mass, mass_shift_pi hρ] at hle
  linarith

/-- The weaker bound of Section 4 (Levi's `s ≥ 2/5` via Minkowski–Radon): `P ≤ 8/15`. -/
theorem P_le_8_15 (hρ : Dens ρ) (hG : Grunbaum ρ) (hM : MinkRadon ρ) : P ρ ≤ 8 / 15 := by
  have h := product_bound hρ (1 / 18) (abs_b_le hρ hG)
  have h2 := one_sub_s_le hρ hM
  rw [abs_le] at h; nlinarith [h.2]

/-! ## Three lines (Lemma 3) -/

/-- Three half-planes: the alternate sectors cut by three lines through the centroid hold at most `2/3`. -/
theorem three_sectors (hρ : Dens ρ) (hG : Grunbaum ρ) (t₀ t₁ t₂ : ℝ) :
    (∫ x in t₀..t₁, ρ x) + (∫ x in t₂..t₀ + π, ρ x) + (∫ x in t₁ + π..t₂ + π, ρ x) ≤ 2 / 3 := by
  have I := ii hρ
  have e1 := intervalIntegral.integral_add_adjacent_intervals (I t₀ t₁) (I t₁ t₂)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (I t₀ t₂) (I t₂ (t₀ + π))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (I t₂ (t₀ + π)) (I (t₀ + π) (t₁ + π))
  have e4 := intervalIntegral.integral_add_adjacent_intervals (I t₂ (t₁ + π)) (I (t₁ + π) (t₂ + π))
  have e5 := intervalIntegral.integral_add_adjacent_intervals (I (t₁ + π) (t₂ + π)) (I (t₂ + π) (t₀ + 2 * π))
  have e6 := intervalIntegral.integral_add_adjacent_intervals (I (t₁ + π) (t₀ + 2 * π))
    (I (t₀ + 2 * π) (t₁ + 2 * π))
  have e7 := intervalIntegral.integral_add_adjacent_intervals (I t₀ (t₀ + π)) (I (t₀ + π) (t₁ + π))
  have e8 := intervalIntegral.integral_add_adjacent_intervals (I t₀ (t₁ + π)) (I (t₁ + π) (t₀ + 2 * π))
  have sh := shift_mass t₀ t₁ (2 * π) hρ.per
  have full := period_mass hρ t₀
  have g1 := hG t₀
  have g2 := hG t₂
  have g3 := hG (t₁ + π)
  rw [show t₂ + π = t₂ + π from rfl] at g2
  rw [show t₁ + π + π = t₁ + 2 * π by ring] at g3
  linarith

/-- Lemma 3 with Proposition 2: if `ρ θ - ρ (θ + π)` changes sign only at `t₀ < t₁ < t₂ < t₀ + π`
(the boundaries of `K` and `-K` cross six times), the central symmetral holds at least `2/3`. -/
theorem s_ge_two_thirds (hρ : Dens ρ) (hG : Grunbaum ρ) (t₀ t₁ t₂ : ℝ)
    (h01 : t₀ ≤ t₁) (h12 : t₁ ≤ t₂) (h20 : t₂ ≤ t₀ + π)
    (hsgn : ∀ θ, (θ ∈ Set.Icc t₀ t₁ ∨ θ ∈ Set.Icc t₂ (t₀ + π) ∨ θ ∈ Set.Icc (t₁ + π) (t₂ + π)) →
      ρ (θ + π) ≤ ρ θ) :
    2 / 3 ≤ s ρ := by
  have I := ii hρ
  have co := continuous_ρo hρ
  have IO : ∀ x y, IntervalIntegrable (ρo ρ) volume x y := fun x y => co.intervalIntegrable x y
  have IA : ∀ x y, IntervalIntegrable (fun θ => |ρo ρ θ|) volume x y :=
    fun x y => co.abs.intervalIntegrable x y
  have cρπ : Continuous fun θ => ρ (θ + π) := hρ.cont.comp (continuous_id.add continuous_const)
  -- the odd part is ≥ 0 on the odd sectors and ≤ 0 on the even ones
  have pos : ∀ θ, (θ ∈ Set.Icc t₀ t₁ ∨ θ ∈ Set.Icc t₂ (t₀ + π) ∨ θ ∈ Set.Icc (t₁ + π) (t₂ + π)) →
      |ρo ρ θ| = ρo ρ θ := fun θ hθ => abs_of_nonneg (by unfold ρo; linarith [hsgn θ hθ])
  have neg : ∀ θ, (θ ∈ Set.Icc t₁ t₂ ∨ θ ∈ Set.Icc (t₀ + π) (t₁ + π) ∨
      θ ∈ Set.Icc (t₂ + π) (t₀ + 2 * π)) → |ρo ρ θ| = - ρo ρ θ := by
    intro θ hθ
    have : ρ θ ≤ ρ (θ + π) := by
      rcases hθ with h | h | h
      · have := hsgn (θ + π) (Or.inr (Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩))
        rwa [show θ + π + π = θ + 2 * π by ring, hρ.per θ] at this
      · have h' := hsgn (θ - π) (Or.inl ⟨by linarith [h.1], by linarith [h.2]⟩)
        rw [sub_add_cancel] at h'
        have hp : ρ (θ + π) = ρ (θ - π) := by
          rw [show θ + π = θ - π + 2 * π by ring]; exact hρ.per _
        linarith
      · have h' := hsgn (θ - π) (Or.inr (Or.inl ⟨by linarith [h.1], by linarith [h.2]⟩))
        rw [sub_add_cancel] at h'
        have hp : ρ (θ + π) = ρ (θ - π) := by
          rw [show θ + π = θ - π + 2 * π by ring]; exact hρ.per _
        linarith
    rw [abs_of_nonpos (by unfold ρo; linarith)]
  -- integrals of |ρo| over the six sectors
  have uI : ∀ x y : ℝ, x ≤ y → ∀ θ ∈ Set.uIcc x y, θ ∈ Set.Icc x y := fun x y h θ hθ => by
    rwa [Set.uIcc_of_le h] at hθ
  have s1 : ∫ θ in t₀..t₁, |ρo ρ θ| = ∫ θ in t₀..t₁, ρo ρ θ :=
    intervalIntegral.integral_congr fun θ hθ => pos θ (Or.inl (uI _ _ h01 θ hθ))
  have s3 : ∫ θ in t₂..t₀ + π, |ρo ρ θ| = ∫ θ in t₂..t₀ + π, ρo ρ θ :=
    intervalIntegral.integral_congr fun θ hθ => pos θ (Or.inr (Or.inl (uI _ _ h20 θ hθ)))
  have s5 : ∫ θ in t₁ + π..t₂ + π, |ρo ρ θ| = ∫ θ in t₁ + π..t₂ + π, ρo ρ θ :=
    intervalIntegral.integral_congr fun θ hθ =>
      pos θ (Or.inr (Or.inr (uI _ _ (by linarith) θ hθ)))
  have s2 : ∫ θ in t₁..t₂, |ρo ρ θ| = - ∫ θ in t₁..t₂, ρo ρ θ := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun θ hθ => neg θ (Or.inl (uI _ _ h12 θ hθ))
  have s4 : ∫ θ in t₀ + π..t₁ + π, |ρo ρ θ| = - ∫ θ in t₀ + π..t₁ + π, ρo ρ θ := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun θ hθ =>
      neg θ (Or.inr (Or.inl (uI _ _ (by linarith) θ hθ)))
  have s6 : ∫ θ in t₂ + π..t₀ + 2 * π, |ρo ρ θ| = - ∫ θ in t₂ + π..t₀ + 2 * π, ρo ρ θ := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun θ hθ =>
      neg θ (Or.inr (Or.inr (uI _ _ (by linarith) θ hθ)))
  -- |ρo| and ρo are 2π-periodic; total over a period
  have perA : Function.Periodic (fun θ => |ρo ρ θ|) (2 * π) := fun θ => by
    simp only [ρo]; rw [show θ + 2 * π + π = θ + π + 2 * π by ring, hρ.per, hρ.per]
  have totA : ∫ θ in t₀..t₀ + 2 * π, |ρo ρ θ| = 1 - s ρ := by
    rw [perA.intervalIntegral_add_eq t₀ 0, zero_add, integral_abs_ρo hρ]
  -- ρo over a sector is half of (mass of the sector) - (mass of its antipode)
  have oI : ∀ x y, ∫ θ in x..y, ρo ρ θ = ((∫ θ in x..y, ρ θ) - ∫ θ in x + π..y + π, ρ θ) / 2 := by
    intro x y
    simp only [ρo]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (I x y) (cρπ.intervalIntegrable _ _),
      intervalIntegral.integral_comp_add_right]
  -- six-sector decomposition of the period, for |ρo| and for ρ
  have a1 := intervalIntegral.integral_add_adjacent_intervals (IA t₀ t₁) (IA t₁ t₂)
  have a2 := intervalIntegral.integral_add_adjacent_intervals (IA t₀ t₂) (IA t₂ (t₀ + π))
  have a3 := intervalIntegral.integral_add_adjacent_intervals (IA t₀ (t₀ + π)) (IA (t₀ + π) (t₁ + π))
  have a4 := intervalIntegral.integral_add_adjacent_intervals (IA t₀ (t₁ + π)) (IA (t₁ + π) (t₂ + π))
  have a5 := intervalIntegral.integral_add_adjacent_intervals (IA t₀ (t₂ + π)) (IA (t₂ + π) (t₀ + 2 * π))
  have r1 := intervalIntegral.integral_add_adjacent_intervals (I t₀ t₁) (I t₁ t₂)
  have r2 := intervalIntegral.integral_add_adjacent_intervals (I t₀ t₂) (I t₂ (t₀ + π))
  have r3 := intervalIntegral.integral_add_adjacent_intervals (I t₀ (t₀ + π)) (I (t₀ + π) (t₁ + π))
  have r4 := intervalIntegral.integral_add_adjacent_intervals (I t₀ (t₁ + π)) (I (t₁ + π) (t₂ + π))
  have r5 := intervalIntegral.integral_add_adjacent_intervals (I t₀ (t₂ + π)) (I (t₂ + π) (t₀ + 2 * π))
  have full := period_mass hρ t₀
  have o1 := oI t₀ t₁
  have o3 := oI t₂ (t₀ + π)
  have o5 := oI (t₁ + π) (t₂ + π)
  have o2 := oI t₁ t₂
  have o4 := oI (t₀ + π) (t₁ + π)
  have o6 := oI (t₂ + π) (t₀ + 2 * π)
  have sh5 : ∫ θ in t₁ + π + π..t₂ + π + π, ρ θ = ∫ θ in t₁..t₂, ρ θ := by
    rw [show t₁ + π + π = t₁ + 2 * π by ring, show t₂ + π + π = t₂ + 2 * π by ring]
    exact shift_mass t₁ t₂ (2 * π) hρ.per
  have sh6 : ∫ θ in t₂ + π + π..t₀ + 2 * π + π, ρ θ = ∫ θ in t₂..t₀ + π, ρ θ := by
    rw [show t₂ + π + π = t₂ + 2 * π by ring, show t₀ + 2 * π + π = t₀ + π + 2 * π by ring]
    exact shift_mass t₂ (t₀ + π) (2 * π) hρ.per
  have sh4 : ∫ θ in t₀ + π + π..t₁ + π + π, ρ θ = ∫ θ in t₀..t₁, ρ θ := by
    rw [show t₀ + π + π = t₀ + 2 * π by ring, show t₁ + π + π = t₁ + 2 * π by ring]
    exact shift_mass t₀ t₁ (2 * π) hρ.per
  rw [sh5] at o5; rw [sh6] at o6; rw [sh4] at o4
  rw [show t₀ + π + π = t₀ + 2 * π by ring] at o3
  have T := three_sectors hρ hG t₀ t₁ t₂
  linarith

/-- Proposition 3 with the product bound: if the boundaries of `K` and `-K` cross six times, `P ≤ 14/27`
from Grünbaum's inequality alone. -/
theorem P_le_14_27_three_sided (hρ : Dens ρ) (hG : Grunbaum ρ) (t₀ t₁ t₂ : ℝ)
    (h01 : t₀ ≤ t₁) (h12 : t₁ ≤ t₂) (h20 : t₂ ≤ t₀ + π)
    (hsgn : ∀ θ, (θ ∈ Set.Icc t₀ t₁ ∨ θ ∈ Set.Icc t₂ (t₀ + π) ∨ θ ∈ Set.Icc (t₁ + π) (t₂ + π)) →
      ρ (θ + π) ≤ ρ θ) :
    P ρ ≤ 14 / 27 := by
  have h := product_bound hρ (1 / 18) (abs_b_le hρ hG)
  have h2 := s_ge_two_thirds hρ hG t₀ t₁ t₂ h01 h12 h20 hsgn
  rw [abs_le] at h; nlinarith [h.2]

/-- Stewart's inequality at the centroid, quoted: the central symmetral holds at least `2/3` of the area. -/
def Stewart (ρ : ℝ → ℝ) : Prop := 2 / 3 ≤ s ρ

/-- Theorem 1: for every planar convex region, `|P - 1/2| ≤ 1/54`, so `P ≤ 14/27`
(Grünbaum's and Stewart's inequalities in the product bound). -/
theorem abs_P_sub_half_le (hρ : Dens ρ) (hG : Grunbaum ρ) (hS : Stewart ρ) :
    |P ρ - 1 / 2| ≤ 1 / 54 := by
  have h := product_bound hρ (1 / 18) (abs_b_le hρ hG)
  unfold Stewart at hS
  calc |P ρ - 1 / 2| ≤ 1 / 18 * (1 - s ρ) := h
    _ ≤ 1 / 18 * (1 / 3) := by gcongr; linarith
    _ = 1 / 54 := by norm_num

theorem P_le_14_27 (hρ : Dens ρ) (hG : Grunbaum ρ) (hS : Stewart ρ) : P ρ ≤ 14 / 27 := by
  have h := abs_P_sub_half_le hρ hG hS
  rw [abs_le] at h; linarith [h.2]

/-- The hypotheses are satisfiable: the uniform density (a disc about its centre). -/
theorem uniform_dens : Dens (fun _ => 1 / (2 * π)) where
  cont := continuous_const
  per := fun _ => rfl
  mass := by simp; field_simp

end CentroidCircle
