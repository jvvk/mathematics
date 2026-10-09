import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Unit hexagons: a triangle with two unit sides (Lemma 3.1)

Put `L = (-a, 0)`, `R = (a, 0)`, `Z = (0, h)` with `0 < a < 1`, `h > 0`, `a² + h² = 1`, and let
`T = conv(L, Z, R)`. A point `(x, y)` lies in `T` exactly when `0 ≤ y` and `h |x| ≤ a (h - y)`.

Metric facts:
* each closed half (`x ≤ 0` or `x ≥ 0`) has the unique unit pair `{L, Z}` (resp. `{R, Z}`);
* a median point `(0, y)` with `y < h` is strictly within distance one of every point of `T`;
* the only points of `T` at distance one from `Z` are `L` and `R`;
* hence two points of `T` other than `Z` at unit distance lie in opposite strict halves;
* at a vertex other than `Z` the two neighbours are within distance one, so the smaller angle is at most `π/3`.

Combinatorial core: along a path whose vertices alternate between the strict halves and whose turn signs
alternate, the statement "convex ↔ left" never changes. This rules out a closed polygon with a convex
leftmost and a convex rightmost vertex, and a path from `L` to `R` with both ends convex.
-/

open Real

namespace UnitHexagon

/-- Membership in the triangle `T`. -/
def InT (a h x y : ℝ) : Prop := 0 ≤ y ∧ h * |x| ≤ a * (h - y)

section metric
variable {a h : ℝ} (ha : 0 < a) (ha1 : a < 1) (hh : 0 < h) (hah : a ^ 2 + h ^ 2 = 1)
include ha ha1 hh hah

omit ha1 hah in
lemma InT.bounds {x y : ℝ} (hT : InT a h x y) : |x| ≤ a ∧ y ≤ h := by
  obtain ⟨hy, hx⟩ := hT
  have h0 : 0 ≤ h * |x| := mul_nonneg hh.le (abs_nonneg x)
  have hyh : y ≤ h := by nlinarith
  refine ⟨?_, hyh⟩
  by_contra hc; push Not at hc
  nlinarith

/-- In the closed left half the only unit pair is `{L, Z}`. -/
lemma left_half_unit_pair {x₁ y₁ x₂ y₂ : ℝ} (h₁ : InT a h x₁ y₁) (h₂ : InT a h x₂ y₂)
    (hx₁ : x₁ ≤ 0) (hx₂ : x₂ ≤ 0) (hd : (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 = 1) :
    (x₁ = -a ∧ y₁ = 0 ∧ x₂ = 0 ∧ y₂ = h) ∨ (x₁ = 0 ∧ y₁ = h ∧ x₂ = -a ∧ y₂ = 0) := by
  obtain ⟨b₁, c₁⟩ := InT.bounds ha hh h₁
  obtain ⟨b₂, c₂⟩ := InT.bounds ha hh h₂
  rw [abs_of_nonpos hx₁] at b₁; rw [abs_of_nonpos hx₂] at b₂
  have hy₁ := h₁.1; have hy₂ := h₂.1
  have e1 : (x₁ - x₂) ^ 2 ≤ a ^ 2 := by nlinarith
  have e2 : (y₁ - y₂) ^ 2 ≤ h ^ 2 := by nlinarith
  have f1 : (x₁ - x₂) ^ 2 = a ^ 2 := by nlinarith
  have f2 : (y₁ - y₂) ^ 2 = h ^ 2 := by nlinarith
  -- |x₁ - x₂| = a forces {x₁, x₂} = {-a, 0}; |y₁ - y₂| = h forces {y₁, y₂} = {0, h}
  have g1 : (x₁ = -a ∧ x₂ = 0) ∨ (x₁ = 0 ∧ x₂ = -a) := by
    rcases le_total x₁ x₂ with hle | hle
    · left; constructor <;> nlinarith
    · right; constructor <;> nlinarith
  have g2 : (y₁ = 0 ∧ y₂ = h) ∨ (y₁ = h ∧ y₂ = 0) := by
    rcases le_total y₁ y₂ with hle | hle
    · left; constructor <;> nlinarith
    · right; constructor <;> nlinarith
  -- the point with x = -a has y = 0
  have hL : ∀ y, InT a h (-a) y → y = 0 := by
    intro y hT
    obtain ⟨hy, hx⟩ := hT
    rw [abs_neg, abs_of_pos ha] at hx
    nlinarith
  rcases g1 with ⟨e, e'⟩ | ⟨e, e'⟩
  · subst e e'
    have := hL y₁ h₁
    rcases g2 with ⟨_, h'⟩ | ⟨h', _⟩
    · left; exact ⟨rfl, this, rfl, h'⟩
    · exfalso; rw [this] at h'; linarith
  · subst e e'
    have := hL y₂ h₂
    rcases g2 with ⟨_, h'⟩ | ⟨h', _⟩
    · exfalso; rw [this] at h'; linarith
    · right; exact ⟨rfl, h', rfl, this⟩

/-- Two points in the same closed half are within distance one. -/
lemma same_half_le_one {x₁ y₁ x₂ y₂ : ℝ} (h₁ : InT a h x₁ y₁) (h₂ : InT a h x₂ y₂)
    (hs : 0 ≤ x₁ * x₂) : (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 ≤ 1 := by
  obtain ⟨b₁, c₁⟩ := InT.bounds ha hh h₁
  obtain ⟨b₂, c₂⟩ := InT.bounds ha hh h₂
  have hy₁ := h₁.1; have hy₂ := h₂.1
  have e1 : (x₁ - x₂) ^ 2 ≤ a ^ 2 := by
    rcases le_total 0 x₁ with p | p
    · rcases le_total 0 x₂ with q | q
      · rw [abs_of_nonneg p] at b₁; rw [abs_of_nonneg q] at b₂; nlinarith
      · have : x₂ = 0 ∨ x₁ = 0 := by
          rcases eq_or_lt_of_le p with p' | p'
          · right; linarith
          · left; nlinarith
        rcases this with r | r <;> rw [r] at * <;> simp_all <;> nlinarith [abs_le.1 b₁, abs_le.1 b₂]
    · rcases le_total 0 x₂ with q | q
      · have : x₂ = 0 ∨ x₁ = 0 := by
          rcases eq_or_lt_of_le q with q' | q'
          · left; linarith
          · right; nlinarith
        rcases this with r | r <;> rw [r] at * <;> simp_all <;> nlinarith [abs_le.1 b₁, abs_le.1 b₂]
      · rw [abs_of_nonpos p] at b₁; rw [abs_of_nonpos q] at b₂; nlinarith
  have e2 : (y₁ - y₂) ^ 2 ≤ h ^ 2 := by nlinarith
  nlinarith

omit ha1 in
/-- A median point `(0, y)` with `0 ≤ y < h` is strictly within unit distance of every point of `T`. -/
lemma median_lt_one {y₀ x y : ℝ} (hy₀ : 0 ≤ y₀) (hy₀h : y₀ < h) (hT : InT a h x y) :
    x ^ 2 + (y - y₀) ^ 2 < 1 := by
  obtain ⟨hy, hx⟩ := hT
  have hyh : y ≤ h := (InT.bounds ha hh ⟨hy, hx⟩).2
  -- |x| ≤ a (h - y) / h, and the bound is a convex function of y maximised at the ends
  have hx2 : h ^ 2 * x ^ 2 ≤ a ^ 2 * (h - y) ^ 2 := by
    have := mul_le_mul hx hx (mul_nonneg hh.le (abs_nonneg x)) (by nlinarith)
    nlinarith [sq_abs x]
  have c0 : a ^ 2 + y₀ ^ 2 < 1 := by nlinarith
  have c1 : (h - y₀) ^ 2 < 1 := by nlinarith
  -- with s = y / h: h²·(value) ≤ (1-s)·h²(a² + y₀²) + s·h²(h - y₀)², up to a nonpositive term
  have key : h ^ 2 * (x ^ 2 + (y - y₀) ^ 2) ≤
      h * (h - y) * (a ^ 2 + y₀ ^ 2) + h * y * (h - y₀) ^ 2 := by
    nlinarith [mul_nonneg hy (sub_nonneg.2 hyh), hah]
  have : h * (h - y) * (a ^ 2 + y₀ ^ 2) + h * y * (h - y₀) ^ 2 < h ^ 2 := by
    rcases eq_or_lt_of_le hy with hy0 | hy0
    · rw [← hy0]; nlinarith
    · nlinarith [mul_pos hh hy0, mul_nonneg hh.le (sub_nonneg.2 hyh)]
  nlinarith

/-- The points of `T` at distance one from `Z = (0, h)` are `L` and `R`. -/
lemma unit_from_Z {x y : ℝ} (hT : InT a h x y) (hd : x ^ 2 + (y - h) ^ 2 = 1) :
    y = 0 ∧ (x = a ∨ x = -a) := by
  obtain ⟨hy, hx⟩ := hT
  have hyh : y ≤ h := (InT.bounds ha hh ⟨hy, hx⟩).2
  have hx2 : h ^ 2 * x ^ 2 ≤ a ^ 2 * (h - y) ^ 2 := by
    have := mul_le_mul hx hx (mul_nonneg hh.le (abs_nonneg x)) (by nlinarith)
    nlinarith [sq_abs x]
  have hy0 : y = 0 := by
    by_contra hne
    have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hne)
    nlinarith [mul_pos hyp hh, mul_pos (mul_pos hyp hh) hh]
  subst hy0
  refine ⟨rfl, ?_⟩
  have : x ^ 2 = a ^ 2 := by nlinarith
  exact sq_eq_sq_iff_eq_or_eq_neg.1 this

/-- Every point of `T` is within distance one of `Z`. -/
lemma Z_le_one {x y : ℝ} (hT : InT a h x y) : x ^ 2 + (y - h) ^ 2 ≤ 1 := by
  obtain ⟨hy, hx⟩ := hT
  have hyh : y ≤ h := (InT.bounds ha hh ⟨hy, hx⟩).2
  have hx2 : h ^ 2 * x ^ 2 ≤ a ^ 2 * (h - y) ^ 2 := by
    have := mul_le_mul hx hx (mul_nonneg hh.le (abs_nonneg x)) (by nlinarith)
    nlinarith [sq_abs x]
  have h3 : (h - y) ^ 2 ≤ h ^ 2 := by nlinarith
  have h4 : h ^ 2 * (x ^ 2 + (y - h) ^ 2) ≤ h ^ 2 * 1 := by nlinarith
  exact le_of_mul_le_mul_left h4 (by positivity)

/-- Two points of `T`, neither equal to `Z`, at unit distance lie in opposite strict halves. -/
theorem unit_pair_opposite {x₁ y₁ x₂ y₂ : ℝ} (h₁ : InT a h x₁ y₁) (h₂ : InT a h x₂ y₂)
    (hz₁ : ¬ (x₁ = 0 ∧ y₁ = h)) (hz₂ : ¬ (x₂ = 0 ∧ y₂ = h))
    (hd : (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 = 1) : x₁ * x₂ < 0 := by
  -- median points other than Z have no unit neighbour
  have med : ∀ {u v p q : ℝ}, InT a h u v → InT a h p q → ¬ (u = 0 ∧ v = h) → u = 0 →
      (u - p) ^ 2 + (v - q) ^ 2 ≠ 1 := by
    intro u v p q hu hp hz hu0 heq
    have hv := hu.1
    have hvh : v < h := lt_of_le_of_ne (InT.bounds ha hh hu).2 (fun e => hz ⟨hu0, e⟩)
    have := median_lt_one ha hh hah hv hvh hp
    rw [hu0] at heq; nlinarith
  by_contra hc; push Not at hc
  rcases eq_or_ne x₁ 0 with e₁ | e₁
  · exact med h₁ h₂ hz₁ e₁ hd
  rcases eq_or_ne x₂ 0 with e₂ | e₂
  · exact med h₂ h₁ hz₂ e₂ (by linarith [hd])
  -- same strict half: the unique unit pair contains Z
  rcases lt_or_gt_of_ne e₁ with p | p
  · have q : x₂ < 0 := by
      by_contra q'; push Not at q'
      have := lt_of_le_of_ne q' (Ne.symm e₂); nlinarith
    rcases left_half_unit_pair ha ha1 hh hah h₁ h₂ p.le q.le hd with ⟨_, _, h0, h'⟩ | ⟨h0, h', _, _⟩
    · exact hz₂ ⟨h0, h'⟩
    · exact hz₁ ⟨h0, h'⟩
  · have q : 0 < x₂ := by
      by_contra q'; push Not at q'
      have := lt_of_le_of_ne q' e₂; nlinarith
    -- reflect x ↦ -x
    have r₁ : InT a h (-x₁) y₁ := ⟨h₁.1, by rw [abs_neg]; exact h₁.2⟩
    have r₂ : InT a h (-x₂) y₂ := ⟨h₂.1, by rw [abs_neg]; exact h₂.2⟩
    rcases left_half_unit_pair ha ha1 hh hah r₁ r₂ (by linarith) (by linarith) (by nlinarith [hd])
      with ⟨_, _, h0, h'⟩ | ⟨h0, h', _, _⟩
    · exact hz₂ ⟨by linarith, h'⟩
    · exact hz₁ ⟨by linarith, h'⟩

/-- At a vertex `V ≠ Z` with unit edges to neighbours `U, W` in `T`, the neighbours are within
distance one. -/
theorem neighbours_close {xv yv xu yu xw yw : ℝ} (hV : InT a h xv yv) (hU : InT a h xu yu)
    (hW : InT a h xw yw) (hzv : ¬ (xv = 0 ∧ yv = h))
    (hvu : (xv - xu) ^ 2 + (yv - yu) ^ 2 = 1) (hvw : (xv - xw) ^ 2 + (yv - yw) ^ 2 = 1) :
    (xu - xw) ^ 2 + (yu - yw) ^ 2 ≤ 1 := by
  by_cases hzu : xu = 0 ∧ yu = h
  · obtain ⟨e1, e2⟩ := hzu; subst e1 e2
    have := Z_le_one ha ha1 hh hah hW; nlinarith
  by_cases hzw : xw = 0 ∧ yw = h
  · obtain ⟨e1, e2⟩ := hzw; subst e1 e2
    have := Z_le_one ha ha1 hh hah hU; nlinarith
  have o1 := unit_pair_opposite ha ha1 hh hah hV hU hzv hzu hvu
  have o2 := unit_pair_opposite ha ha1 hh hah hV hW hzv hzw hvw
  apply same_half_le_one ha ha1 hh hah hU hW
  have : 0 < (xv * xu) * (xv * xw) := mul_pos_of_neg_of_neg o1 o2
  nlinarith [sq_nonneg xv]

end metric

/-- The cosine rule: unit neighbours within distance one give a smaller angle at most `π/3`. -/
lemma angle_le_pi_div_three {θ : ℝ} (hπ : θ ≤ π) (hd : 2 - 2 * Real.cos θ ≤ 1) :
    θ ≤ π / 3 := by
  have hc : Real.cos (π / 3) ≤ Real.cos θ := by rw [Real.cos_pi_div_three]; linarith
  by_contra hc'; push Not at hc'
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) hπ hc'
  linarith

/-! ## The combinatorial core -/

/-- Along a path whose labels (`left`) and turn signs (`convex`) both alternate, the statement
"convex ↔ left" is invariant. -/
theorem invariant_along_path (left convex : ℕ → Prop) (k : ℕ)
    (hl : ∀ i < k, (left (i + 1) ↔ ¬ left i)) (hc : ∀ i < k, (convex (i + 1) ↔ ¬ convex i)) :
    ∀ i ≤ k, ((convex i ↔ left i) ↔ (convex 0 ↔ left 0)) := by
  intro i hi
  induction i with
  | zero => exact Iff.rfl
  | succ j ih =>
    rw [← ih (by omega), hl j (by omega), hc j (by omega)]
    tauto

/-- No closed polygon avoiding `Z`: a convex vertex in the left half and a convex vertex in the right
half would make the invariant both true and false. -/
theorem no_polygon_avoiding_apex (left convex : ℕ → Prop) (k : ℕ)
    (hl : ∀ i < k, (left (i + 1) ↔ ¬ left i)) (hc : ∀ i < k, (convex (i + 1) ↔ ¬ convex i))
    {i j : ℕ} (hi : i ≤ k) (hj : j ≤ k) (ci : convex i) (li : left i) (cj : convex j)
    (lj : ¬ left j) : False := by
  have a := invariant_along_path left convex k hl hc i hi
  have b := invariant_along_path left convex k hl hc j hj
  have : (convex i ↔ left i) ↔ (convex j ↔ left j) := a.trans b.symm
  tauto

/-- No path from `L` to `R` with both ends convex: the same invariant at its two ends. -/
theorem no_path_through_apex (left convex : ℕ → Prop) (k : ℕ)
    (hl : ∀ i < k, (left (i + 1) ↔ ¬ left i)) (hc : ∀ i < k, (convex (i + 1) ↔ ¬ convex i))
    (c0 : convex 0) (l0 : left 0) (ck : convex k) (lk : ¬ left k) : False :=
  no_polygon_avoiding_apex left convex k hl hc (le_refl 0 |>.trans (Nat.zero_le k)) le_rfl c0 l0 ck lk

end UnitHexagon
