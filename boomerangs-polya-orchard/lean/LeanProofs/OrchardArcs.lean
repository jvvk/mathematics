import Mathlib

/-!
# Boomerangs in Pólya's orchard (MO 224015)

Open discs of radius `r` sit at the nonzero lattice points; `B(r)` is the farthest distance from the origin reached by
a circular arc from the origin before it enters a disc. This file proves the inequalities behind
`4/r - 10 < B(r) ≤ 28/r²`.

Lower bound (the corridor arc, half-angle `t = tan(α/2)`, `a = (1-r)(1+t²)/(2t²)`, `a sin α = (1-r)/t`):
* `t0_root`, `t0_pos`, `t0_le`: the smaller root `t₀` of `K t² - 2A t + r(1-r)`.
* `lower_value`: `2(1-r)/t₀ - (1-r) > 4/r - 10` for `0 < r ≤ 1/3`.
* `rise_clear`, `corridor_clear`: points of the box `[0,1-r]²`, and points with `r ≤ x ≤ 1-r`, are at distance
  `≥ r` from every nonzero lattice point.
* `arc_in_corridor`: on the corridor arc, `r ≤ x ≤ 1-r` for heights in `[1-r, 2a sin α - (1-r)]`.

Upper bound:
* `corridor_lemma`: an arc piece turning through `[0, ε]` with `tan ε < 2r/m` that crosses a band `|τ - τ_k| ≤ r`
  of a lattice line (points spaced `m`) passes strictly within `r` of a lattice point.
* `farey_product`, `farey_angle`: consecutive primitive vectors of norms `x, y` with `x + y > Q` are at angle
  `< π/Q`.
* `minkowski_offset`: for `a ≥ 4/r³` the arc stays within `0.29 r` of its tangent over length `3/(2r)`.
* `eps_cos`, `eps_tan`, `eps_le`: the explicit `ε_m = 1.01 √(2(1/m + 2r)/a)` satisfies the corridor conditions.
* `middle_bound`, `small_bound`, `large_bound`: the three ranges of `a` give at most `28/r²`.
-/

namespace OrchardArcs

open Real

/-! ### Lower bound: algebra -/

/-- `A = (1-r)²`, `K = 1 - 3r + 3r²`, `c₀ = r(1-r)`. -/
noncomputable def A (r : ℝ) : ℝ := (1 - r) ^ 2
noncomputable def K (r : ℝ) : ℝ := 1 - 3 * r + 3 * r ^ 2
noncomputable def S (r : ℝ) : ℝ := Real.sqrt (A r ^ 2 - K r * (r * (1 - r)))

/-- The smaller root of `K t² - 2A t + r(1-r)`. -/
noncomputable def t0 (r : ℝ) : ℝ := r * (1 - r) / (A r + S r)

theorem disc_nonneg {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1 / 3) : 0 ≤ A r ^ 2 - K r * (r * (1 - r)) := by
  unfold A K; nlinarith [mul_pos h0 h0, mul_pos (mul_pos h0 h0) h0, sq_nonneg (r - 1 / 3), mul_pos h0 (by linarith : (0:ℝ) < 1 / 3 - r + 1)]

theorem A_pos {r : ℝ} (h1 : r ≤ 1 / 3) : 0 < A r := by unfold A; nlinarith

theorem S_sq {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1 / 3) : S r ^ 2 = A r ^ 2 - K r * (r * (1 - r)) := by
  unfold S; rw [sq_sqrt (disc_nonneg h0 h1)]

theorem t0_root {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1 / 3) :
    K r * t0 r ^ 2 - 2 * A r * t0 r + r * (1 - r) = 0 := by
  have hA := A_pos h1
  have hS : 0 ≤ S r := Real.sqrt_nonneg _
  have hden : A r + S r ≠ 0 := by positivity
  have hsq := S_sq h0 h1
  unfold t0
  field_simp
  linear_combination (r * (1 - r)) * hsq

theorem t0_pos {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1 / 3) : 0 < t0 r := by
  unfold t0; have := A_pos h1; have : 0 ≤ S r := Real.sqrt_nonneg _
  apply div_pos (by nlinarith) (by positivity)

theorem t0_le {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1 / 3) : t0 r ≤ 1 := by
  unfold t0
  have hA := A_pos h1
  have hS : 0 ≤ S r := Real.sqrt_nonneg _
  rw [div_le_one (by positivity)]
  unfold A at *; nlinarith

/-- `√(A² - X) ≥ A - X/(2A) - X²/(2A³)` for `0 ≤ X ≤ A²`. -/
theorem sqrt_lower {A X : ℝ} (hA : 0 < A) (hX : 0 ≤ X) (hXA : X ≤ A ^ 2) :
    A - X / (2 * A) - X ^ 2 / (2 * A ^ 3) ≤ Real.sqrt (A ^ 2 - X) := by
  set L := A - X / (2 * A) - X ^ 2 / (2 * A ^ 3)
  by_cases hL : L ≤ 0
  · exact hL.trans (Real.sqrt_nonneg _)
  · apply Real.le_sqrt_of_sq_le
    -- with y = X / A², (1 - y/2 - y²/2)² ≤ 1 - y on [0,1]
    set y := X / A ^ 2 with hy
    have hy0 : 0 ≤ y := by positivity
    have hy1 : y ≤ 1 := by rw [hy, div_le_one (by positivity)]; exact hXA
    have hLy : L = A * (1 - y / 2 - y ^ 2 / 2) := by
      rw [hy]; simp only [L]; field_simp
    have hXy : A ^ 2 - X = A ^ 2 * (1 - y) := by rw [hy]; field_simp
    rw [hLy, hXy, mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [mul_nonneg hy0 hy0, mul_nonneg (mul_nonneg hy0 hy0) (by linarith : 0 ≤ 1 - y),
      mul_nonneg (mul_nonneg hy0 hy0) hy0]

/-- **The corridor arc reaches beyond `4/r - 10`.** -/
theorem lower_value {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1 / 3) : 4 / r - 10 < 2 * (1 - r) / t0 r - (1 - r) := by
  have hA := A_pos h1
  have hS : 0 ≤ S r := Real.sqrt_nonneg _
  have hr1 : 0 < 1 - r := by linarith
  have ht : 2 * (1 - r) / t0 r = 2 * (A r + S r) / r := by
    unfold t0; field_simp
  rw [ht]
  set X := K r * (r * (1 - r)) with hXdef
  have hK0 : 0 < K r := by unfold K; nlinarith
  have hK1 : K r ≤ 1 := by unfold K; nlinarith
  have hX0 : 0 ≤ X := by positivity
  have hXA : X ≤ A r ^ 2 := by have := disc_nonneg h0 h1; linarith
  have hlow := sqrt_lower hA hX0 hXA
  have hSdef : S r = Real.sqrt (A r ^ 2 - X) := rfl
  rw [← hSdef] at hlow
  -- 2(A + S)/r ≥ 2(2A - X/(2A) - X²/(2A³))/r = 4A/r - K/(1-r) - K² r/(1-r)⁴
  have key : 4 / r - 10 + (1 - r) < 2 * (A r + (A r - X / (2 * A r) - X ^ 2 / (2 * A r ^ 3))) / r := by
    have e : 2 * (A r + (A r - X / (2 * A r) - X ^ 2 / (2 * A r ^ 3))) / r =
        4 * (1 - r) ^ 2 / r - K r / (1 - r) - K r ^ 2 * r / (1 - r) ^ 4 := by
      rw [hXdef]; unfold A; field_simp; ring
    rw [e]
    have h4 : (16 / 81 : ℝ) ≤ (1 - r) ^ 4 := by
      have : (2 / 3 : ℝ) ≤ 1 - r := by linarith
      calc (16 / 81 : ℝ) = (2 / 3) ^ 4 := by norm_num
        _ ≤ (1 - r) ^ 4 := by gcongr
    have hq : K r ^ 2 * r / (1 - r) ^ 4 ≤ 81 / 16 * r := by
      rw [div_le_iff₀ (by positivity)]
      have : K r ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this h0.le]
    have hk : K r / (1 - r) = 1 - 2 * r + r ^ 2 / (1 - r) := by unfold K; field_simp; ring
    have hr2 : r ^ 2 / (1 - r) ≤ r / 2 := by
      rw [div_le_iff₀ hr1]; nlinarith
    rw [hk]
    have : 4 * (1 - r) ^ 2 / r = 4 / r - 8 + 4 * r := by field_simp; ring
    rw [this]
    nlinarith
  have : 2 * (A r + (A r - X / (2 * A r) - X ^ 2 / (2 * A r ^ 3))) / r ≤ 2 * (A r + S r) / r := by
    apply div_le_div_of_nonneg_right _ h0.le; linarith
  linarith

/-! ### Lower bound: geometry -/

/-- In the box `[0, 1-r]²` (with `r ≤ 1/2`) every point is at distance `≥ r` from each nonzero lattice point. -/
theorem rise_clear {r x y : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 - r) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1 - r) (i j : ℤ) (hij : (i, j) ≠ (0, 0)) : r ^ 2 ≤ (x - i) ^ 2 + (y - j) ^ 2 := by
  have hi : i ≤ -1 ∨ i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
  have hj : j ≤ -1 ∨ j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
  have sq1 : ∀ u : ℝ, r ≤ |u| → r ^ 2 ≤ u ^ 2 := fun u h => by
    have := sq_le_sq' (by linarith [abs_nonneg u, neg_abs_le u]) (le_abs_self u |>.trans' (le_refl _))
    nlinarith [sq_abs u, abs_nonneg u]
  rcases hi with hi | rfl | rfl | hi
  · have : (i : ℝ) ≤ -1 := by exact_mod_cast hi
    nlinarith [sq_nonneg (y - j)]
  · rcases hj with hj | rfl | rfl | hj
    · have : (j : ℝ) ≤ -1 := by exact_mod_cast hj
      nlinarith [sq_nonneg (x - 0)]
    · exact absurd rfl hij
    · push_cast; nlinarith [sq_nonneg x]
    · have : (2 : ℝ) ≤ j := by exact_mod_cast hj
      nlinarith [sq_nonneg x]
  · rcases hj with hj | rfl | rfl | hj
    · have : (j : ℝ) ≤ -1 := by exact_mod_cast hj
      nlinarith [sq_nonneg (x - 1)]
    · push_cast; nlinarith [sq_nonneg y]
    · push_cast; nlinarith [sq_nonneg (y - 1)]
    · have : (2 : ℝ) ≤ j := by exact_mod_cast hj
      nlinarith [sq_nonneg (x - 1)]
  · have : (2 : ℝ) ≤ i := by exact_mod_cast hi
    nlinarith [sq_nonneg (y - j)]

/-- Points with `r ≤ x ≤ 1 - r` are at distance `≥ r` from every lattice point. -/
theorem corridor_clear {r x y : ℝ} (hx0 : r ≤ x) (hx1 : x ≤ 1 - r) (hr : 0 ≤ r) (i j : ℤ) :
    r ^ 2 ≤ (x - i) ^ 2 + (y - j) ^ 2 := by
  have hi : i ≤ 0 ∨ 1 ≤ i := by omega
  rcases hi with hi | hi
  · have : (i : ℝ) ≤ 0 := by exact_mod_cast hi
    nlinarith [sq_nonneg (y - j)]
  · have : (1 : ℝ) ≤ i := by exact_mod_cast hi
    nlinarith [sq_nonneg (y - j)]

/-- The corridor arc: circle of radius `a` centred at `(-a c, a s)` (it passes through the origin); on its right
branch, `x(y) = -a c + √(a² - (y - a s)²)`. If `a(1 - c) = 1 - r` and `x(1 - r) ≥ r`, then `r ≤ x(y) ≤ 1 - r` for
every `y` with `|y - a s| ≤ a s - (1 - r)`. -/
theorem arc_in_corridor {a s c r y : ℝ} (ha : 0 < a) (hac : a * (1 - c) = 1 - r)
    (hstart : r ≤ -a * c + Real.sqrt (a ^ 2 - (1 - r - a * s) ^ 2)) (hy : |y - a * s| ≤ a * s - (1 - r)) :
    r ≤ -a * c + Real.sqrt (a ^ 2 - (y - a * s) ^ 2) ∧ -a * c + Real.sqrt (a ^ 2 - (y - a * s) ^ 2) ≤ 1 - r := by
  have h1 : (y - a * s) ^ 2 ≤ (1 - r - a * s) ^ 2 := by
    have : (y - a * s) ^ 2 ≤ (a * s - (1 - r)) ^ 2 := by
      rw [← sq_abs (y - a * s)]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    nlinarith
  have hup : Real.sqrt (a ^ 2 - (y - a * s) ^ 2) ≤ a := by
    calc Real.sqrt (a ^ 2 - (y - a * s) ^ 2) ≤ Real.sqrt (a ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (y - a * s)])
      _ = a := Real.sqrt_sq ha.le
  constructor
  · have := Real.sqrt_le_sqrt (by linarith : a ^ 2 - (1 - r - a * s) ^ 2 ≤ a ^ 2 - (y - a * s) ^ 2)
    linarith
  · linarith

/-- The starting condition `x(1-r) ≥ r` in half-angle form: with `s = 2t/(1+t²)`, `c = (1-t²)/(1+t²)`,
`a = (1-r)(1+t²)/(2t²)`, it holds whenever `K t² - 2A t + r(1-r) ≤ 0`, `0 < t ≤ 1`, `0 < r ≤ 1/3`. -/
theorem start_condition {r t : ℝ} (h0 : 0 < r) (h1 : r ≤ 1 / 3) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hq : K r * t ^ 2 - 2 * A r * t + r * (1 - r) ≤ 0) :
    let a := (1 - r) * (1 + t ^ 2) / (2 * t ^ 2)
    let s := 2 * t / (1 + t ^ 2)
    let c := (1 - t ^ 2) / (1 + t ^ 2)
    r ≤ -a * c + Real.sqrt (a ^ 2 - (1 - r - a * s) ^ 2) := by
  intro a s c
  have hr1 : 0 < 1 - r := by linarith
  have ha : 0 < a := by positivity
  have hrc : 0 ≤ r + a * c := by
    have : a * c = (1 - r) * (1 - t ^ 2) / (2 * t ^ 2) := by simp only [a, c]; field_simp
    rw [this]; have : 0 ≤ 1 - t ^ 2 := by nlinarith
    positivity
  -- (r + a c)² ≤ a² - (1 - r - a s)²  ⟺  2a(s(1-r) - r c) ≥ (1-r)² + r²  ⟺  the quadratic condition
  have e : a ^ 2 - (1 - r - a * s) ^ 2 - (r + a * c) ^ 2 =
      -(K r * t ^ 2 - 2 * A r * t + r * (1 - r)) / t ^ 2 := by
    simp only [a, s, c]; unfold K A; field_simp; ring
  have : 0 ≤ -(K r * t ^ 2 - 2 * A r * t + r * (1 - r)) / t ^ 2 := by
    apply div_nonneg _ (by positivity); nlinarith
  have hsq : (r + a * c) ^ 2 ≤ a ^ 2 - (1 - r - a * s) ^ 2 := by linarith
  have := Real.le_sqrt_of_sq_le hsq
  linarith

/-- `a sin α = (1 - r)/t` for the half-angle parametrisation. -/
theorem height_identity {r t : ℝ} (ht : 0 < t) :
    (1 - r) * (1 + t ^ 2) / (2 * t ^ 2) * (2 * t / (1 + t ^ 2)) = (1 - r) / t := by
  field_simp

/-! ### Upper bound: the corridor lemma -/

/-- **Corridor lemma.** The arc piece `φ ↦ (ℓ₀ + a sin φ, τ₀ + a(1 - cos φ))`, `φ ∈ [0, ε]`, turns through `ε < π/2`
with `tan ε < 2r/m`. If its transverse coordinate runs from at most `τₖ - r` to at least `τₖ + r`, it passes strictly
within `r` of a point `(c + n m, τₖ)` of the lattice line. -/
theorem corridor_lemma {a ε r m ℓ₀ τ₀ τk c : ℝ} (ha : 0 < a) (hr : 0 < r) (hm : 0 < m) (hε0 : 0 < ε)
    (hε : ε < π / 2) (htan : Real.tan ε < 2 * r / m) (hlo : τ₀ ≤ τk - r)
    (hhi : τk + r ≤ τ₀ + a * (1 - Real.cos ε)) :
    ∃ φ ∈ Set.Icc 0 ε, ∃ n : ℤ,
      (ℓ₀ + a * Real.sin φ - (c + n * m)) ^ 2 + (τ₀ + a * (1 - Real.cos φ) - τk) ^ 2 < r ^ 2 := by
  set τ := fun φ : ℝ => τ₀ + a * (1 - Real.cos φ) with hτ
  set ℓ := fun φ : ℝ => ℓ₀ + a * Real.sin φ with hℓ
  have hcont_τ : Continuous τ := by simp only [hτ]; fun_prop
  have hcont_ℓ : Continuous ℓ := by simp only [hℓ]; fun_prop
  have hπ : ε ≤ π := by linarith [Real.pi_pos]
  -- cos is strictly decreasing on [0, π], so τ is strictly increasing on [0, ε]
  have hmono : StrictMonoOn τ (Set.Icc 0 ε) := by
    intro x hx y hy hxy
    simp only [hτ]
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hx.1 (hy.2.trans hπ) hxy
    nlinarith
  -- φ₁ with τ = τk - r and φ₂ with τ = τk + r
  obtain ⟨φ₁, hφ₁, h1⟩ : ∃ φ ∈ Set.Icc 0 ε, τ φ = τk - r := by
    have := intermediate_value_Icc hε0.le hcont_τ.continuousOn
    exact this ⟨by simp [hτ]; linarith, by simp only [hτ]; linarith⟩
  obtain ⟨φ₂, hφ₂, h2⟩ : ∃ φ ∈ Set.Icc 0 ε, τ φ = τk + r := by
    have := intermediate_value_Icc hε0.le hcont_τ.continuousOn
    exact this ⟨by simp [hτ]; linarith, by simp only [hτ]; linarith⟩
  have h12 : φ₁ < φ₂ := by
    by_contra hle; push_neg at hle
    have := hmono.monotoneOn hφ₂ hφ₁ hle; linarith
  -- longitudinal extent: ℓ φ₂ - ℓ φ₁ ≥ 2r cot ε > m, via cos(ε - φ₂) ≥ cos(ε - φ₁)
  have hext : m < ℓ φ₂ - ℓ φ₁ := by
    have hcosε : 0 < Real.cos ε := Real.cos_pos_of_mem_Ioo ⟨by linarith, hε⟩
    have hsinε : 0 < Real.sin ε := Real.sin_pos_of_pos_of_lt_pi hε0 (by linarith)
    have hcmp : Real.cos (ε - φ₁) ≤ Real.cos (ε - φ₂) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hφ₂.2]) (by linarith [hφ₁.1]) (by linarith)
    rw [Real.cos_sub, Real.cos_sub] at hcmp
    -- a (sin φ₂ - sin φ₁) sin ε ≥ a (cos φ₁ - cos φ₂) cos ε = 2r cos ε
    have hdiff : a * (Real.cos φ₁ - Real.cos φ₂) = 2 * r := by simp only [hτ] at h1 h2; linarith
    have hl : (ℓ φ₂ - ℓ φ₁) * Real.sin ε ≥ 2 * r * Real.cos ε := by
      simp only [hℓ]; nlinarith
    have htan' : m * Real.sin ε < 2 * r * Real.cos ε := by
      rw [Real.tan_eq_sin_div_cos, div_lt_div_iff₀ hcosε hm] at htan; linarith
    nlinarith
  -- a lattice position strictly inside (ℓ φ₁, ℓ φ₂)
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℤ, ℓ φ₁ < c + n * m ∧ c + n * m < ℓ φ₂ := by
    refine ⟨⌊(ℓ φ₁ - c) / m⌋ + 1, ?_, ?_⟩
    · have := Int.lt_floor_add_one ((ℓ φ₁ - c) / m)
      push_cast
      have : ℓ φ₁ - c < (⌊(ℓ φ₁ - c) / m⌋ + 1) * m := by rwa [div_lt_iff₀ hm] at this
      linarith
    · have := Int.floor_le ((ℓ φ₁ - c) / m)
      push_cast
      have : ⌊(ℓ φ₁ - c) / m⌋ * m ≤ ℓ φ₁ - c := by rwa [le_div_iff₀ hm] at this
      linarith
  obtain ⟨φ, hφ, hφℓ⟩ : ∃ φ ∈ Set.Icc φ₁ φ₂, ℓ φ = c + n * m :=
    intermediate_value_Icc h12.le hcont_ℓ.continuousOn ⟨hn1.le, hn2.le⟩
  have hφ1 : φ₁ < φ := lt_of_le_of_ne hφ.1 (by rintro rfl; linarith)
  have hφ2 : φ < φ₂ := lt_of_le_of_ne hφ.2 (by rintro rfl; linarith)
  have hφε : φ ∈ Set.Icc 0 ε := ⟨hφ₁.1.trans hφ.1, hφ.2.trans hφ₂.2⟩
  have t1 := hmono hφ₁ hφε hφ1
  have t2 := hmono hφε hφ₂ hφ2
  refine ⟨φ, hφε, n, ?_⟩
  have : ℓ₀ + a * Real.sin φ - (c + n * m) = 0 := by simp only [hℓ] at hφℓ; linarith
  rw [this]
  have hb : |τ₀ + a * (1 - Real.cos φ) - τk| < r := by
    rw [abs_lt]; simp only [hτ] at t1 t2 h1 h2; constructor <;> linarith
  nlinarith [abs_nonneg (τ₀ + a * (1 - Real.cos φ) - τk), sq_abs (τ₀ + a * (1 - Real.cos φ) - τk)]

/-! ### Upper bound: Farey gaps -/

theorem farey_product {x y Q : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (h : Q < x + y) : Q - 1 < x * y := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ x - 1) (by linarith : 0 ≤ y - 1)]

/-- An angle `θ ∈ [0, π/2]` with `sin θ < 1/(Q-1)`, `Q ≥ 2`, is less than `π/Q`. -/
theorem farey_angle {θ Q : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ π / 2) (hQ : 2 ≤ Q) (hs : Real.sin θ < 1 / (Q - 1)) :
    θ < π / Q := by
  have hJ := Real.mul_le_sin hθ0 hθ
  have hQ1 : 0 < Q - 1 := by linarith
  have hπ := Real.pi_pos
  have h0 : 2 / π * θ < 1 / (Q - 1) := lt_of_le_of_lt hJ hs
  have h1 : θ < π / (2 * (Q - 1)) := by
    calc θ = π / 2 * (2 / π * θ) := by field_simp
      _ < π / 2 * (1 / (Q - 1)) := by gcongr
      _ = π / (2 * (Q - 1)) := by field_simp
  have h2 : π / (2 * (Q - 1)) ≤ π / Q :=
    div_le_div_of_nonneg_left hπ.le (by linarith) (by linarith)
  exact h1.trans_le h2

/-! ### Upper bound: Minkowski range -/

/-- For `a ≥ 4/r³`, `r ≤ 1/10`, `0 ≤ t ≤ 3/(2r)`: the arc is within `0.29 r` of its tangent, and
`2r/3 + 0.29 r < r`. -/
theorem minkowski_offset {a r t : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 10) (ha : 4 / r ^ 3 ≤ a) (ht0 : 0 ≤ t)
    (ht : t ≤ 3 / (2 * r)) : a - Real.sqrt (a ^ 2 - t ^ 2) ≤ 29 / 100 * r ∧ 2 / 3 * r + 29 / 100 * r < r := by
  refine ⟨?_, by linarith⟩
  have hapos : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hr3 : 0 < r ^ 3 := by positivity
  have har : 4 ≤ a * r ^ 3 := by rwa [div_le_iff₀ hr3] at ha
  have htr : t * r ≤ 3 / 2 := by rw [le_div_iff₀ (by positivity)] at ht; linarith
  -- t ≤ a/2, so √(a² - t²) ≥ a/2 > 0 and a - √(a² - t²) = t²/(a + √(a² - t²)) ≤ t²/a
  have htr3 : t * r ^ 3 ≤ 3 / 2 * r ^ 2 := by
    have : t * r ^ 3 = (t * r) * r ^ 2 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right htr (by positivity)
  have hta : t ≤ a / 2 := by
    have : t * r ^ 3 ≤ a / 2 * r ^ 3 := by nlinarith
    exact le_of_mul_le_mul_right this hr3
  have hsq : 0 ≤ a ^ 2 - t ^ 2 := by nlinarith
  have hS := Real.sq_sqrt hsq
  have hSn : 0 ≤ Real.sqrt (a ^ 2 - t ^ 2) := Real.sqrt_nonneg _
  have hSa : a * (99 / 100) ≤ Real.sqrt (a ^ 2 - t ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    -- t r³ ≤ (3/2) r² ≤ (3/800)·4 ≤ (3/800) a r³, so t ≤ (3/800) a
    have : t * r ^ 3 ≤ 3 / 800 * a * r ^ 3 := by nlinarith
    have ht8 : t ≤ 3 / 800 * a := le_of_mul_le_mul_right this hr3
    nlinarith
  -- (a - S)(a + S) = t², a + S ≥ 1.99 a
  have hprod : (a - Real.sqrt (a ^ 2 - t ^ 2)) * (a + Real.sqrt (a ^ 2 - t ^ 2)) = t ^ 2 := by nlinarith
  have ht2 : t ^ 2 * r ^ 2 ≤ 9 / 4 := by nlinarith
  have hgoal : t ^ 2 ≤ 29 / 100 * r * (a * (199 / 100)) := by nlinarith
  nlinarith

/-! ### Upper bound: the middle range -/

/-- The explicit angle `ε_m = 1.01 √(2(1/m + 2r)/a)`. -/
noncomputable def eps (a r m : ℝ) : ℝ := 101 / 100 * Real.sqrt (2 * (1 / m + 2 * r) / a)

/-- Small-angle data used below: for `2/r² < a`, `r ≤ 1/10`, `m ≥ 1`, we have `ε_m² ≤ 0.0123`. -/
theorem eps_sq {a r m : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 10) (ha : 2 / r ^ 2 < a) (hm : 1 ≤ m) :
    eps a r m ^ 2 = (101 / 100) ^ 2 * (2 * (1 / m + 2 * r) / a) ∧ eps a r m ^ 2 ≤ 123 / 10000 := by
  have hapos : 0 < a := lt_trans (by positivity) ha
  have hx : 0 ≤ 2 * (1 / m + 2 * r) / a := by positivity
  have e : eps a r m ^ 2 = (101 / 100) ^ 2 * (2 * (1 / m + 2 * r) / a) := by
    unfold eps; rw [mul_pow, Real.sq_sqrt hx]
  refine ⟨e, ?_⟩
  rw [e]
  have h1m : 1 / m ≤ 1 := by rw [div_le_one (by linarith)]; exact hm
  have ha200 : 200 < a := by
    have : 2 / r ^ 2 ≥ 200 := by
      rw [ge_iff_le, le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have : 2 * (1 / m + 2 * r) / a ≤ 2 * (1 + 2 * (1 / 10)) / 200 := by
    rw [div_le_div_iff₀ hapos (by norm_num)]; nlinarith
  nlinarith

theorem eps_nonneg (a r m : ℝ) : 0 ≤ eps a r m := by unfold eps; positivity

/-- `a(1 - cos ε_m) ≥ 1/m + 2r`. -/
theorem eps_cos {a r m : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 10) (ha : 2 / r ^ 2 < a) (hm : 1 ≤ m) :
    1 / m + 2 * r ≤ a * (1 - Real.cos (eps a r m)) := by
  obtain ⟨e, hb⟩ := eps_sq hr0 hr ha hm
  have hapos : 0 < a := lt_trans (by positivity) ha
  set x := eps a r m with hxdef
  have hx0 : 0 ≤ x := eps_nonneg a r m
  have hx1 : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; nlinarith
  have hcb := Real.cos_bound hx1
  rw [abs_of_nonneg hx0] at hcb
  have hcos : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 * (5 / 96) := by
    have := (abs_le.mp hcb).2; linarith
  -- a (x²/2 - 5x⁴/96) ≥ 1/m + 2r since x² = 1.0201 · 2(1/m+2r)/a and x² ≤ 0.0123
  have hx2 : a * x ^ 2 = (101 / 100) ^ 2 * (2 * (1 / m + 2 * r)) := by rw [e]; field_simp
  have hpos : 0 ≤ 1 / m + 2 * r := by have : 0 < m := by linarith
                                      positivity
  have : a * (x ^ 2 / 2 - x ^ 4 * (5 / 96)) ≥ 1 / m + 2 * r := by
    have : a * (x ^ 2 / 2 - x ^ 4 * (5 / 96)) = a * x ^ 2 * (1 / 2 - x ^ 2 * (5 / 96)) := by ring
    rw [this, hx2]
    nlinarith [sq_nonneg x]
  nlinarith

/-- `tan ε_m < 2r/m` when `a > 0.52 (m + 2r m²)/r²`, which holds for `m ≤ a r²`, `m² ≤ a r / 4`. -/
theorem eps_tan {a r m : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 10) (ha : 2 / r ^ 2 < a) (hm : 1 ≤ m)
    (hQ1 : m ≤ a * r ^ 2) (hQ2 : m ^ 2 ≤ a * r / 4) : Real.tan (eps a r m) < 2 * r / m := by
  obtain ⟨e, hb⟩ := eps_sq hr0 hr ha hm
  have hapos : 0 < a := lt_trans (by positivity) ha
  have hmpos : 0 < m := by linarith
  set x := eps a r m with hxdef
  have hx0 : 0 ≤ x := eps_nonneg a r m
  have hcos : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have hcpos : 0 < Real.cos x := by nlinarith
  have hsin : Real.sin x ≤ x := Real.sin_le hx0
  rw [Real.tan_eq_sin_div_cos, div_lt_div_iff₀ hcpos hmpos]
  -- sin x · m ≤ x m, and x m < 2r (1 - x²/2) ≤ 2 r cos x
  have key : x * m < 2 * r * (1 - x ^ 2 / 2) := by
    -- (x m)² = 1.0201 · 2(m + 2r m²)/a ≤ 1.0201 · 2 · 1.5 r² < (2r · 0.9938)²
    have hxm2 : (x * m) ^ 2 = (101 / 100) ^ 2 * (2 * (m + 2 * r * m ^ 2) / a) := by
      rw [mul_pow, e]; field_simp
    have hnum : m + 2 * r * m ^ 2 ≤ 3 / 2 * (a * r ^ 2) := by nlinarith
    have hfrac : 2 * (m + 2 * r * m ^ 2) / a ≤ 3 * r ^ 2 := by
      rw [div_le_iff₀ hapos]; nlinarith
    have hle : (x * m) ^ 2 ≤ (101 / 100) ^ 2 * 3 * r ^ 2 := by
      rw [hxm2]; nlinarith
    have hrhs : 0 < 2 * r * (1 - x ^ 2 / 2) := by nlinarith
    have : (101 / 100) ^ 2 * 3 * r ^ 2 < (2 * r * (1 - x ^ 2 / 2)) ^ 2 := by
      have hf : 99 / 100 ≤ 1 - x ^ 2 / 2 := by nlinarith
      have : (2 * r * (99 / 100)) ^ 2 ≤ (2 * r * (1 - x ^ 2 / 2)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by nlinarith) 2
      nlinarith [sq_nonneg r]
    have hxm0 : 0 ≤ x * m := by positivity
    nlinarith [sq_nonneg (x * m - 2 * r * (1 - x ^ 2 / 2))]
  nlinarith [mul_le_mul_of_nonneg_right hsin hmpos.le]

theorem eps_le {a r m : ℝ} (hr0 : 0 < r) (ha : 0 < a) (hm : 1 ≤ m) :
    eps a r m ≤ 101 / 100 * Real.sqrt (2 * (1 + 2 * r) / a) := by
  unfold eps
  gcongr
  rw [div_le_one (by linarith)]; exact hm

theorem eps_lt_half_pi {a r m : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 10) (ha : 2 / r ^ 2 < a) (hm : 1 ≤ m) :
    eps a r m < π / 2 := by
  obtain ⟨-, hb⟩ := eps_sq hr0 hr ha hm
  have := eps_nonneg a r m
  have : eps a r m < 1 := by nlinarith
  linarith [Real.pi_gt_three]

/-! ### Upper bound: the three ranges -/

/-- Middle range `2/r² < a < 4/r³`: `2a (π/Q + ε̄) ≤ 28/r²` with `Q = min(a r², √(a r)/2)`. -/
theorem middle_bound {a r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 10) (ha1 : 2 / r ^ 2 < a) (ha2 : a < 4 / r ^ 3) :
    2 ≤ min (a * r ^ 2) (Real.sqrt (a * r) / 2) ∧
      2 * a * (π / min (a * r ^ 2) (Real.sqrt (a * r) / 2) + 101 / 100 * Real.sqrt (2 * (1 + 2 * r) / a)) ≤
        28 / r ^ 2 := by
  have hapos : 0 < a := lt_trans (by positivity) ha1
  have hr2 : 0 < r ^ 2 := by positivity
  have hr3 : 0 < r ^ 3 := by positivity
  have h1 : 2 < a * r ^ 2 := by rwa [div_lt_iff₀ hr2] at ha1
  have h2 : a * r ^ 3 < 4 := by rwa [lt_div_iff₀ hr3] at ha2
  have har : 16 ≤ a * r := by
    have : 2 / r ≤ a * r := by
      rw [div_le_iff₀ hr0]; nlinarith
    have : 20 ≤ 2 / r := by rw [le_div_iff₀ hr0]; linarith
    linarith
  have hsq : 4 ≤ Real.sqrt (a * r) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt har
  have hQ : 2 ≤ min (a * r ^ 2) (Real.sqrt (a * r) / 2) := le_min h1.le (by linarith)
  refine ⟨hQ, ?_⟩
  set Q := min (a * r ^ 2) (Real.sqrt (a * r) / 2)
  have hQpos : 0 < Q := by linarith
  -- 2aπ/Q ≤ 2π max(1/r², 2√(a/r)) ≤ 8π/r²
  have hA : 2 * a * (π / Q) ≤ 8 * π / r ^ 2 := by
    have hcase : a / Q ≤ 4 / r ^ 2 := by
      rcases min_choice (a * r ^ 2) (Real.sqrt (a * r) / 2) with h | h
      · rw [show Q = a * r ^ 2 from h, div_le_div_iff₀ (by positivity) hr2]; nlinarith
      · rw [show Q = Real.sqrt (a * r) / 2 from h]
        have hs := Real.sq_sqrt (by positivity : 0 ≤ a * r)
        have hspos : 0 < Real.sqrt (a * r) := by linarith
        rw [div_le_div_iff₀ (by positivity) hr2]
        -- a r² ≤ 2 √(a r) ⟺ a r⁴ ≤ 4/... : (a r²)² = a r³ · a r < 4 a r = 4 √(ar)²
        have : (a * r ^ 2) ^ 2 < (2 * Real.sqrt (a * r)) ^ 2 := by
          have e : (a * r ^ 2) ^ 2 = (a * r ^ 3) * (a * r) := by ring
          rw [e, mul_pow, hs]; nlinarith
        have : a * r ^ 2 < 2 * Real.sqrt (a * r) := by
          nlinarith [sq_nonneg (a * r ^ 2 - 2 * Real.sqrt (a * r))]
        nlinarith
    have := mul_le_mul_of_nonneg_left hcase (by linarith [Real.pi_pos] : 0 ≤ 2 * π)
    calc 2 * a * (π / Q) = 2 * π * (a / Q) := by ring
      _ ≤ 2 * π * (4 / r ^ 2) := this
      _ = 8 * π / r ^ 2 := by ring
  -- 2a · 1.01 √(2(1+2r)/a) = 2.02 √(2(1+2r) a) ≤ 2.02 √(9.6/r³) ≤ 6.3 r^{-3/2} ≤ 2/r²  (r ≤ 1/10)
  have hB : 2 * a * (101 / 100 * Real.sqrt (2 * (1 + 2 * r) / a)) ≤ 2 / r ^ 2 := by
    have hx : 0 ≤ 2 * (1 + 2 * r) / a := by positivity
    have hw := Real.sq_sqrt hx
    have hw0 : 0 ≤ Real.sqrt (2 * (1 + 2 * r) / a) := Real.sqrt_nonneg _
    set w := Real.sqrt (2 * (1 + 2 * r) / a)
    set W := 2 * a * (101 / 100 * w) with hW
    have hW0 : 0 ≤ W := by positivity
    have hW2 : W ^ 2 = (202 / 100) ^ 2 * (2 * (1 + 2 * r) * a) := by
      rw [hW, show (2 * a * (101 / 100 * w)) ^ 2 = (202 / 100) ^ 2 * a ^ 2 * w ^ 2 by ring, hw]
      field_simp
    have hr4 : W ^ 2 * r ^ 4 ≤ 4 := by
      rw [hW2]
      have e : 2 * (1 + 2 * r) * a * r ^ 4 = 2 * (1 + 2 * r) * r * (a * r ^ 3) := by ring
      have : (202 / 100) ^ 2 * (2 * (1 + 2 * r) * a) * r ^ 4 = (202 / 100) ^ 2 * (2 * (1 + 2 * r) * r * (a * r ^ 3)) := by
        rw [← e]; ring
      rw [this]
      have : 2 * (1 + 2 * r) * r ≤ 24 / 100 := by nlinarith
      nlinarith
    have hpos : 0 < 2 / r ^ 2 := by positivity
    rw [← pow_le_pow_iff_left₀ hW0 hpos.le two_ne_zero, div_pow, le_div_iff₀ (by positivity)]
    have : (r ^ 2) ^ 2 = r ^ 4 := by ring
    rw [this]; linarith
  have hπ : π < 3.15 := Real.pi_lt_d2
  have : 8 * π / r ^ 2 + 2 / r ^ 2 ≤ 28 / r ^ 2 := by
    rw [← add_div, div_le_div_iff_of_pos_right hr2]; linarith
  calc 2 * a * (π / Q + 101 / 100 * Real.sqrt (2 * (1 + 2 * r) / a))
      = 2 * a * (π / Q) + 2 * a * (101 / 100 * Real.sqrt (2 * (1 + 2 * r) / a)) := by ring
    _ ≤ 8 * π / r ^ 2 + 2 / r ^ 2 := add_le_add hA hB
    _ ≤ 28 / r ^ 2 := this

/-- Small range `a ≤ 2/r²`: the reach `≤ 2a ≤ 4/r² ≤ 28/r²`. -/
theorem small_bound {a r : ℝ} (hr0 : 0 < r) (ha : a ≤ 2 / r ^ 2) : 2 * a ≤ 28 / r ^ 2 := by
  have : 2 / r ^ 2 ≤ 14 / r ^ 2 := by gcongr; norm_num
  calc 2 * a ≤ 2 * (2 / r ^ 2) := by linarith
    _ ≤ 28 / r ^ 2 := by rw [show 2 * (2 / r ^ 2) = 4 / r ^ 2 by ring]; gcongr; norm_num

/-- Large range `a ≥ 4/r³`: the reach `< 3/(2r) + r ≤ 28/r²`. -/
theorem large_bound {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 10) : 3 / (2 * r) + r ≤ 28 / r ^ 2 := by
  rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hr0 hr0, mul_pos (mul_pos hr0 hr0) hr0]

end OrchardArcs
