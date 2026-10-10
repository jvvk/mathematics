import Mathlib

/-!
# Colour the points, not the plane (MSE 1381502)

`N` points pairwise more than `1` apart contain `N/7` pairwise more than `√3` apart, but no tiling
argument with seven colours proves it.

* `thirty`, `thirty_strict`: points at distances in `[1, √3]` from `P`, at most `30°` apart as seen
  from `P`, are at most `1` apart, and less than `1` below `30°` (the lemma behind the point
  colouring);
* `density_eq`: a cell of diameter `≤ 1` (area `≤ π/4`, isodiametric inequality) thickened by
  `√3/2` (Brunn–Minkowski) fills at most `1/(1 + √3)²` of the thickened region;
  `ratio_mono` is the monotonicity used there; `density_lt`: this is less than `1/7`;
* `colours_ge_eight`: so `k` colour classes, each of density at most `1/(1 + √3)²`, cover the
  plane only if `k ≥ 8`;
* `hexagon_counterexample`: in the seven-colour hexagon scheme of the 2023 answer, the points
  `(0.45, 0)` and `(1.8, √3/4)` lie in two hexagons of the same colour and are more than `1` but
  less than `√3` apart.
-/

open Real

namespace SevenColours

/-- The lemma: `r₁, r₂ ∈ [1, √3]` and `cos θ ≥ √3/2` give `r₁² + r₂² - 2 r₁ r₂ cos θ ≤ 1`. -/
theorem thirty (r₁ r₂ c : ℝ) (h1 : 1 ≤ r₁) (h1' : r₁ ≤ √3) (h2 : 1 ≤ r₂) (h2' : r₂ ≤ √3)
    (hc : √3 / 2 ≤ c) : r₁ ^ 2 + r₂ ^ 2 - 2 * r₁ * r₂ * c ≤ 1 := by
  have s3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have s1 : 1 < √3 := by
    rw [show (1 : ℝ) = √1 by simp]; exact sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- each `rᵢ² ≤ (1 + √3) rᵢ - √3`, and the bilinear remainder is largest at a corner
  have q1 : r₁ ^ 2 ≤ (1 + √3) * r₁ - √3 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1')]
  have q2 : r₂ ^ 2 ≤ (1 + √3) * r₂ - √3 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2')]
  have hr : 0 ≤ r₁ * r₂ := by positivity
  have hb : 2 * r₁ * r₂ * c ≥ √3 * (r₁ * r₂) := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2'),
    mul_nonneg (sub_nonneg.2 h1') (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 h1') (sub_nonneg.2 h2')]

/-- The strict form: `cos θ > √3/2` (an angle below `30°`) gives a distance below `1`. -/
theorem thirty_strict (r₁ r₂ c : ℝ) (h1 : 1 ≤ r₁) (h1' : r₁ ≤ √3) (h2 : 1 ≤ r₂) (h2' : r₂ ≤ √3)
    (hc : √3 / 2 < c) : r₁ ^ 2 + r₂ ^ 2 - 2 * r₁ * r₂ * c < 1 := by
  have h := thirty r₁ r₂ (√3 / 2) h1 h1' h2 h2' le_rfl
  have hr : 0 < r₁ * r₂ := by positivity
  nlinarith

/-- `A / (√A + c)²` increases with `A ≥ 0` (for `c > 0`). -/
theorem ratio_mono {A B c : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hc : 0 < c) :
    A / (√A + c) ^ 2 ≤ B / (√B + c) ^ 2 := by
  have hB : 0 ≤ B := hA.trans hAB
  have pa : 0 < √A + c := by positivity
  have pb : 0 < √B + c := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hs : √A ≤ √B := sqrt_le_sqrt hAB
  have eA : A = √A ^ 2 := (sq_sqrt hA).symm
  have eB : B = √B ^ 2 := (sq_sqrt hB).symm
  rw [eA, eB, sqrt_sq (sqrt_nonneg _), sqrt_sq (sqrt_nonneg _)]
  have : 0 ≤ √A := sqrt_nonneg _
  -- `(√A (√B + c))² ≤ (√B (√A + c))²` since `√A √B + √A c ≤ √A √B + √B c`
  have key : √A * (√B + c) ≤ √B * (√A + c) := by nlinarith
  have k0 : 0 ≤ √A * (√B + c) := by positivity
  nlinarith [mul_le_mul key key k0 (by positivity)]

/-- The largest fraction: `(π/4) / (√(π/4) + √π · √3/2)² = 1/(1 + √3)²`. -/
theorem density_eq : (π / 4) / (√(π / 4) + √π * (√3 / 2)) ^ 2 = 1 / (1 + √3) ^ 2 := by
  have hp : 0 < π := pi_pos
  have h4 : √(π / 4) = √π / 2 := by
    rw [sqrt_div hp.le, show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  have sp : √π ^ 2 = π := sq_sqrt hp.le
  have spos : 0 < √π := sqrt_pos.2 hp
  rw [h4, show √π / 2 + √π * (√3 / 2) = √π / 2 * (1 + √3) by ring, mul_pow, div_pow, sp]
  have : (0 : ℝ) < 1 + √3 := by positivity
  field_simp
  norm_num

/-- `1/(1 + √3)² < 1/7`, i.e. `(1 + √3)² = 4 + 2√3 > 7`. -/
theorem density_lt : 1 / (1 + √3) ^ 2 < 1 / 7 := by
  have s3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have h : (3 / 2 : ℝ) < √3 := by
    rw [show (3 / 2 : ℝ) = √(9 / 4) by
      rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- If `k` colour classes, each of density at most `1/(1 + √3)²`, cover the plane (total density
`1`), then `k ≥ 8`. -/
theorem colours_ge_eight (k : ℕ) (hk : (1 : ℝ) ≤ k * (1 / (1 + √3) ^ 2)) : 8 ≤ k := by
  by_contra h
  have hk7 : (k : ℝ) ≤ 7 := by exact_mod_cast Nat.lt_succ_iff.mp (not_le.mp h)
  have hpos : (0 : ℝ) < 1 / (1 + √3) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right hk7 hpos.le
  have := density_lt
  linarith

/-- The closed regular hexagon of side `1/2` centred at `c`, with vertices in directions
`0°, 60°, …`: `|y| ≤ √3/4` and `√3 |x| + |y| ≤ √3/2` in coordinates centred at `c`. -/
def InHex (c p : ℝ × ℝ) : Prop :=
  |p.2 - c.2| ≤ √3 / 4 ∧ √3 * |p.1 - c.1| + |p.2 - c.2| ≤ √3 / 2

/-- The scheme of the 2023 answer: centres `i x + j y` with `x = (3/4, √3/4)`, `y = (0, √3/2)`,
coloured by the coset of the sublattice spanned by `a = 3x - y` and `b = x + 2y`. -/
noncomputable def centre (i j : ℤ) : ℝ × ℝ := (i * (3 / 4), i * (√3 / 4) + j * (√3 / 2))

/-- `(0.45, 0)` and `(1.8, √3/4)` lie in the hexagons centred at `0` and at `a = 3x - y`, which
differ by `a` and so have the same colour; they are more than `1` and less than `√3` apart. -/
theorem hexagon_counterexample :
    InHex (centre 0 0) (0.45, 0) ∧ InHex (centre 3 (-1)) (1.8, √3 / 4) ∧
      centre 3 (-1) = (3 * (3 / 4) - 0, 3 * (√3 / 4) - √3 / 2) ∧
      1 < (1.8 - 0.45) ^ 2 + (√3 / 4 - 0) ^ 2 ∧ (1.8 - 0.45) ^ 2 + (√3 / 4 - 0) ^ 2 < 3 := by
  have s3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have h0 : 0 < √3 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [InHex, centre]; norm_num
    constructor <;> nlinarith
  · simp only [InHex, centre]; push_cast
    have e1 : (1.8 : ℝ) - 3 * (3 / 4) = -(9 / 20) := by norm_num
    have e2 : √3 / 4 - (3 * (√3 / 4) + -1 * (√3 / 2)) = 0 := by ring
    rw [e1, e2, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 20), abs_zero]
    constructor <;> nlinarith
  · simp only [centre]; push_cast; ext <;> simp <;> ring
  · nlinarith
  · nlinarith

end SevenColours
