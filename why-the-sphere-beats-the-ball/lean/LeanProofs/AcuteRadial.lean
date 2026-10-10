import Mathlib

/-!
# Acute triangles on concentric spheres (MO 484567)

Three independent points, uniform in direction on concentric spheres in `ℝ³` of radii `a ≥ b ≥ c > 0`. By Archimedes'
hat-box theorem (quoted), for opposite radii `u, v` the length `M = |U + V|` has density `M/(2uv)` on `[|u-v|, u+v]`,
and given `U, V` the projection `(U + V)·W` is uniform on `[-wM, wM]`. The angle at `W` is obtuse iff
`(U + V)·W > U·V + w²` (`obtuse_iff`), so its probability is `∫ M/(2uv) · q(M) dM` where `q` is a clamped linear
fraction (`uniform_tail`, `integrand_eq`). This file evaluates the three integrals and proves the bound.

* `obtuseC`, `obtuseB`, `obtuseA`: the obtuse probabilities at the smallest, middle and largest radius.
* `acute_formula`: `P = b/(2a) + c²/(6ab) - h³/(6abc)`, `h = √(b² + c² - a²)₊`.
* `acute_le_half`, `acute_lt_half`: `P ≤ 1/2`, with equality iff `a = b`.
* `mixture2`, `mixture3`: the centre experiment in the plane and in space.
-/

namespace AcuteRadial

open Real intervalIntegral MeasureTheory Set

/-! ### The reduction: obtuse condition, uniform tail, integrand -/

/-- The angle at `W` of triangle `UVW` is obtuse iff `(U + V)·W > U·V + |W|²`. -/
theorem obtuse_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (U V W : E) :
    inner ℝ (U - W) (V - W) < 0 ↔ inner ℝ U V + ‖W‖ ^ 2 < inner ℝ (U + V) W := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_add_left, real_inner_self_eq_norm_sq,
    real_inner_comm W U]
  constructor <;> intro h <;> linarith [real_inner_comm V W, real_inner_comm U W]

/-- A uniform point of `[-L, L]` exceeds `T` with probability `max 0 (min 1 ((L - T)/(2L)))`. -/
theorem uniform_tail (L T : ℝ) (hL : 0 < L) :
    (volume (Icc (-L) L ∩ Ioi T)).toReal / (2 * L) = max 0 (min 1 ((L - T) / (2 * L))) := by
  have h2L : (0 : ℝ) < 2 * L := by linarith
  rcases lt_or_ge T (-L) with hT | hT
  · have : Icc (-L) L ∩ Ioi T = Icc (-L) L := by
      ext x; simp only [mem_inter_iff, mem_Icc, mem_Ioi]; constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, by linarith [h.1]⟩
    rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    have : 1 ≤ (L - T) / (2 * L) := by rw [le_div_iff₀ h2L]; linarith
    rw [min_eq_left this, max_eq_right (by norm_num)]
    field_simp; ring
  · rcases le_or_gt T L with hTL | hTL
    · have : Icc (-L) L ∩ Ioi T = Ioc T L := by
        ext x; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]; constructor
        · exact fun h => ⟨h.2, h.1.2⟩
        · exact fun h => ⟨⟨by linarith [h.1], h.2⟩, h.1⟩
      rw [this, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
      have h1 : (L - T) / (2 * L) ≤ 1 := by rw [div_le_iff₀ h2L]; linarith
      have h0 : 0 ≤ (L - T) / (2 * L) := div_nonneg (by linarith) h2L.le
      rw [min_eq_right h1, max_eq_right h0]
    · have : Icc (-L) L ∩ Ioi T = ∅ := by
        ext x; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_empty_iff_false, iff_false]
        intro h; linarith [h.1.2, h.2]
      rw [this, measure_empty, ENNReal.toReal_zero, zero_div]
      have : (L - T) / (2 * L) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) h2L.le
      rw [min_eq_right (by linarith), max_eq_left this]

/-- The integrand: the density `M/(2uv)` of `M = |U + V|` times the conditional obtuse probability, with
`K = u² + v² - w²`. -/
noncomputable def f (u v w K M : ℝ) : ℝ := max 0 (min (M / (2 * u * v)) ((K - (M - w) ^ 2) / (8 * u * v * w)))

/-- For `M > 0` the integrand is the density times `q(M) = P(uniform on [-wM, wM] exceeds (M² + w² - K)/2)`. -/
theorem integrand_eq (u v w K M : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (hM : 0 < M) :
    M / (2 * u * v) * max 0 (min 1 ((w * M - (M ^ 2 + w ^ 2 - K) / 2) / (2 * (w * M)))) = f u v w K M := by
  have hd : 0 < M / (2 * u * v) := by positivity
  have key : (w * M - (M ^ 2 + w ^ 2 - K) / 2) / (2 * (w * M)) = (K - (M - w) ^ 2) / (4 * w * M) := by
    field_simp; ring
  rw [key, f, mul_max_of_nonneg _ _ hd.le, mul_min_of_nonneg _ _ hd.le, mul_zero, mul_one]
  congr 2
  field_simp; ring

theorem f_continuous (u v w K : ℝ) : Continuous (f u v w K) := by
  unfold f; fun_prop

/-- The obtuse probability at the vertex of radius `w`, with opposite radii `u, v`. -/
noncomputable def obtuse (u v w : ℝ) : ℝ := ∫ M in |u - v|..(u + v), f u v w (u ^ 2 + v ^ 2 - w ^ 2) M

/-! ### Integrating the three pieces -/

theorem int_linear (u v l r : ℝ) : ∫ M in l..r, M / (2 * u * v) = (r ^ 2 - l ^ 2) / (4 * u * v) := by
  simp only [div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_id]; ring

theorem int_quad (u v w K l r : ℝ) :
    ∫ M in l..r, (K - (M - w) ^ 2) / (8 * u * v * w)
      = (K * (r - l) - ((r - w) ^ 3 - (l - w) ^ 3) / 3) / (8 * u * v * w) := by
  have : ∀ M : ℝ, (K - (M - w) ^ 2) / (8 * u * v * w)
      = (K - w ^ 2) / (8 * u * v * w) + (2 * w / (8 * u * v * w)) * M + (-1 / (8 * u * v * w)) * M ^ 2 := by
    intro M; ring
  simp only [this]
  have ii : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g volume l r := fun g hg => hg.intervalIntegrable _ _
  rw [intervalIntegral.integral_add (ii _ (by fun_prop)) (ii _ (by fun_prop)),
    intervalIntegral.integral_add (ii _ (by fun_prop)) (ii _ (by fun_prop)), intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow]
  simp only [smul_eq_mul]
  ring

/-- Split an integral of a continuous function at two interior points. -/
theorem split3 (g : ℝ → ℝ) (hg : Continuous g) (l m₁ m₂ r : ℝ) :
    ∫ M in l..r, g M = (∫ M in l..m₁, g M) + (∫ M in m₁..m₂, g M) + ∫ M in m₂..r, g M := by
  rw [intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]

variable {a b c : ℝ}

/-- The smallest radius `c`: obtuse probability `1/2 - c²/(3ab)`. -/
theorem obtuseC (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 < c) : obtuse a b c = 1 / 2 - c ^ 2 / (3 * a * b) := by
  have hb : 0 < b := by linarith
  have ha : 0 < a := by linarith
  set K := a ^ 2 + b ^ 2 - c ^ 2 with hK
  have hK0 : 0 ≤ K := by nlinarith
  set H := Real.sqrt K with hH
  have hH2 : H ^ 2 = K := Real.sq_sqrt hK0
  have hH0 : 0 ≤ H := Real.sqrt_nonneg K
  -- a - b ≤ H - c and H + c ≤ a + b
  have e1 : a - b + c ≤ H := by
    apply Real.le_sqrt_of_sq_le; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a + c) (by linarith : (0:ℝ) ≤ b - c)]
  have e2 : H ≤ a + b - c := by
    rw [hH, Real.sqrt_le_left (by linarith)]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a - c) (by linarith : (0:ℝ) ≤ b - c)]
  unfold obtuse
  rw [abs_of_nonneg (by linarith), split3 _ (f_continuous _ _ _ _) _ (H - c) (H + c)]
  have p1 : ∫ M in (a - b)..(H - c), f a b c K M = ∫ M in (a - b)..(H - c), M / (2 * a * b) := by
    apply intervalIntegral.integral_congr
    intro M hM
    rw [uIcc_of_le (by linarith)] at hM
    obtain ⟨h1, h2⟩ := hM
    have hM0 : 0 ≤ M := by linarith
    unfold f
    have : M / (2 * a * b) ≤ (K - (M - c) ^ 2) / (8 * a * b * c) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ H - c - M) (by linarith : (0:ℝ) ≤ H + c + M),
        mul_pos ha hb, mul_pos (mul_pos ha hb) hc]
    rw [min_eq_left this, max_eq_right (by positivity)]
  have p2 : ∫ M in (H - c)..(H + c), f a b c K M = ∫ M in (H - c)..(H + c), (K - (M - c) ^ 2) / (8 * a * b * c) := by
    apply intervalIntegral.integral_congr
    intro M hM
    rw [uIcc_of_le (by linarith)] at hM
    obtain ⟨h1, h2⟩ := hM
    unfold f
    have hle : (K - (M - c) ^ 2) / (8 * a * b * c) ≤ M / (2 * a * b) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ M + c - H) (by linarith : (0:ℝ) ≤ M + c + H),
        mul_pos ha hb, mul_pos (mul_pos ha hb) hc]
    have hge : 0 ≤ (K - (M - c) ^ 2) / (8 * a * b * c) := by
      apply div_nonneg _ (by positivity)
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ M - c + H) (by linarith : (0:ℝ) ≤ H - (M - c))]
    rw [min_eq_right hle, max_eq_right hge]
  have p3 : ∫ M in (H + c)..(a + b), f a b c K M = ∫ M in (H + c)..(a + b), (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro M hM
    rw [uIcc_of_le (by linarith)] at hM
    obtain ⟨h1, h2⟩ := hM
    unfold f
    have : (K - (M - c) ^ 2) / (8 * a * b * c) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ M - c - H) (by linarith : (0:ℝ) ≤ M - c + H)]
    rw [max_eq_left (le_trans (min_le_right _ _) this)]
  rw [p1, p2, p3, int_linear, int_quad, intervalIntegral.integral_zero, hK]
  field_simp
  ring

/-- The middle radius `b`: obtuse probability `(a - b)/(2a) + c²/(6ab)`. -/
theorem obtuseB (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 < c) :
    obtuse a c b = (a - b) / (2 * a) + c ^ 2 / (6 * a * b) := by
  have hb : 0 < b := by linarith
  have ha : 0 < a := by linarith
  unfold obtuse
  rw [abs_of_nonneg (by linarith)]
  have p : ∫ M in (a - c)..(a + c), f a c b (a ^ 2 + c ^ 2 - b ^ 2) M
      = ∫ M in (a - c)..(a + c), (a ^ 2 + c ^ 2 - b ^ 2 - (M - b) ^ 2) / (8 * a * c * b) := by
    apply intervalIntegral.integral_congr
    intro M hM
    rw [uIcc_of_le (by linarith)] at hM
    obtain ⟨h1, h2⟩ := hM
    unfold f
    have hle : (a ^ 2 + c ^ 2 - b ^ 2 - (M - b) ^ 2) / (8 * a * c * b) ≤ M / (2 * a * c) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ M - (a - c)) (by linarith : (0:ℝ) ≤ M + a - c + 2 * b),
        mul_nonneg (by linarith : (0:ℝ) ≤ a + b) (by linarith : (0:ℝ) ≤ b - c), mul_pos ha hc,
        mul_pos (mul_pos ha hc) hb]
    have hge : 0 ≤ (a ^ 2 + c ^ 2 - b ^ 2 - (M - b) ^ 2) / (8 * a * c * b) := by
      apply div_nonneg _ (by positivity)
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a + c - M) (by linarith : (0:ℝ) ≤ M - a + c),
        mul_nonneg (by linarith : (0:ℝ) ≤ a - b) (by linarith : (0:ℝ) ≤ a + b - M)]
    rw [min_eq_right hle, max_eq_right hge]
  rw [p, int_quad]
  field_simp
  ring

/-- The largest radius `a`: obtuse probability `h³/(6abc)`, `h² = (b² + c² - a²)₊`. -/
theorem obtuseA (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 < c) :
    obtuse b c a = Real.sqrt (max 0 (b ^ 2 + c ^ 2 - a ^ 2)) ^ 3 / (6 * a * b * c) := by
  have hb : 0 < b := by linarith
  have ha : 0 < a := by linarith
  set K := b ^ 2 + c ^ 2 - a ^ 2 with hK
  unfold obtuse
  rw [abs_of_nonneg (by linarith)]
  rcases le_or_gt K 0 with hK0 | hK0
  · rw [max_eq_left hK0, Real.sqrt_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
    rw [← intervalIntegral.integral_zero (a := b - c) (b := b + c) (μ := volume)]
    apply intervalIntegral.integral_congr
    intro M _
    unfold f
    have : (K - (M - a) ^ 2) / (8 * b * c * a) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (M - a)]) (by positivity)
    rw [max_eq_left (le_trans (min_le_right _ _) this)]
  · rw [max_eq_right hK0.le]
    set h := Real.sqrt K with hh
    have hh2 : h ^ 2 = K := Real.sq_sqrt hK0.le
    have hh0 : 0 ≤ h := Real.sqrt_nonneg K
    have hhc : h ≤ c := by rw [hh, Real.sqrt_le_left hc.le]; nlinarith
    have e1 : b - c ≤ a - h := by
      have : h ≤ a - b + c := by
        rw [hh, Real.sqrt_le_left (by linarith)]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a + c) (by linarith : (0:ℝ) ≤ a - b)]
      linarith
    have e2 : a + h ≤ b + c := by
      have hpos : 0 ≤ b + c - a := by nlinarith
      have : h ≤ b + c - a := by
        rw [hh, Real.sqrt_le_left hpos]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a - b) (by linarith : (0:ℝ) ≤ a - c)]
      linarith
    rw [split3 _ (f_continuous _ _ _ _) _ (a - h) (a + h)]
    have zero_out : ∀ l r : ℝ, (∀ M ∈ uIcc l r, K ≤ (M - a) ^ 2) →
        ∫ M in l..r, f b c a K M = 0 := by
      intro l r hlr
      rw [← intervalIntegral.integral_zero (a := l) (b := r) (μ := volume)]
      apply intervalIntegral.integral_congr
      intro M hM
      unfold f
      have : (K - (M - a) ^ 2) / (8 * b * c * a) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith [hlr M hM]) (by positivity)
      rw [max_eq_left (le_trans (min_le_right _ _) this)]
    have q1 := zero_out (b - c) (a - h) (by
      intro M hM; rw [uIcc_of_le e1] at hM
      nlinarith [hM.1, hM.2, mul_nonneg (by linarith [hM.2] : (0:ℝ) ≤ a - h - M) (by linarith [hM.2] : (0:ℝ) ≤ a + h - M)])
    have q3 := zero_out (a + h) (b + c) (by
      intro M hM; rw [uIcc_of_le e2] at hM
      nlinarith [hM.1, hM.2, mul_nonneg (by linarith [hM.1] : (0:ℝ) ≤ M - a - h) (by linarith [hM.1] : (0:ℝ) ≤ M - a + h)])
    have q2 : ∫ M in (a - h)..(a + h), f b c a K M = ∫ M in (a - h)..(a + h), (K - (M - a) ^ 2) / (8 * b * c * a) := by
      apply intervalIntegral.integral_congr
      intro M hM
      rw [uIcc_of_le (by linarith)] at hM
      obtain ⟨h1, h2⟩ := hM
      unfold f
      have hle : (K - (M - a) ^ 2) / (8 * b * c * a) ≤ M / (2 * b * c) := by
        have hk : K ≤ (M + a) ^ 2 := by nlinarith [hh2, hhc, hh0]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_pos hb hc).le (by linarith : (0:ℝ) ≤ (M + a) ^ 2 - K)]
      have hge : 0 ≤ (K - (M - a) ^ 2) / (8 * b * c * a) := by
        apply div_nonneg _ (by positivity)
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ M - a + h) (by linarith : (0:ℝ) ≤ a + h - M)]
      rw [min_eq_right hle, max_eq_right hge]
    rw [q1, q2, q3, int_quad, ← hh2]
    field_simp
    ring

/-- The acute probability: one minus the three obtuse probabilities (right angles have probability zero and a
triangle has at most one obtuse angle). -/
noncomputable def acute (a b c : ℝ) : ℝ := 1 - obtuse b c a - obtuse a c b - obtuse a b c

/-- `h = √(b² + c² - a²)₊`. -/
noncomputable def hgt (a b c : ℝ) : ℝ := Real.sqrt (max 0 (b ^ 2 + c ^ 2 - a ^ 2))

theorem acute_formula (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 < c) :
    acute a b c = b / (2 * a) + c ^ 2 / (6 * a * b) - hgt a b c ^ 3 / (6 * a * b * c) := by
  have hb : 0 < b := by linarith
  have ha : 0 < a := by linarith
  rw [acute, obtuseA hab hbc hc, obtuseB hab hbc hc, obtuseC hab hbc hc, hgt]
  field_simp
  ring

/-! ### The bound -/

/-- `G(a) = 3bc(a - b) - c³ + h³`, so that `6abc (1/2 - P) = G`. -/
noncomputable def G (b c a : ℝ) : ℝ := 3 * b * c * (a - b) - c ^ 3 + hgt a b c ^ 3

theorem half_sub_acute (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 < c) :
    6 * a * b * c * (1 / 2 - acute a b c) = G b c a := by
  have hb : 0 < b := by linarith
  have ha : 0 < a := by linarith
  rw [acute_formula hab hbc hc, G]
  field_simp
  ring

/-- `G` is strictly increasing on `[b, ∞)`: on `[b, √(b² + c²)]` its derivative is `3(bc - ah) > 0` because
`b²c² - a²h² = (a² - b²)(a² - c²)`; beyond, `h = 0` and `G` is linear with slope `3bc`. -/
theorem G_strictMono (hbc : c ≤ b) (hc : 0 < c) : StrictMonoOn (G b c) (Ici b) := by
  have hb : 0 < b := by linarith
  set a₀ := Real.sqrt (b ^ 2 + c ^ 2) with ha₀
  have hba₀ : b < a₀ := by
    rw [ha₀]; apply Real.lt_sqrt_of_sq_lt; nlinarith
  -- on [b, a₀] write G with h³ = K √K, K = b² + c² - a²
  have hG1 : ∀ a ∈ Icc b a₀, G b c a
      = 3 * b * c * (a - b) - c ^ 3 + (b ^ 2 + c ^ 2 - a ^ 2) * Real.sqrt (b ^ 2 + c ^ 2 - a ^ 2) := by
    intro a ha
    have hK : 0 ≤ b ^ 2 + c ^ 2 - a ^ 2 := by
      have : a ^ 2 ≤ a₀ ^ 2 := pow_le_pow_left₀ (by linarith [ha.1]) ha.2 2
      rw [ha₀, Real.sq_sqrt (by positivity)] at this; linarith
    rw [G, hgt, max_eq_right hK]
    have h3 : Real.sqrt (b ^ 2 + c ^ 2 - a ^ 2) ^ 3 = (b ^ 2 + c ^ 2 - a ^ 2) * Real.sqrt (b ^ 2 + c ^ 2 - a ^ 2) := by
      rw [pow_succ, Real.sq_sqrt hK]
    rw [h3]
  have hmono1 : StrictMonoOn (G b c) (Icc b a₀) := by
    let g := fun a => 3 * b * c * (a - b) - c ^ 3 + (b ^ 2 + c ^ 2 - a ^ 2) * Real.sqrt (b ^ 2 + c ^ 2 - a ^ 2)
    have hg : StrictMonoOn g (Icc b a₀) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc b a₀)
      · apply Continuous.continuousOn; fun_prop
      · intro a ha
        rw [interior_Icc] at ha
        obtain ⟨h1, h2⟩ := ha
        have hK : 0 < b ^ 2 + c ^ 2 - a ^ 2 := by
          have : a ^ 2 < a₀ ^ 2 := pow_lt_pow_left₀ h2 (by linarith) (by norm_num)
          rw [ha₀, Real.sq_sqrt (by positivity)] at this; linarith
        have hd : HasDerivAt g (3 * b * c - 3 * a * Real.sqrt (b ^ 2 + c ^ 2 - a ^ 2)) a := by
          have hk : HasDerivAt (fun a : ℝ => b ^ 2 + c ^ 2 - a ^ 2) (-(2 * a)) a := by
            have := (hasDerivAt_pow 2 a).const_sub (b ^ 2 + c ^ 2)
            simpa using this
          have hs := hk.sqrt hK.ne'
          have := ((hasDerivAt_id a).sub_const b |>.const_mul (3 * b * c)).sub_const (c ^ 3) |>.add (hk.mul hs)
          convert this using 1
          · funext x; simp [g]
          · have hsq := Real.sq_sqrt hK.le
            field_simp
            nlinarith [hsq]
        rw [hd.deriv]
        set s := Real.sqrt (b ^ 2 + c ^ 2 - a ^ 2)
        have hs0 : 0 ≤ s := Real.sqrt_nonneg _
        have hss : s ^ 2 = b ^ 2 + c ^ 2 - a ^ 2 := Real.sq_sqrt hK.le
        -- (a s)² < (b c)²
        have key : (a * s) ^ 2 < (b * c) ^ 2 := by
          rw [mul_pow, hss]
          nlinarith [mul_pos (by nlinarith : (0:ℝ) < a ^ 2 - b ^ 2) (by nlinarith : (0:ℝ) < a ^ 2 - c ^ 2)]
        have : a * s < b * c := by
          by_contra hcon; push Not at hcon
          nlinarith [mul_pos hb hc]
        linarith
    intro x hx y hy hxy
    rw [hG1 x hx, hG1 y hy]
    exact hg hx hy hxy
  -- beyond a₀, h = 0
  have hG2 : ∀ a, a₀ ≤ a → G b c a = 3 * b * c * (a - b) - c ^ 3 := by
    intro a ha
    have hK : b ^ 2 + c ^ 2 - a ^ 2 ≤ 0 := by
      have : a₀ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) ha 2
      rw [ha₀, Real.sq_sqrt (by positivity)] at this; linarith
    rw [G, hgt, max_eq_left hK, Real.sqrt_zero]; ring
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  rcases le_or_gt y a₀ with hya | hya
  · exact hmono1 ⟨hx, by linarith⟩ ⟨hy, hya⟩ hxy
  · rcases le_or_gt x a₀ with hxa | hxa
    · calc G b c x ≤ G b c a₀ := hmono1.monotoneOn ⟨hx, hxa⟩ ⟨hba₀.le, le_rfl⟩ hxa
        _ = 3 * b * c * (a₀ - b) - c ^ 3 := hG2 a₀ le_rfl
        _ < 3 * b * c * (y - b) - c ^ 3 := by nlinarith [mul_pos hb hc]
        _ = G b c y := (hG2 y hya.le).symm
    · rw [hG2 x hxa.le, hG2 y hya.le]; nlinarith [mul_pos hb hc]

theorem G_at_b (hc : 0 < c) : G b c b = 0 := by
  rw [G, hgt, show b ^ 2 + c ^ 2 - b ^ 2 = c ^ 2 by ring, max_eq_right (sq_nonneg c), Real.sqrt_sq hc.le]
  ring

/-- `P ≤ 1/2`. -/
theorem acute_le_half (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 < c) : acute a b c ≤ 1 / 2 := by
  have hb : 0 < b := by linarith
  have ha : 0 < a := by linarith
  have h := half_sub_acute hab hbc hc
  have hG : 0 ≤ G b c a := by
    rcases eq_or_lt_of_le hab with h' | h'
    · rw [← h', G_at_b hc]
    · rw [← G_at_b hc]; exact ((G_strictMono hbc hc) (mem_Ici.mpr le_rfl) (mem_Ici.mpr hab) h').le
  have : 0 ≤ 1 / 2 - acute a b c := by
    by_contra hneg; push Not at hneg
    have : 6 * a * b * c * (1 / 2 - acute a b c) < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  linarith

/-- `P < 1/2` when the largest radius is unique. -/
theorem acute_lt_half (hab : b < a) (hbc : c ≤ b) (hc : 0 < c) : acute a b c < 1 / 2 := by
  have hb : 0 < b := by linarith
  have ha : 0 < a := by linarith
  have h := half_sub_acute hab.le hbc hc
  have hG : 0 < G b c a := by
    rw [← G_at_b hc]; exact (G_strictMono hbc hc) (mem_Ici.mpr le_rfl) (mem_Ici.mpr hab.le) hab
  by_contra hneg; push Not at hneg
  have : 6 * a * b * c * (1 / 2 - acute a b c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith

/-- On one sphere (`a = b = c`) the acute probability is `1/2`. -/
theorem acute_sphere (ha : 0 < a) : acute a a a = 1 / 2 := by
  have h := half_sub_acute (le_refl a) (le_refl a) ha
  rw [G_at_b ha] at h
  have : (6 * a * a * a) ≠ 0 := by positivity
  have := (mul_eq_zero.mp h).resolve_left this
  linarith

/-- One vertex at the centre (`c = 0`): the acute probability is `b/(2a) ≤ 1/2`, with equality iff `a = b`. -/
theorem centre_vertex (hab : b ≤ a) (hb : 0 < b) : b / (2 * a) ≤ 1 / 2 ∧ (b / (2 * a) = 1 / 2 ↔ a = b) := by
  have ha : 0 < a := by linarith
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  · rw [div_eq_div_iff (by positivity) (by norm_num)]; constructor <;> intro h <;> linarith

/-! ### The centre experiment -/

/-- In the plane: `(1-ε)³/4 + 3ε(1-ε)²/2 = (1-ε)²(1+5ε)/4`, rising at `ε = 0` (derivative `3/4`). -/
theorem mixture2 (ε : ℝ) : (1 - ε) ^ 3 / 4 + 3 * ε * (1 - ε) ^ 2 / 2 = (1 - ε) ^ 2 * (1 + 5 * ε) / 4 := by ring

theorem mixture2_deriv : HasDerivAt (fun ε : ℝ => (1 - ε) ^ 2 * (1 + 5 * ε) / 4) (3 / 4) 0 := by
  have := (((hasDerivAt_id (0 : ℝ)).const_sub 1).pow 2).mul (((hasDerivAt_id (0 : ℝ)).const_mul 5).const_add 1)
  convert this.div_const 4 using 1 <;> simp; norm_num

theorem mixture2_tenth : (1 - (1 / 10 : ℝ)) ^ 2 * (1 + 5 * (1 / 10)) / 4 = 243 / 800 := by norm_num

/-- In space: `(1-ε)³/2 + 3ε(1-ε)²/2 = (1-ε)²(1+2ε)/2 = 1/2 - 3ε²/2 + ε³ < 1/2` for `0 < ε ≤ 1`. -/
theorem mixture3 (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (1 - ε) ^ 3 / 2 + 3 * ε * (1 - ε) ^ 2 / 2 = (1 - ε) ^ 2 * (1 + 2 * ε) / 2 ∧
    (1 - ε) ^ 2 * (1 + 2 * ε) / 2 < 1 / 2 := by
  refine ⟨by ring, ?_⟩
  nlinarith [mul_pos (mul_pos h0 h0) (by linarith : (0:ℝ) < 3 - 2 * ε)]

end AcuteRadial
