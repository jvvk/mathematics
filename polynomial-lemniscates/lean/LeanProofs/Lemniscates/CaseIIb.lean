import LeanProofs.Lemniscates.CaseII
import LeanProofs.Lemniscates.GrowthGen
import Mathlib.Topology.Order.IntermediateValue

/-!
# Case II with `R = 0`: the lemniscates are nested

If `R = Res_W(F₁, F₂)` vanishes identically, then for every `Z` with `f₁(Z) f₂(Z) ≠ 0` the two
equations have a common root `w` in `W` (`common_root`). Near a root `ζ` of `f₁ f₂`, `|g(w)|` is
large, so `w` is large and `|g₁(w)|^{n₂} ≍ |g₂(w)|^{n₁}`, i.e. `|f₂(Z)|^{n₁} ≍ |f₁(Z)|^{n₂}`
(`compare`). Comparing orders of vanishing at `ζ` gives `a n₂ = b n₁` for the multiplicities
(`local_exp`), so `f₁^{n₂} = f₂^{n₁}` (`pow_eq`). Then `|f₂| = |f₁|^{n₂/n₁}`, the two lemniscates
are nested, and a nonempty intersection is the whole of `Γ₁`, which is infinite
(`level_set_infinite`). So under the finiteness hypothesis the intersection is empty.
-/

open Polynomial ComplexConjugate

namespace Lemniscates.CaseII

open CaseI

lemma monic_upper (f : ℂ[X]) (hf : f.Monic) (hd : 0 < f.natDegree) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ w : ℂ, R ≤ ‖w‖ → ‖f.eval w‖ ≤ 2 * ‖w‖ ^ f.natDegree := by
  set n := f.natDegree
  set K := ∑ k ∈ Finset.range n, ‖f.coeff k‖
  refine ⟨max 1 (2 * K), le_max_left _ _, fun w hw => ?_⟩
  have hw1 : 1 ≤ ‖w‖ := le_trans (le_max_left _ _) hw
  have hK : 2 * K ≤ ‖w‖ := le_trans (le_max_right _ _) hw
  set s := ∑ k ∈ Finset.range n, f.coeff k * w ^ k
  have heval : f.eval w = w ^ n + s := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, one_mul, add_comm]
  have hlow : ‖s‖ ≤ K * ‖w‖ ^ (n - 1) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hw1 (by rw [Finset.mem_range] at hk; omega)) (norm_nonneg _)
  have hpow : ‖w‖ ^ n = ‖w‖ * ‖w‖ ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hp0 : 0 ≤ ‖w‖ ^ (n - 1) := pow_nonneg (norm_nonneg w) _
  have hKs : K * ‖w‖ ^ (n - 1) ≤ ‖w‖ ^ n / 2 := by rw [hpow]; nlinarith
  have : ‖f.eval w‖ ≤ ‖w‖ ^ n + ‖s‖ := by
    rw [heval]; exact (norm_add_le _ _).trans (by rw [norm_pow])
  have : 0 ≤ ‖w‖ ^ n := pow_nonneg (norm_nonneg w) _
  linarith

/-- If `t^p ≤ C t^q` for all small `t > 0`, then `q ≤ p`. -/
lemma exps_le (p q : ℕ) (C δ : ℝ) (hδ : 0 < δ)
    (h : ∀ t : ℝ, 0 < t → t < δ → t ^ p ≤ C * t ^ q) : q ≤ p := by
  by_contra hlt
  push Not at hlt
  set t := min (δ / 2) (min (1 / 2) (1 / (2 * (|C| + 1))))
  have ht0 : 0 < t := by positivity
  have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht1 : t ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have htC : t ≤ 1 / (2 * (|C| + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hC1 : 0 < |C| + 1 := by positivity
  have key := h t ht0 htδ
  have hq : t ^ q = t ^ p * t ^ (q - p) := by rw [← pow_add]; congr 1; omega
  have hqp : t ^ (q - p) ≤ t := by
    calc t ^ (q - p) ≤ t ^ 1 := pow_le_pow_of_le_one ht0.le (by linarith) (by omega)
      _ = t := pow_one t
  have htp : 0 < t ^ p := pow_pos ht0 p
  have h1 : t ^ p ≤ |C| * t ^ p * t := by
    calc t ^ p ≤ C * t ^ q := key
      _ ≤ |C| * t ^ q := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg ht0.le _)
      _ = |C| * t ^ p * t ^ (q - p) := by rw [hq]; ring
      _ ≤ |C| * t ^ p * t := mul_le_mul_of_nonneg_left hqp (by positivity)
  have h2 : (|C| + 1) * t ≤ 1 / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    calc (|C| + 1) * t * 2 = 2 * (|C| + 1) * t := by ring
      _ ≤ 2 * (|C| + 1) * (1 / (2 * (|C| + 1))) := by gcongr
      _ = 1 := by field_simp
  nlinarith [abs_nonneg C]

/-- `R = 0` gives a common root in `W` wherever `f₁ f₂ ≠ 0`. -/
lemma common_root (f₁ f₂ g₁ g₂ : ℂ[X]) (r₁ r₂ : ℂ)
    (hR : R f₁ f₂ g₁ g₂ r₁ r₂ = 0) (Z : ℂ) (hZ₁ : f₁.eval Z ≠ 0) (hZ₂ : f₂.eval Z ≠ 0) :
    ∃ w : ℂ, f₁.eval Z * g₁.eval w = r₁ ∧ f₂.eval Z * g₂.eval w = r₂ := by
  have h0 : (R f₁ f₂ g₁ g₂ r₁ r₂).eval Z = 0 := by rw [hR, eval_zero]
  rw [R, ← coe_evalRingHom, ← resultant_map_map] at h0
  change ((Fp f₁ g₁ r₁).map (atZ Z)).resultant ((Fp f₂ g₂ r₂).map (atZ Z)) _ _ = 0 at h0
  rw [Fp_map_atZ, Fp_map_atZ] at h0
  have hd₁ : (C (f₁.eval Z) * g₁ - C r₁).natDegree = g₁.natDegree := by
    rw [natDegree_sub_C, natDegree_C_mul hZ₁]
  have hd₂ : (C (f₂.eval Z) * g₂ - C r₂).natDegree = g₂.natDegree := by
    rw [natDegree_sub_C, natDegree_C_mul hZ₂]
  rw [← hd₁, ← hd₂, resultant_eq_zero_iff] at h0
  have := h0.2
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ] at this
  push Not at this
  obtain ⟨w, h₁, h₂⟩ := this
  refine ⟨w, ?_, ?_⟩
  · simpa [sub_eq_zero] using h₁
  · simpa [sub_eq_zero] using h₂

/-- Where one level value is small, `|y|^{m₁} ≍ |x|^{m₂}` for `x g₁(w) = r₁`, `y g₂(w) = r₂`. -/
lemma compare (g₁ g₂ : ℂ[X]) (hg₁ : g₁.Monic) (hg₂ : g₂.Monic) (hm₁ : 0 < g₁.natDegree)
    (hm₂ : 0 < g₂.natDegree) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    ∃ ε₁ > 0, ∃ ε₂ > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ x y w : ℂ, x * g₁.eval w = r₁ → y * g₂.eval w = r₂ →
      (‖x‖ < ε₁ ∨ ‖y‖ < ε₂) →
      ‖y‖ ^ g₁.natDegree ≤ K * ‖x‖ ^ g₂.natDegree ∧ ‖x‖ ^ g₂.natDegree ≤ K * ‖y‖ ^ g₁.natDegree := by
  set m₁ := g₁.natDegree
  set m₂ := g₂.natDegree
  obtain ⟨A₁, hA₁, hlow₁⟩ := GrowthGen.monic_lower g₁ hg₁ hm₁
  obtain ⟨A₂, hA₂, hlow₂⟩ := GrowthGen.monic_lower g₂ hg₂ hm₂
  obtain ⟨B₁, hB₁, hup₁⟩ := monic_upper g₁ hg₁ hm₁
  obtain ⟨B₂, hB₂, hup₂⟩ := monic_upper g₂ hg₂ hm₂
  set Rg := max (max A₁ B₁) (max A₂ B₂)
  obtain ⟨K₁, hK₁⟩ := (isCompact_closedBall (0 : ℂ) Rg).exists_bound_of_continuousOn
    g₁.continuous.continuousOn
  obtain ⟨K₂, hK₂⟩ := (isCompact_closedBall (0 : ℂ) Rg).exists_bound_of_continuousOn
    g₂.continuous.continuousOn
  set c := (2 : ℝ) ^ (m₁ + m₂)
  refine ⟨r₁ / (|K₁| + 1), by positivity, r₂ / (|K₂| + 1), by positivity,
    max (c * r₂ ^ m₁ / r₁ ^ m₂) (c * r₁ ^ m₂ / r₂ ^ m₁), le_max_of_le_left (by positivity),
    fun x y w hx hy hsmall => ?_⟩
  have hnx : ‖x‖ * ‖g₁.eval w‖ = r₁ := by
    rw [← norm_mul, hx, Complex.norm_real, Real.norm_of_nonneg hr₁.le]
  have hny : ‖y‖ * ‖g₂.eval w‖ = r₂ := by
    rw [← norm_mul, hy, Complex.norm_real, Real.norm_of_nonneg hr₂.le]
  -- `w` lies outside the disc where `g₁, g₂` are bounded
  have hw : Rg ≤ ‖w‖ := by
    by_contra hlt
    push Not at hlt
    have hb : w ∈ Metric.closedBall (0 : ℂ) Rg := by simpa using hlt.le
    rcases hsmall with h | h
    · have h1 : ‖g₁.eval w‖ ≤ |K₁| := (hK₁ w hb).trans (le_abs_self _)
      have h2 : ‖x‖ * (|K₁| + 1) < r₁ := by rwa [lt_div_iff₀ (by positivity)] at h
      nlinarith [norm_nonneg x, norm_nonneg (g₁.eval w)]
    · have h1 : ‖g₂.eval w‖ ≤ |K₂| := (hK₂ w hb).trans (le_abs_self _)
      have h2 : ‖y‖ * (|K₂| + 1) < r₂ := by rwa [lt_div_iff₀ (by positivity)] at h
      nlinarith [norm_nonneg y, norm_nonneg (g₂.eval w)]
  have hwA₁ : A₁ ≤ ‖w‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hw
  have hwB₁ : B₁ ≤ ‖w‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hw
  have hwA₂ : A₂ ≤ ‖w‖ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hw
  have hwB₂ : B₂ ≤ ‖w‖ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hw
  set N₁ := ‖g₁.eval w‖
  set N₂ := ‖g₂.eval w‖
  set W := ‖w‖
  have hW0 : 0 ≤ W := norm_nonneg w
  -- `N₁^{m₂} ≤ c N₂^{m₁}` and `N₂^{m₁} ≤ c N₁^{m₂}`
  have k₁ : N₁ ^ m₂ ≤ c * N₂ ^ m₁ := by
    have a1 : N₁ ^ m₂ ≤ (2 * W ^ m₁) ^ m₂ := pow_le_pow_left₀ (norm_nonneg _) (hup₁ w hwB₁) _
    have a2 : (W ^ m₂) ^ m₁ ≤ (2 * N₂) ^ m₁ :=
      pow_le_pow_left₀ (by positivity) (by linarith [hlow₂ w hwA₂]) _
    calc N₁ ^ m₂ ≤ (2 * W ^ m₁) ^ m₂ := a1
      _ = 2 ^ m₂ * (W ^ m₂) ^ m₁ := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m₁]
      _ ≤ 2 ^ m₂ * (2 * N₂) ^ m₁ := by gcongr
      _ = c * N₂ ^ m₁ := by rw [mul_pow, show c = 2 ^ m₁ * 2 ^ m₂ from pow_add 2 m₁ m₂]; ring
  have k₂ : N₂ ^ m₁ ≤ c * N₁ ^ m₂ := by
    have a1 : N₂ ^ m₁ ≤ (2 * W ^ m₂) ^ m₁ := pow_le_pow_left₀ (norm_nonneg _) (hup₂ w hwB₂) _
    have a2 : (W ^ m₁) ^ m₂ ≤ (2 * N₁) ^ m₂ :=
      pow_le_pow_left₀ (by positivity) (by linarith [hlow₁ w hwA₁]) _
    calc N₂ ^ m₁ ≤ (2 * W ^ m₂) ^ m₁ := a1
      _ = 2 ^ m₁ * (W ^ m₁) ^ m₂ := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m₂]
      _ ≤ 2 ^ m₁ * (2 * N₁) ^ m₂ := by gcongr
      _ = c * N₁ ^ m₂ := by rw [mul_pow, show c = 2 ^ m₁ * 2 ^ m₂ from pow_add 2 m₁ m₂]; ring
  have hr₁m : 0 < r₁ ^ m₂ := pow_pos hr₁ _
  have hr₂m : 0 < r₂ ^ m₁ := pow_pos hr₂ _
  constructor
  · -- `r₁^{m₂} ‖y‖^{m₁} ≤ c r₂^{m₁} ‖x‖^{m₂}`
    have : r₁ ^ m₂ * ‖y‖ ^ m₁ ≤ c * r₂ ^ m₁ * ‖x‖ ^ m₂ := by
      calc r₁ ^ m₂ * ‖y‖ ^ m₁ = ‖x‖ ^ m₂ * N₁ ^ m₂ * ‖y‖ ^ m₁ := by rw [← hnx, mul_pow]
        _ ≤ ‖x‖ ^ m₂ * (c * N₂ ^ m₁) * ‖y‖ ^ m₁ := by gcongr
        _ = c * (‖y‖ * N₂) ^ m₁ * ‖x‖ ^ m₂ := by rw [mul_pow]; ring
        _ = c * r₂ ^ m₁ * ‖x‖ ^ m₂ := by rw [hny]
    calc ‖y‖ ^ m₁ ≤ c * r₂ ^ m₁ / r₁ ^ m₂ * ‖x‖ ^ m₂ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hr₁m]; linarith
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have : r₂ ^ m₁ * ‖x‖ ^ m₂ ≤ c * r₁ ^ m₂ * ‖y‖ ^ m₁ := by
      calc r₂ ^ m₁ * ‖x‖ ^ m₂ = ‖y‖ ^ m₁ * N₂ ^ m₁ * ‖x‖ ^ m₂ := by rw [← hny, mul_pow]
        _ ≤ ‖y‖ ^ m₁ * (c * N₁ ^ m₂) * ‖x‖ ^ m₂ := by gcongr
        _ = c * (‖x‖ * N₁) ^ m₂ * ‖y‖ ^ m₁ := by rw [mul_pow]; ring
        _ = c * r₁ ^ m₂ * ‖y‖ ^ m₁ := by rw [hnx]
    calc ‖x‖ ^ m₂ ≤ c * r₁ ^ m₂ / r₂ ^ m₁ * ‖y‖ ^ m₁ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hr₂m]; linarith
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- A polynomial nonzero at `ζ` stays within a factor 2 of `|u(ζ)|` near `ζ` (real directions). -/
lemma near_nonzero (u : ℂ[X]) (ζ : ℂ) (hu : u.eval ζ ≠ 0) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ →
      ‖u.eval ζ‖ / 2 ≤ ‖u.eval (ζ + t)‖ ∧ ‖u.eval (ζ + t)‖ ≤ 2 * ‖u.eval ζ‖ := by
  set c := ‖u.eval ζ‖
  have hc : 0 < c := norm_pos_iff.mpr hu
  have hcont : Continuous fun t : ℝ => u.eval (ζ + t) :=
    u.continuous.comp (continuous_const.add Complex.continuous_ofReal)
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp hcont 0 (c / 2) (by positivity)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have := h t (by simpa [Real.dist_eq] using ht)
  simp only [Complex.ofReal_zero, add_zero, dist_eq_norm] at this
  have t1 := norm_sub_norm_le (u.eval (ζ + t)) (u.eval ζ)
  have t2 := norm_sub_norm_le (u.eval ζ) (u.eval (ζ + t))
  rw [norm_sub_rev] at t2
  constructor <;> linarith

/-- `f(ζ + t) = t^a u(ζ + t)` with `a` the multiplicity of `ζ`. -/
lemma eval_split (f : ℂ[X]) (hf : f ≠ 0) (ζ : ℂ) :
    ∃ u : ℂ[X], u.eval ζ ≠ 0 ∧ ∀ t : ℂ, f.eval (ζ + t) = t ^ rootMultiplicity ζ f * u.eval (ζ + t) := by
  obtain ⟨u, hfu, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf ζ
  refine ⟨u, fun h => hnd (dvd_iff_isRoot.mpr h), fun t => ?_⟩
  conv_lhs => rw [hfu]
  simp

/-- **Equal weighted orders.** -/
lemma local_exp (f₁ f₂ : ℂ[X]) (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) (m₁ m₂ : ℕ) (ζ : ℂ)
    (hab : 0 < rootMultiplicity ζ f₁ + rootMultiplicity ζ f₂) {ε₁ ε₂ K : ℝ} (hε₁ : 0 < ε₁)
    (hε₂ : 0 < ε₂) (hK : 0 ≤ K)
    (hcmp : ∀ Z, f₁.eval Z ≠ 0 → f₂.eval Z ≠ 0 → (‖f₁.eval Z‖ < ε₁ ∨ ‖f₂.eval Z‖ < ε₂) →
      ‖f₂.eval Z‖ ^ m₁ ≤ K * ‖f₁.eval Z‖ ^ m₂ ∧ ‖f₁.eval Z‖ ^ m₂ ≤ K * ‖f₂.eval Z‖ ^ m₁) :
    rootMultiplicity ζ f₁ * m₂ = rootMultiplicity ζ f₂ * m₁ := by
  set a := rootMultiplicity ζ f₁
  set b := rootMultiplicity ζ f₂
  obtain ⟨u₁, hu₁, hs₁⟩ := eval_split f₁ hf₁ ζ
  obtain ⟨u₂, hu₂, hs₂⟩ := eval_split f₂ hf₂ ζ
  obtain ⟨δ₁, hδ₁, hn₁⟩ := near_nonzero u₁ ζ hu₁
  obtain ⟨δ₂, hδ₂, hn₂⟩ := near_nonzero u₂ ζ hu₂
  set c₁ := ‖u₁.eval ζ‖
  set c₂ := ‖u₂.eval ζ‖
  have hc₁ : 0 < c₁ := norm_pos_iff.mpr hu₁
  have hc₂ : 0 < c₂ := norm_pos_iff.mpr hu₂
  set δ := min (min δ₁ δ₂) (min 1 (min (ε₁ / (2 * c₁ + 1)) (ε₂ / (2 * c₂ + 1))))
  have hδ : 0 < δ := by positivity
  -- the two-sided bound at `ζ + t`, `0 < t < δ`
  have key : ∀ t : ℝ, 0 < t → t < δ →
      t ^ (b * m₁) * (c₂ / 2) ^ m₁ ≤ K * (2 * c₁) ^ m₂ * t ^ (a * m₂) ∧
      t ^ (a * m₂) * (c₁ / 2) ^ m₂ ≤ K * (2 * c₂) ^ m₁ * t ^ (b * m₁) := by
    intro t ht htδ
    have htδ₁ : |t| < δ₁ := by
      rw [abs_of_pos ht]; exact lt_of_lt_of_le htδ (le_trans (min_le_left _ _) (min_le_left _ _))
    have htδ₂ : |t| < δ₂ := by
      rw [abs_of_pos ht]; exact lt_of_lt_of_le htδ (le_trans (min_le_left _ _) (min_le_right _ _))
    have ht1 : t ≤ 1 := le_trans htδ.le (le_trans (min_le_right _ _) (min_le_left _ _))
    have htε₁ : t < ε₁ / (2 * c₁ + 1) := lt_of_lt_of_le htδ
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have htε₂ : t < ε₂ / (2 * c₂ + 1) := lt_of_lt_of_le htδ
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    obtain ⟨l₁, u₁b⟩ := hn₁ t htδ₁
    obtain ⟨l₂, u₂b⟩ := hn₂ t htδ₂
    have hnt : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg ht.le]
    have e₁ : ‖f₁.eval (ζ + t)‖ = t ^ a * ‖u₁.eval (ζ + t)‖ := by
      rw [hs₁, norm_mul, norm_pow, hnt]
    have e₂ : ‖f₂.eval (ζ + t)‖ = t ^ b * ‖u₂.eval (ζ + t)‖ := by
      rw [hs₂, norm_mul, norm_pow, hnt]
    have hu₁t : 0 < ‖u₁.eval (ζ + t)‖ := by linarith
    have hu₂t : 0 < ‖u₂.eval (ζ + t)‖ := by linarith
    have hne₁ : f₁.eval (ζ + t) ≠ 0 := by
      rw [← norm_pos_iff, e₁]; positivity
    have hne₂ : f₂.eval (ζ + t) ≠ 0 := by
      rw [← norm_pos_iff, e₂]; positivity
    have hsmall : ‖f₁.eval (ζ + t)‖ < ε₁ ∨ ‖f₂.eval (ζ + t)‖ < ε₂ := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · right
        have hb : 1 ≤ b := by omega
        rw [e₂]
        have : t ^ b ≤ t := by
          calc t ^ b ≤ t ^ 1 := pow_le_pow_of_le_one ht.le ht1 hb
            _ = t := pow_one t
        have h3 : t * (2 * c₂ + 1) < ε₂ := by rwa [lt_div_iff₀ (by positivity)] at htε₂
        nlinarith [pow_nonneg ht.le b]
      · left
        rw [e₁]
        have : t ^ a ≤ t := by
          calc t ^ a ≤ t ^ 1 := pow_le_pow_of_le_one ht.le ht1 ha
            _ = t := pow_one t
        have h3 : t * (2 * c₁ + 1) < ε₁ := by rwa [lt_div_iff₀ (by positivity)] at htε₁
        nlinarith [pow_nonneg ht.le a]
    obtain ⟨i₁, i₂⟩ := hcmp _ hne₁ hne₂ hsmall
    rw [e₁, e₂, mul_pow, mul_pow, ← pow_mul, ← pow_mul] at i₁ i₂
    constructor
    · calc t ^ (b * m₁) * (c₂ / 2) ^ m₁ ≤ t ^ (b * m₁) * ‖u₂.eval (ζ + t)‖ ^ m₁ := by
            gcongr
        _ ≤ K * (t ^ (a * m₂) * ‖u₁.eval (ζ + t)‖ ^ m₂) := i₁
        _ ≤ K * (t ^ (a * m₂) * (2 * c₁) ^ m₂) := by gcongr
        _ = K * (2 * c₁) ^ m₂ * t ^ (a * m₂) := by ring
    · calc t ^ (a * m₂) * (c₁ / 2) ^ m₂ ≤ t ^ (a * m₂) * ‖u₁.eval (ζ + t)‖ ^ m₂ := by
            gcongr
        _ ≤ K * (t ^ (b * m₁) * ‖u₂.eval (ζ + t)‖ ^ m₁) := i₂
        _ ≤ K * (t ^ (b * m₁) * (2 * c₂) ^ m₁) := by gcongr
        _ = K * (2 * c₂) ^ m₁ * t ^ (b * m₁) := by ring
  have hp₁ : 0 < (c₂ / 2) ^ m₁ := by positivity
  have hp₂ : 0 < (c₁ / 2) ^ m₂ := by positivity
  have le₁ : a * m₂ ≤ b * m₁ := exps_le (b * m₁) (a * m₂) (K * (2 * c₁) ^ m₂ / (c₂ / 2) ^ m₁) δ hδ
    fun t ht htδ => by
      rw [div_mul_eq_mul_div, le_div_iff₀ hp₁]
      have := (key t ht htδ).1
      linarith
  have le₂ : b * m₁ ≤ a * m₂ := exps_le (a * m₂) (b * m₁) (K * (2 * c₂) ^ m₁ / (c₁ / 2) ^ m₂) δ hδ
    fun t ht htδ => by
      rw [div_mul_eq_mul_div, le_div_iff₀ hp₂]
      have := (key t ht htδ).2
      linarith
  omega

/-- **`R = 0` forces `f₁^{n₂} = f₂^{n₁}`.** -/
theorem pow_eq {f₁ f₂ : ℂ[X]} (hf₁ : f₁.Monic) (hf₂ : f₂.Monic) (hn₁ : 0 < f₁.natDegree)
    (hn₂ : 0 < f₂.natDegree) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hR : R f₁ f₂ (conjP f₁) (conjP f₂) r₁ r₂ = 0) :
    f₁ ^ f₂.natDegree = f₂ ^ f₁.natDegree := by
  classical
  obtain ⟨ε₁, hε₁, ε₂, hε₂, K, hK, hcmp⟩ := compare (conjP f₁) (conjP f₂) (conjP_monic hf₁)
    (conjP_monic hf₂) (by rw [conjP_natDegree]; exact hn₁) (by rw [conjP_natDegree]; exact hn₂)
    hr₁ hr₂
  rw [conjP_natDegree, conjP_natDegree] at hcmp
  have hcmp' : ∀ Z, f₁.eval Z ≠ 0 → f₂.eval Z ≠ 0 → (‖f₁.eval Z‖ < ε₁ ∨ ‖f₂.eval Z‖ < ε₂) →
      ‖f₂.eval Z‖ ^ f₁.natDegree ≤ K * ‖f₁.eval Z‖ ^ f₂.natDegree ∧
      ‖f₁.eval Z‖ ^ f₂.natDegree ≤ K * ‖f₂.eval Z‖ ^ f₁.natDegree := by
    intro Z h₁ h₂ hs
    obtain ⟨w, e₁, e₂⟩ := common_root f₁ f₂ (conjP f₁) (conjP f₂) r₁ r₂ hR Z h₁ h₂
    exact hcmp _ _ w e₁ e₂ hs
  have hmult : ∀ ζ, rootMultiplicity ζ f₁ * f₂.natDegree = rootMultiplicity ζ f₂ * f₁.natDegree := by
    intro ζ
    rcases Nat.eq_zero_or_pos (rootMultiplicity ζ f₁ + rootMultiplicity ζ f₂) with h | h
    · have h1 : rootMultiplicity ζ f₁ = 0 := by omega
      have h2 : rootMultiplicity ζ f₂ = 0 := by omega
      rw [h1, h2, zero_mul, zero_mul]
    · exact local_exp f₁ f₂ hf₁.ne_zero hf₂.ne_zero _ _ ζ h hε₁ hε₂ hK hcmp'
  have hroots : (f₁ ^ f₂.natDegree).roots = (f₂ ^ f₁.natDegree).roots := by
    rw [roots_pow, roots_pow]
    ext ζ
    rw [Multiset.count_nsmul, Multiset.count_nsmul, count_roots, count_roots, mul_comm,
      hmult ζ, mul_comm]
  have e₁ := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := f₁ ^ f₂.natDegree))
  have e₂ := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := f₂ ^ f₁.natDegree))
  rw [(hf₁.pow _).leadingCoeff, C_1, one_mul] at e₁
  rw [(hf₂.pow _).leadingCoeff, C_1, one_mul] at e₂
  rw [← e₁, ← e₂, hroots]

/-- **Nested lemniscates.** -/
lemma nested {f₁ f₂ : ℂ[X]} (hpow : f₁ ^ f₂.natDegree = f₂ ^ f₁.natDegree)
    (hn₁ : 0 < f₁.natDegree) {r₁ r₂ : ℝ} {z₀ : ℂ} (h₀ : ‖f₁.eval z₀‖ ^ 2 = r₁ ∧ ‖f₂.eval z₀‖ ^ 2 = r₂)
    {z : ℂ} (hz : ‖f₁.eval z‖ ^ 2 = r₁) : ‖f₂.eval z‖ ^ 2 = r₂ := by
  have key : ∀ x : ℂ, (‖f₁.eval x‖ ^ 2) ^ f₂.natDegree = (‖f₂.eval x‖ ^ 2) ^ f₁.natDegree := by
    intro x
    have := congrArg (fun p => ‖p.eval x‖ ^ 2) hpow
    simp only [eval_pow, norm_pow] at this
    rw [← pow_mul, ← pow_mul, mul_comm 2, mul_comm 2, pow_mul, pow_mul, this]
  have h1 := key z₀
  have h2 := key z
  rw [h₀.1, h₀.2] at h1
  rw [hz, h1] at h2
  have hr₂ : 0 ≤ r₂ := h₀.2 ▸ by positivity
  exact (pow_left_inj₀ (by positivity) hr₂ hn₁.ne').mp h2.symm

/-- A lemniscate `‖f‖² = r` (`f` nonconstant monic, `r > 0`) is infinite. -/
theorem level_set_infinite (f : ℂ[X]) (hf : f.Monic) (hd : 0 < f.natDegree) {r : ℝ} (hr : 0 < r) :
    {z : ℂ | ‖f.eval z‖ ^ 2 = r}.Infinite := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root f
    (by rw [degree_eq_natDegree hf.ne_zero]; exact_mod_cast hd.ne')
  -- near `ζ` (horizontally) the value is below `r`
  have hcont : Continuous fun x : ℝ => ‖f.eval (ζ + x)‖ ^ 2 :=
    ((f.continuous.comp (continuous_const.add Complex.continuous_ofReal)).norm).pow 2
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuous_iff.mp hcont 0 r hr
  have hlt : ∀ x : ℝ, |x| < δ → ‖f.eval (ζ + x)‖ ^ 2 < r := by
    intro x hx
    have := hsmall x (by simpa [Real.dist_eq] using hx)
    simp only [Complex.ofReal_zero, add_zero, hζ.eq_zero, norm_zero, Real.dist_eq] at this
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h0, sub_zero, abs_of_nonneg (by positivity)] at this
    exact this
  -- far up, the value exceeds `r`
  obtain ⟨A, hA1, hlow⟩ := GrowthGen.monic_lower f hf hd
  set Y := A + ‖ζ‖ + δ + 2 * Real.sqrt r + 2
  have hY : 0 ≤ Y := by positivity
  have hbig : ∀ x : ℝ, |x| < δ → r ≤ ‖f.eval (ζ + x + Y * Complex.I)‖ ^ 2 := by
    intro x hx
    set w := ζ + x + Y * Complex.I
    have hw : Y - ‖ζ‖ - |x| ≤ ‖w‖ := by
      have h1 : ‖(Y : ℂ) * Complex.I‖ = Y := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hY]
      have h2 : ‖ζ + (x : ℂ)‖ ≤ ‖ζ‖ + |x| := by
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
      have h3 := norm_sub_norm_le ((Y : ℂ) * Complex.I) (-(ζ + x))
      rw [sub_neg_eq_add, norm_neg, h1] at h3
      have : (Y : ℂ) * Complex.I + (ζ + x) = w := by simp only [w]; ring
      rw [this] at h3
      linarith
    have hwA : A ≤ ‖w‖ := by
      have := Real.sqrt_nonneg r
      linarith
    have hw1 : 1 ≤ ‖w‖ := le_trans hA1 hwA
    have hfw := hlow w hwA
    have hp : ‖w‖ ≤ ‖w‖ ^ f.natDegree := le_self_pow₀ hw1 hd.ne'
    have hs : Real.sqrt r + 1 ≤ ‖f.eval w‖ := by
      have := Real.sqrt_nonneg r
      linarith
    have hsq : r ≤ (Real.sqrt r + 1) ^ 2 := by
      have := Real.sq_sqrt hr.le
      nlinarith [Real.sqrt_nonneg r]
    calc r ≤ (Real.sqrt r + 1) ^ 2 := hsq
      _ ≤ ‖f.eval w‖ ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
  -- intermediate value theorem on each vertical segment
  have hpt : ∀ x : Set.Ioo (-δ) δ, ∃ y : ℝ, ‖f.eval (ζ + (x : ℝ) + y * Complex.I)‖ ^ 2 = r := by
    intro ⟨x, hx⟩
    have hxδ : |x| < δ := abs_lt.mpr hx
    have hk : Continuous fun y : ℝ => ‖f.eval (ζ + x + y * Complex.I)‖ ^ 2 :=
      ((f.continuous.comp (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))).norm).pow 2
    have hivt := intermediate_value_Icc hY hk.continuousOn
    obtain ⟨y, -, hy⟩ := hivt ⟨by simpa using (hlt x hxδ).le, hbig x hxδ⟩
    exact ⟨y, hy⟩
  choose y hy using hpt
  have : Infinite (Set.Ioo (-δ) δ) := (Set.Ioo_infinite (by linarith)).to_subtype
  refine Set.infinite_of_injective_forall_mem (f := fun x : Set.Ioo (-δ) δ =>
    ζ + (x : ℝ) + y x * Complex.I) (fun a b hab => ?_) (fun x => hy x)
  have := congrArg Complex.re hab
  simp at this
  exact Subtype.ext this

/-- **Case II with `R = 0`.** A finite intersection is empty. -/
theorem empty_of_R_eq_zero {f₁ f₂ : ℂ[X]} (hf₁ : f₁.Monic) (hf₂ : f₂.Monic)
    (hn₁ : 0 < f₁.natDegree) (hn₂ : 0 < f₂.natDegree) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hR : R f₁ f₂ (conjP f₁) (conjP f₂) r₁ r₂ = 0)
    (hfin : {z : ℂ | ‖f₁.eval z‖ ^ 2 = r₁ ∧ ‖f₂.eval z‖ ^ 2 = r₂}.Finite) :
    {z : ℂ | ‖f₁.eval z‖ ^ 2 = r₁ ∧ ‖f₂.eval z‖ ^ 2 = r₂} = ∅ := by
  by_contra hne
  obtain ⟨z₀, h₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hpow := pow_eq hf₁ hf₂ hn₁ hn₂ hr₁ hr₂ hR
  have heq : {z : ℂ | ‖f₁.eval z‖ ^ 2 = r₁ ∧ ‖f₂.eval z‖ ^ 2 = r₂} =
      {z : ℂ | ‖f₁.eval z‖ ^ 2 = r₁} := by
    ext z
    exact ⟨fun h => h.1, fun h => ⟨h, nested hpow hn₁ h₀ h⟩⟩
  rw [heq] at hfin
  exact level_set_infinite f₁ hf₁ hn₁ hr₁ hfin

end Lemniscates.CaseII
