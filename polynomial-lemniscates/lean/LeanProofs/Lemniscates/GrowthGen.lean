import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Growth in all degrees (Lemma 5)

The solutions of `f(Z) g(W) = c`, `f'(Z) g'(W) = r` satisfy
`‖(Z - m)(W - m')‖ ≤ A + B √‖c‖` (`growth_level`), and the solutions of `f₁(Z) g₁(W) = 0`,
`f₂(Z) g₂(W) = d` satisfy the same bound in `d` (`growth_zero`). Degrees of `f, g` (resp.
`f₂, g₂`) are at least 2; this is where `n ≥ 2` enters.

Ingredients:
* `monic_lower`: a monic `f` of degree `n ≥ 1` has `‖f(Z)‖ ≥ ‖Z‖ⁿ / 2` for large `‖Z‖`;
* `coprime_lower`: coprime `p, q` are not simultaneously small on a disc (from `u p + v q = 1`);
* `one_side`: if `W` stays in a disc, then `‖Z‖ ≤ A + B √‖c‖`. For large `Z`, `g'(W)` is small,
  so `g(W)` is not, and `‖c‖ = ‖f(Z)‖ ‖g(W)‖ ≥ ‖Z‖² δ / 2`.
-/

open Polynomial

namespace Lemniscates.GrowthGen

lemma monic_lower (f : ℂ[X]) (hf : f.Monic) (hd : 0 < f.natDegree) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ Z : ℂ, R ≤ ‖Z‖ → ‖Z‖ ^ f.natDegree / 2 ≤ ‖f.eval Z‖ := by
  set n := f.natDegree
  set K := ∑ k ∈ Finset.range n, ‖f.coeff k‖
  refine ⟨max 1 (2 * K), le_max_left _ _, fun Z hZ => ?_⟩
  have hZ1 : 1 ≤ ‖Z‖ := le_trans (le_max_left _ _) hZ
  have hK : 2 * K ≤ ‖Z‖ := le_trans (le_max_right _ _) hZ
  set s := ∑ k ∈ Finset.range n, f.coeff k * Z ^ k
  have heval : f.eval Z = Z ^ n + s := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, one_mul, add_comm]
  have hlow : ‖s‖ ≤ K * ‖Z‖ ^ (n - 1) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hZ1 (by rw [Finset.mem_range] at hk; omega)) (norm_nonneg _)
  have hpow : ‖Z‖ ^ n = ‖Z‖ * ‖Z‖ ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hp0 : 0 ≤ ‖Z‖ ^ (n - 1) := pow_nonneg (norm_nonneg Z) _
  have hKs : K * ‖Z‖ ^ (n - 1) ≤ ‖Z‖ ^ n / 2 := by rw [hpow]; nlinarith
  have htri : ‖Z ^ n‖ ≤ ‖f.eval Z‖ + ‖s‖ := by
    rw [heval]
    calc ‖Z ^ n‖ = ‖(Z ^ n + s) + -s‖ := by ring_nf
      _ ≤ ‖Z ^ n + s‖ + ‖-s‖ := norm_add_le _ _
      _ = ‖Z ^ n + s‖ + ‖s‖ := by rw [norm_neg]
  rw [norm_pow] at htri
  linarith

lemma coprime_lower (p q : ℂ[X]) (h : IsCoprime p q) (R : ℝ) :
    ∃ δ > 0, ∀ Z : ℂ, ‖Z‖ ≤ R → δ ≤ ‖p.eval Z‖ ∨ δ ≤ ‖q.eval Z‖ := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    u.continuous.continuousOn
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    v.continuous.continuousOn
  set K' := max (max K L) 1
  have hK'1 : 1 ≤ K' := le_max_right _ _
  refine ⟨1 / (4 * K'), by positivity, fun Z hZ => ?_⟩
  by_contra hcon
  push Not at hcon
  have hZb : Z ∈ Metric.closedBall (0 : ℂ) R := by simpa using hZ
  have hu : ‖u.eval Z‖ ≤ K' := (hK Z hZb).trans (le_trans (le_max_left _ _) (le_max_left _ _))
  have hv : ‖v.eval Z‖ ≤ K' := (hL Z hZb).trans (le_trans (le_max_right _ _) (le_max_left _ _))
  have h1 : u.eval Z * p.eval Z + v.eval Z * q.eval Z = 1 := by
    have := congrArg (eval Z) huv
    simpa using this
  have h2 : (1 : ℝ) ≤ K' * ‖p.eval Z‖ + K' * ‖q.eval Z‖ := by
    calc (1 : ℝ) = ‖u.eval Z * p.eval Z + v.eval Z * q.eval Z‖ := by rw [h1, norm_one]
      _ ≤ ‖u.eval Z‖ * ‖p.eval Z‖ + ‖v.eval Z‖ * ‖q.eval Z‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ K' * ‖p.eval Z‖ + K' * ‖q.eval Z‖ := by gcongr
  have h3 : K' * ‖p.eval Z‖ < 1 / 4 := by
    calc K' * ‖p.eval Z‖ < K' * (1 / (4 * K')) := by gcongr; linarith
      _ = 1 / 4 := by field_simp
  have h4 : K' * ‖q.eval Z‖ < 1 / 4 := by
    calc K' * ‖q.eval Z‖ < K' * (1 / (4 * K')) := by gcongr; linarith
      _ = 1 / 4 := by field_simp
  linarith

/-- **One-sided bound.** If `W` stays in a disc, `‖Z‖ ≤ A + B √‖c‖`. -/
theorem one_side (f g f' g' : ℂ[X]) (r : ℂ) (hf : f.Monic) (hf' : f'.Monic)
    (hn : 2 ≤ f.natDegree) (hn' : 0 < f'.natDegree) (hg : IsCoprime g' g) (R₀ : ℝ) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ c Z W : ℂ, f.eval Z * g.eval W = c → f'.eval Z * g'.eval W = r →
      ‖W‖ ≤ R₀ → ‖Z‖ ≤ A + B * Real.sqrt ‖c‖ := by
  obtain ⟨δ, hδ, hsep⟩ := coprime_lower g' g hg R₀
  obtain ⟨Rf, hRf1, hRf⟩ := monic_lower f hf (by omega)
  obtain ⟨Rf', hRf'1, hRf'⟩ := monic_lower f' hf' hn'
  set R₃ := max (max Rf Rf') (4 * ‖r‖ / δ + 1)
  have hR₃f : Rf ≤ R₃ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hR₃f' : Rf' ≤ R₃ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hR₃r : 4 * ‖r‖ / δ + 1 ≤ R₃ := le_max_right _ _
  refine ⟨R₃, Real.sqrt (2 / δ), Real.sqrt_nonneg _, fun c Z W h₁ h₂ hW => ?_⟩
  have hB : 0 ≤ Real.sqrt (2 / δ) * Real.sqrt ‖c‖ := by positivity
  by_cases hZ : ‖Z‖ ≤ R₃
  · linarith
  push Not at hZ
  have hZ1 : 1 ≤ ‖Z‖ := by linarith
  -- `‖f'(Z)‖ ≥ ‖Z‖ / 2`
  have hf'Z : ‖Z‖ / 2 ≤ ‖f'.eval Z‖ := by
    have := hRf' Z (by linarith)
    have hp : ‖Z‖ ≤ ‖Z‖ ^ f'.natDegree := le_self_pow₀ hZ1 hn'.ne'
    linarith
  -- so `g'(W)` is small and `g(W)` is not
  have hg'W : ‖g'.eval W‖ < δ := by
    by_contra hcon
    push Not at hcon
    have hr : ‖r‖ = ‖f'.eval Z‖ * ‖g'.eval W‖ := by rw [← h₂, norm_mul]
    have h4 : 4 * ‖r‖ / δ < ‖Z‖ := by linarith
    have h5 : 4 * ‖r‖ < ‖Z‖ * δ := by rwa [div_lt_iff₀ hδ] at h4
    have : ‖Z‖ / 2 * δ ≤ ‖r‖ := by
      rw [hr]
      exact mul_le_mul hf'Z hcon hδ.le (norm_nonneg _)
    nlinarith [norm_nonneg r]
  have hgW : δ ≤ ‖g.eval W‖ := (hsep W hW).resolve_left (not_le.mpr hg'W)
  -- `‖c‖ ≥ ‖Z‖² δ / 2`
  have hfZ : ‖Z‖ ^ 2 / 2 ≤ ‖f.eval Z‖ := by
    have := hRf Z (by linarith)
    have hp : ‖Z‖ ^ 2 ≤ ‖Z‖ ^ f.natDegree := pow_le_pow_right₀ hZ1 hn
    linarith
  have hc : ‖Z‖ ^ 2 ≤ 2 / δ * ‖c‖ := by
    have : ‖Z‖ ^ 2 / 2 * δ ≤ ‖c‖ := by
      rw [← h₁, norm_mul]
      exact mul_le_mul hfZ hgW hδ.le (norm_nonneg _)
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    linarith
  have hZc : ‖Z‖ ≤ Real.sqrt (2 / δ) * Real.sqrt ‖c‖ := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq (norm_nonneg Z)]
    exact Real.sqrt_le_sqrt hc
  have : 0 ≤ R₃ := by linarith
  linarith

/-- Combining the two one-sided bounds. -/
lemma combine (Sol : ℂ → ℂ → ℂ → Prop) (R₀ A₁ B₁ A₂ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (h₁ : ∀ c Z W, Sol c Z W → ‖W‖ ≤ R₀ → ‖Z‖ ≤ A₁ + B₁ * Real.sqrt ‖c‖)
    (h₂ : ∀ c Z W, Sol c Z W → ‖Z‖ ≤ R₀ → ‖W‖ ≤ A₂ + B₂ * Real.sqrt ‖c‖)
    (h₀ : ∀ c Z W, Sol c Z W → ‖Z‖ ≤ R₀ ∨ ‖W‖ ≤ R₀) (m m' : ℂ) :
    ∃ A B : ℝ, ∀ c Z W, Sol c Z W → ‖(Z - m) * (W - m')‖ ≤ A + B * Real.sqrt ‖c‖ := by
  set P := |A₁| + |A₂| + |R₀| + ‖m‖ + ‖m'‖ + 1
  have hP : 0 ≤ P := by positivity
  refine ⟨P * P, P * (B₁ + B₂), fun c Z W hs => ?_⟩
  set s := Real.sqrt ‖c‖
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hφ : ‖(Z - m) * (W - m')‖ ≤ (‖Z‖ + ‖m‖) * (‖W‖ + ‖m'‖) := by
    rw [norm_mul]
    exact mul_le_mul (norm_sub_le _ _) (norm_sub_le _ _) (norm_nonneg _) (by positivity)
  have hA₁ := le_abs_self A₁
  have hA₂ := le_abs_self A₂
  have hR₀ := le_abs_self R₀
  have hm := norm_nonneg m
  have hm' := norm_nonneg m'
  rcases h₀ c Z W hs with hZ | hW
  · have hW := h₂ c Z W hs hZ
    have e1 : ‖Z‖ + ‖m‖ ≤ P := by simp only [P]; linarith [abs_nonneg A₁, abs_nonneg A₂]
    have e2 : ‖W‖ + ‖m'‖ ≤ P + (B₁ + B₂) * s := by
      simp only [P]; nlinarith [abs_nonneg A₁, abs_nonneg R₀]
    calc ‖(Z - m) * (W - m')‖ ≤ (‖Z‖ + ‖m‖) * (‖W‖ + ‖m'‖) := hφ
      _ ≤ P * (P + (B₁ + B₂) * s) := mul_le_mul e1 e2 (by positivity) hP
      _ = P * P + P * (B₁ + B₂) * s := by ring
  · have hZ := h₁ c Z W hs hW
    have e1 : ‖Z‖ + ‖m‖ ≤ P + (B₁ + B₂) * s := by
      simp only [P]; nlinarith [abs_nonneg A₂, abs_nonneg R₀]
    have e2 : ‖W‖ + ‖m'‖ ≤ P := by simp only [P]; linarith [abs_nonneg A₁, abs_nonneg A₂]
    calc ‖(Z - m) * (W - m')‖ ≤ (‖Z‖ + ‖m‖) * (‖W‖ + ‖m'‖) := hφ
      _ ≤ (P + (B₁ + B₂) * s) * P := mul_le_mul e1 e2 (by positivity) (by positivity)
      _ = P * P + P * (B₁ + B₂) * s := by ring

/-- **Lemma 5, first deformation**: `f(Z) g(W) = c`, `f'(Z) g'(W) = r`. -/
theorem growth_level (f g f' g' : ℂ[X]) (r : ℂ) (hf : f.Monic) (hg : g.Monic) (hf' : f'.Monic)
    (hg' : g'.Monic) (hn : 2 ≤ f.natDegree) (hm : 2 ≤ g.natDegree) (hn' : 0 < f'.natDegree)
    (hm' : 0 < g'.natDegree) (cf : IsCoprime f' f) (cg : IsCoprime g' g) (m m' : ℂ) :
    ∃ A B : ℝ, ∀ c Z W : ℂ, f.eval Z * g.eval W = c → f'.eval Z * g'.eval W = r →
      ‖(Z - m) * (W - m')‖ ≤ A + B * Real.sqrt ‖c‖ := by
  obtain ⟨Ra, hRa1, hRa⟩ := monic_lower f' hf' hn'
  obtain ⟨Rb, hRb1, hRb⟩ := monic_lower g' hg' hm'
  set R₀ := max (max Ra Rb) (2 * ‖r‖ + 2)
  obtain ⟨A₁, B₁, hB₁, h₁⟩ := one_side f g f' g' r hf hf' hn hn' cg R₀
  obtain ⟨A₂, B₂, hB₂, h₂⟩ := one_side g f g' f' r hg hg' hm hm' cf R₀
  suffices h : ∃ A B : ℝ, ∀ c Z W : ℂ, (f.eval Z * g.eval W = c ∧ f'.eval Z * g'.eval W = r) →
      ‖(Z - m) * (W - m')‖ ≤ A + B * Real.sqrt ‖c‖ by
    obtain ⟨A, B, h⟩ := h; exact ⟨A, B, fun c Z W h₁ h₂ => h c Z W ⟨h₁, h₂⟩⟩
  refine combine (fun c Z W => f.eval Z * g.eval W = c ∧ f'.eval Z * g'.eval W = r) R₀ A₁ B₁
    A₂ B₂ hB₁ hB₂ (fun c Z W hs hW => h₁ c Z W hs.1 hs.2 hW)
    (fun c Z W hs hZ => h₂ c W Z (by rw [mul_comm]; exact hs.1) (by rw [mul_comm]; exact hs.2) hZ)
    (fun c Z W hs => ?_) m m'
  -- both large is impossible: `‖r‖ = ‖f'(Z)‖ ‖g'(W)‖ ≥ (‖r‖ + 1)²`
  by_contra hcon
  push Not at hcon
  obtain ⟨hZ, hW⟩ := hcon
  have hRa' : Ra ≤ R₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRb' : Rb ≤ R₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hRr : 2 * ‖r‖ + 2 ≤ R₀ := le_max_right _ _
  have hZ1 : 1 ≤ ‖Z‖ := by linarith
  have hW1 : 1 ≤ ‖W‖ := by linarith
  have ha : ‖r‖ + 1 ≤ ‖f'.eval Z‖ := by
    have := hRa Z (by linarith)
    have hp : ‖Z‖ ≤ ‖Z‖ ^ f'.natDegree := le_self_pow₀ hZ1 hn'.ne'
    linarith
  have hb : ‖r‖ + 1 ≤ ‖g'.eval W‖ := by
    have := hRb W (by linarith)
    have hp : ‖W‖ ≤ ‖W‖ ^ g'.natDegree := le_self_pow₀ hW1 hm'.ne'
    linarith
  have hr : ‖r‖ = ‖f'.eval Z‖ * ‖g'.eval W‖ := by rw [← hs.2, norm_mul]
  nlinarith [norm_nonneg r]

/-- **Lemma 5, second deformation**: `f₁(Z) g₁(W) = 0`, `f₂(Z) g₂(W) = d`. -/
theorem growth_zero (f₁ g₁ f₂ g₂ : ℂ[X]) (hf₁ : f₁.Monic) (hg₁ : g₁.Monic) (hf₂ : f₂.Monic)
    (hg₂ : g₂.Monic) (hn₁ : 0 < f₁.natDegree) (hm₁ : 0 < g₁.natDegree) (hn₂ : 2 ≤ f₂.natDegree)
    (hm₂ : 2 ≤ g₂.natDegree) (cf : IsCoprime f₁ f₂) (cg : IsCoprime g₁ g₂) (m m' : ℂ) :
    ∃ A B : ℝ, ∀ d Z W : ℂ, f₁.eval Z * g₁.eval W = 0 → f₂.eval Z * g₂.eval W = d →
      ‖(Z - m) * (W - m')‖ ≤ A + B * Real.sqrt ‖d‖ := by
  obtain ⟨Ra, hRa1, hRa⟩ := monic_lower f₁ hf₁ hn₁
  obtain ⟨Rb, hRb1, hRb⟩ := monic_lower g₁ hg₁ hm₁
  set R₀ := max Ra Rb
  -- `g₁(W) = 0` bounds `W`; then `Z` is controlled by the second equation
  obtain ⟨A₁, B₁, hB₁, h₁⟩ := one_side f₂ g₂ f₁ g₁ 0 hf₂ hf₁ hn₂ hn₁ cg R₀
  obtain ⟨A₂, B₂, hB₂, h₂⟩ := one_side g₂ f₂ g₁ f₁ 0 hg₂ hg₁ hm₂ hm₁ cf R₀
  suffices h : ∃ A B : ℝ, ∀ d Z W : ℂ, (f₁.eval Z * g₁.eval W = 0 ∧ f₂.eval Z * g₂.eval W = d) →
      ‖(Z - m) * (W - m')‖ ≤ A + B * Real.sqrt ‖d‖ by
    obtain ⟨A, B, h⟩ := h; exact ⟨A, B, fun d Z W h₁ h₂ => h d Z W ⟨h₁, h₂⟩⟩
  refine combine (fun d Z W => f₁.eval Z * g₁.eval W = 0 ∧ f₂.eval Z * g₂.eval W = d) R₀ A₁ B₁
    A₂ B₂ hB₁ hB₂ (fun d Z W hs hW => h₁ d Z W hs.2 hs.1 hW)
    (fun d Z W hs hZ => h₂ d W Z (by rw [mul_comm]; exact hs.2) (by rw [mul_comm]; exact hs.1) hZ)
    (fun d Z W hs => ?_) m m'
  -- a root of a monic polynomial lies in the disc where it is not yet large
  rcases mul_eq_zero.mp hs.1 with h | h
  · left
    by_contra hZ
    push Not at hZ
    have := hRa Z (le_trans (le_max_left _ _) hZ.le)
    rw [h, norm_zero] at this
    have : 0 < ‖Z‖ ^ f₁.natDegree / 2 := by
      have : 0 < ‖Z‖ := by linarith [le_max_left Ra Rb]
      positivity
    linarith
  · right
    by_contra hW
    push Not at hW
    have := hRb W (le_trans (le_max_right _ _) hW.le)
    rw [h, norm_zero] at this
    have : 0 < ‖W‖ ^ g₁.natDegree / 2 := by
      have : 0 < ‖W‖ := by linarith [le_max_right Ra Rb]
      positivity
    linarith

end Lemniscates.GrowthGen
