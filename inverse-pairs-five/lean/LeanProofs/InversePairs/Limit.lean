import LeanProofs.InversePairs.Bound

/-!
# Inverse pairs: `S(p) → 5` (Theorem 1)

With `L = ⌈p^{1/4}⌉`, `h = ⌈p^{3/4}⌉`, `Y = ⌈p^{7/4}⌉` in `main_ineq`, the divisor bound with
exponent `ε/4`, and `log p ≤ p^{ε/2}/(ε/2)`, every error term is at most a constant times
`p^{-1/8+ε}`.
* `rate`: given Weil's bound for every prime, for every `ε > 0` there is `K` with
  `|S p - 5| ≤ K p^{-1/8+ε}` for every prime `p`;
* `tendsto_five`: `S p → 5` along the primes.
-/

open Finset Real Filter Topology

namespace InversePairs

lemma ceil_le_two {y : ℝ} (hy : 1 ≤ y) : (⌈y⌉₊ : ℝ) ≤ 2 * y := by
  have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ y); linarith

section Params

variable {x : ℝ} (hx1 : 1 ≤ x)
include hx1

lemma one_add_log_le {ε : ℝ} (hε : 0 < ε) :
    1 + Real.log x ≤ (1 + 2 / ε) * x ^ (ε / 2) := by
  have h1 : Real.log x ≤ x ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div (by linarith) (by linarith)
  have h2 : (1 : ℝ) ≤ x ^ (ε / 2) := Real.one_le_rpow hx1 (by linarith)
  have e : x ^ (ε / 2) / (ε / 2) = 2 / ε * x ^ (ε / 2) := by field_simp
  rw [e] at h1
  nlinarith

lemma w_ceil_le : w ⌈x ^ (7 / 4 : ℝ)⌉₊ ≤ x ^ (-7 / 8 : ℝ) := by
  have hx0 : 0 < x := by linarith
  simp only [w]
  have hsY : x ^ (7 / 8 : ℝ) ≤ Real.sqrt ⌈x ^ (7 / 4 : ℝ)⌉₊ := by
    have e : x ^ (7 / 8 : ℝ) = Real.sqrt (x ^ (7 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; norm_num
    rw [e]; exact Real.sqrt_le_sqrt (Nat.le_ceil _)
  have h0 : 0 < x ^ (7 / 8 : ℝ) := Real.rpow_pos_of_pos hx0 _
  calc 1 / Real.sqrt ⌈x ^ (7 / 4 : ℝ)⌉₊ ≤ 1 / x ^ (7 / 8 : ℝ) := one_div_le_one_div_of_le h0 hsY
    _ = x ^ (-7 / 8 : ℝ) := by
        rw [show (-7 / 8 : ℝ) = -(7 / 8) by norm_num, Real.rpow_neg hx0.le, one_div]

lemma sqrt_ceil_le : Real.sqrt ⌈x ^ (7 / 4 : ℝ)⌉₊ ≤ 2 * x ^ (7 / 8 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hq7 : (1 : ℝ) ≤ x ^ (7 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hY2 := ceil_le_two hq7
  have hs : Real.sqrt (x ^ (7 / 4 : ℝ)) = x ^ (7 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; norm_num
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc Real.sqrt ⌈x ^ (7 / 4 : ℝ)⌉₊ ≤ Real.sqrt (4 * x ^ (7 / 4 : ℝ)) :=
        Real.sqrt_le_sqrt (by linarith)
    _ = 2 * x ^ (7 / 8 : ℝ) := by rw [Real.sqrt_mul (by norm_num), hs, h4]

/-- Term 1: `(L · 3 x^{1/2} G² + h + 1) w(Y) ≤ (6 G² + 3) x^{-1/8}`. -/
lemma term1 (G : ℝ) :
    ((⌈x ^ (1 / 4 : ℝ)⌉₊ : ℝ) * (3 * x ^ (1 / 2 : ℝ) * G ^ 2) + ⌈x ^ (3 / 4 : ℝ)⌉₊ + 1) *
      w ⌈x ^ (7 / 4 : ℝ)⌉₊ ≤ (6 * G ^ 2 + 3) * x ^ (-1 / 8 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hq1 : (1 : ℝ) ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hq3 : (1 : ℝ) ≤ x ^ (3 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hL2 := ceil_le_two hq1
  have hh2 := ceil_le_two hq3
  have hwY := w_ceil_le hx1
  have hw0 := w_nonneg ⌈x ^ (7 / 4 : ℝ)⌉₊
  have hx12 : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
  have hm78 : 0 ≤ x ^ (-7 / 8 : ℝ) := by positivity
  have e1 : x ^ (1 / 4 : ℝ) * x ^ (1 / 2 : ℝ) * x ^ (-7 / 8 : ℝ) = x ^ (-1 / 8 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
  have e2 : x ^ (3 / 4 : ℝ) * x ^ (-7 / 8 : ℝ) = x ^ (-1 / 8 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  set A := (⌈x ^ (1 / 4 : ℝ)⌉₊ : ℝ) * (3 * x ^ (1 / 2 : ℝ) * G ^ 2) + ⌈x ^ (3 / 4 : ℝ)⌉₊ + 1
  have hA0 : 0 ≤ A := by positivity
  have hA : A ≤ 2 * x ^ (1 / 4 : ℝ) * (3 * x ^ (1 / 2 : ℝ) * G ^ 2) + 3 * x ^ (3 / 4 : ℝ) := by
    have : (⌈x ^ (1 / 4 : ℝ)⌉₊ : ℝ) * (3 * x ^ (1 / 2 : ℝ) * G ^ 2) ≤
        2 * x ^ (1 / 4 : ℝ) * (3 * x ^ (1 / 2 : ℝ) * G ^ 2) :=
      mul_le_mul_of_nonneg_right hL2 (by positivity)
    simp only [A]; linarith
  calc A * w ⌈x ^ (7 / 4 : ℝ)⌉₊ ≤ A * x ^ (-7 / 8 : ℝ) := mul_le_mul_of_nonneg_left hwY hA0
    _ ≤ (2 * x ^ (1 / 4 : ℝ) * (3 * x ^ (1 / 2 : ℝ) * G ^ 2) + 3 * x ^ (3 / 4 : ℝ)) *
          x ^ (-7 / 8 : ℝ) := mul_le_mul_of_nonneg_right hA hm78
    _ = 6 * G ^ 2 * (x ^ (1 / 4 : ℝ) * x ^ (1 / 2 : ℝ) * x ^ (-7 / 8 : ℝ)) +
          3 * (x ^ (3 / 4 : ℝ) * x ^ (-7 / 8 : ℝ)) := by ring
    _ = (6 * G ^ 2 + 3) * x ^ (-1 / 8 : ℝ) := by rw [e1, e2]; ring

/-- Term 2: `√Y/x (D (1+Y)^{ε/4} + 1 + log x) ≤ 2 x^{-1/8} (D 3^{ε/4} x^{ε/2} + 1 + log x)`. -/
lemma term2 (D ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    Real.sqrt ⌈x ^ (7 / 4 : ℝ)⌉₊ / x * (D * (1 + (⌈x ^ (7 / 4 : ℝ)⌉₊ : ℝ)) ^ (ε / 4) + 1 +
      Real.log x) ≤ 2 * x ^ (-1 / 8 : ℝ) * (D * 3 ^ (ε / 4) * x ^ (ε / 2) + (1 + Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hq7 : (1 : ℝ) ≤ x ^ (7 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hY2 := ceil_le_two hq7
  have hYe : (1 + (⌈x ^ (7 / 4 : ℝ)⌉₊ : ℝ)) ^ (ε / 4) ≤ 3 ^ (ε / 4) * x ^ (ε / 2) := by
    have hx74 : x ^ (7 / 4 : ℝ) ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hx2 : (1 : ℝ) ≤ x ^ (2 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    calc (1 + (⌈x ^ (7 / 4 : ℝ)⌉₊ : ℝ)) ^ (ε / 4) ≤ (3 * x ^ (2 : ℝ)) ^ (ε / 4) := by
          gcongr; linarith
      _ = 3 ^ (ε / 4) * x ^ (ε / 2) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hx0.le]; ring_nf
  have e3 : x ^ (7 / 8 : ℝ) / x = x ^ (-1 / 8 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hx0]; norm_num
  have hlog := Real.log_nonneg hx1
  calc Real.sqrt ⌈x ^ (7 / 4 : ℝ)⌉₊ / x * (D * (1 + (⌈x ^ (7 / 4 : ℝ)⌉₊ : ℝ)) ^ (ε / 4) + 1 +
        Real.log x)
      ≤ (2 * x ^ (7 / 8 : ℝ)) / x * (D * (3 ^ (ε / 4) * x ^ (ε / 2)) + 1 + Real.log x) := by
        gcongr
        exact sqrt_ceil_le hx1
    _ = 2 * (x ^ (7 / 8 : ℝ) / x) * (D * 3 ^ (ε / 4) * x ^ (ε / 2) + (1 + Real.log x)) := by ring
    _ = _ := by rw [e3]

end Params

/-- Theorem 1 with a rate, given Weil's bound. -/
theorem rate (hW : ∀ (p : ℕ) [Fact p.Prime], WeilBound p) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ (p : ℕ) [Fact p.Prime], |S p - 5| ≤ K * (p : ℝ) ^ (-1 / 8 + ε) := by
  obtain ⟨D, hD0, hD⟩ := divisor_bound (ε / 4) (by linarith)
  set c := 1 + 2 / ε with hc
  have hc0 : 0 < c := by positivity
  refine ⟨6 * c ^ 2 + 3 + 2 * (D * 3 ^ (ε / 4) + c) + 1 + 8, fun p _ => ?_⟩
  have hp2 := (Fact.out : p.Prime).two_le
  have hx1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hx0 : (0 : ℝ) < p := by linarith
  have hq1 : (1 : ℝ) ≤ (p : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hq3 : (1 : ℝ) ≤ (p : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hq7 : (1 : ℝ) ≤ (p : ℝ) ^ (7 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hh : 1 ≤ ⌈(p : ℝ) ^ (3 / 4 : ℝ)⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
  have hY : 1 ≤ ⌈(p : ℝ) ^ (7 / 4 : ℝ)⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
  have hLh : p ≤ 1 + ⌈(p : ℝ) ^ (1 / 4 : ℝ)⌉₊ * ⌈(p : ℝ) ^ (3 / 4 : ℝ)⌉₊ := by
    have h1 : (p : ℝ) ≤ ((⌈(p : ℝ) ^ (1 / 4 : ℝ)⌉₊ * ⌈(p : ℝ) ^ (3 / 4 : ℝ)⌉₊ : ℕ) : ℝ) := by
      push_cast
      calc (p : ℝ) = (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (3 / 4 : ℝ) := by
            rw [← Real.rpow_add hx0]; norm_num
        _ ≤ _ := mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) (by positivity) (by positivity)
    have : p ≤ ⌈(p : ℝ) ^ (1 / 4 : ℝ)⌉₊ * ⌈(p : ℝ) ^ (3 / 4 : ℝ)⌉₊ := by exact_mod_cast h1
    omega
  have hmain := main_ineq p (hW p) _ _ _ hh hLh hY D (ε / 4) (by linarith) hD0.le hD
  have hC := C_close p hp2
  set G := 1 + Real.log p
  have hG0 : 0 ≤ G := by have := Real.log_nonneg hx1; simp only [G]; linarith
  have hlog : G ≤ c * (p : ℝ) ^ (ε / 2) := one_add_log_le hx1 hε
  have hE1 : E1 p = 3 * (p : ℝ) ^ (1 / 2 : ℝ) * G ^ 2 := by
    simp only [E1, G, Real.sqrt_eq_rpow]
  have ht1 := term1 hx1 G
  rw [← hE1] at ht1
  have ht2 := term2 hx1 D ε hD0.le hε
  set q := (p : ℝ) ^ (-1 / 8 : ℝ)
  have hq0 : 0 < q := Real.rpow_pos_of_pos hx0 _
  have ht3 : 1 / (p : ℝ) ≤ q := by
    calc 1 / (p : ℝ) = (p : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ q := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have ht4 : 8 / Real.sqrt p ≤ 8 * q := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hx0.le]
    gcongr
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hxe : (1 : ℝ) ≤ (p : ℝ) ^ ε := Real.one_le_rpow hx1 hε.le
  have hxe2 : (p : ℝ) ^ (ε / 2) ≤ (p : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hqe' : q * (p : ℝ) ^ ε = (p : ℝ) ^ (-1 / 8 + ε) := by rw [← Real.rpow_add hx0]
  have hG2 : G ^ 2 ≤ c ^ 2 * (p : ℝ) ^ ε := by
    calc G ^ 2 ≤ (c * (p : ℝ) ^ (ε / 2)) ^ 2 := by gcongr
      _ = c ^ 2 * ((p : ℝ) ^ (ε / 2)) ^ 2 := by ring
      _ = c ^ 2 * (p : ℝ) ^ ε := by rw [← Real.rpow_mul_natCast hx0.le]; norm_num
  have hGe : G ≤ c * (p : ℝ) ^ ε := hlog.trans (by gcongr)
  have hS : |S p - 5| ≤ |S p - C p - 1| + |C p - 4| := by
    calc |S p - 5| = |(S p - C p - 1) + (C p - 4)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hsum : |S p - 5| ≤ (6 * G ^ 2 + 3) * q +
      2 * q * (D * 3 ^ (ε / 4) * (p : ℝ) ^ (ε / 2) + G) + q + 8 * q := by
    have h1 := hmain.trans (add_le_add (add_le_add ht1 ht2) ht3)
    have h2 : |C p - 4| ≤ 8 * q := hC.trans ht4
    linarith
  have hD3 : 0 ≤ D * 3 ^ (ε / 4) := by positivity
  have k1 : (6 * G ^ 2 + 3) * q ≤ (6 * c ^ 2 + 3) * (q * (p : ℝ) ^ ε) := by
    have : 6 * G ^ 2 + 3 ≤ (6 * c ^ 2 + 3) * (p : ℝ) ^ ε := by linarith
    calc (6 * G ^ 2 + 3) * q ≤ (6 * c ^ 2 + 3) * (p : ℝ) ^ ε * q :=
          mul_le_mul_of_nonneg_right this hq0.le
      _ = _ := by ring
  have k2 : 2 * q * (D * 3 ^ (ε / 4) * (p : ℝ) ^ (ε / 2) + G) ≤
      2 * (D * 3 ^ (ε / 4) + c) * (q * (p : ℝ) ^ ε) := by
    have : D * 3 ^ (ε / 4) * (p : ℝ) ^ (ε / 2) + G ≤ (D * 3 ^ (ε / 4) + c) * (p : ℝ) ^ ε := by
      have : D * 3 ^ (ε / 4) * (p : ℝ) ^ (ε / 2) ≤ D * 3 ^ (ε / 4) * (p : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_left hxe2 hD3
      linarith
    calc 2 * q * (D * 3 ^ (ε / 4) * (p : ℝ) ^ (ε / 2) + G)
        ≤ 2 * q * ((D * 3 ^ (ε / 4) + c) * (p : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have k3 : q ≤ q * (p : ℝ) ^ ε := le_mul_of_one_le_right hq0.le hxe
  calc |S p - 5| ≤ _ := hsum
    _ ≤ (6 * c ^ 2 + 3) * (q * (p : ℝ) ^ ε) + 2 * (D * 3 ^ (ε / 4) + c) * (q * (p : ℝ) ^ ε) +
          q * (p : ℝ) ^ ε + 8 * (q * (p : ℝ) ^ ε) := by linarith
    _ = (6 * c ^ 2 + 3 + 2 * (D * 3 ^ (ε / 4) + c) + 1 + 8) * (q * (p : ℝ) ^ ε) := by ring
    _ = _ := by rw [hqe']

/-- Theorem 1: `S(p) → 5` along the primes, given Weil's bound. -/
theorem tendsto_five (hW : ∀ (p : ℕ) [Fact p.Prime], WeilBound p) :
    Tendsto (fun p : {p : ℕ // p.Prime} =>
      have : Fact p.1.Prime := ⟨p.2⟩; S p.1) atTop (𝓝 5) := by
  have : Nonempty {p : ℕ // p.Prime} := ⟨⟨2, Nat.prime_two⟩⟩
  obtain ⟨K, hK⟩ := rate hW (1 / 16) (by norm_num)
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hlim : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-1 / 8 + 1 / 16 : ℝ)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 16 by norm_num)).comp
      tendsto_natCast_atTop_atTop
    have := this.const_mul K
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp]; norm_num
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) δ hδ
  obtain ⟨P, hP⟩ := Nat.exists_infinite_primes N
  refine ⟨⟨P, hP.2⟩, fun p hp => ?_⟩
  have : Fact p.1.Prime := ⟨p.2⟩
  have hpN : N ≤ p.1 := le_trans hP.1 hp
  have h1 := hK p.1
  have h2 := hN p.1 hpN
  rw [Real.dist_eq, sub_zero] at h2
  rw [Real.dist_eq]
  exact lt_of_le_of_lt h1 (lt_of_le_of_lt (le_abs_self _) h2)

end InversePairs
