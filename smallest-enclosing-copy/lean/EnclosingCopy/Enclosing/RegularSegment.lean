import EnclosingCopy.Enclosing.RegularModel

/-!
# Theorem 8 for the regular `q`-gon: the segment terms

For side data `IsReg K r c` of the regular `q`-gon:

* `un_neg_iff`: `u_b = -u_a` forces `q` even and `b = a + q/2`, so the ordered pairs of
  parallel sides are the `q` pairs `(a, a + q/2)` when `q` is even and there are none when `q`
  is odd (`parPairs_even`, `parPairs_odd`);
* `segDensity_reg`: the position density is `2r ∫∫_{s₀ < s₁} (s₁ - s₀)² = 8 r c⁴ / 3`;
* `slopeSum_reg`: `S = ∑_{uⱼ·t > 0} 2c uⱼ·t = 2c ∑_{d=1}^{q/2-1} sin (2πd/q) = 2c cot (π/q)`.
-/

namespace Enclosing

open MeasureTheory Set Real ENNReal

variable {q : ℕ}

/-! ### Angles modulo `2π` -/

/-- Normals of sums: `u_{a+d}` has angle `θ_a + θ_d`. -/
lemma un_add [NeZero q] (a d : Fin q) :
    un q (a + d) = (cos (2 * π * ((a : ℕ) + (d : ℕ)) / q), sin (2 * π * ((a : ℕ) + (d : ℕ)) / q)) := by
  have hq : (0 : ℝ) < q := by have := NeZero.pos q; exact_mod_cast this
  set x := (a : ℕ) + (d : ℕ)
  have hval : ((a + d : Fin q) : ℕ) = x % q := Fin.val_add a d
  have hdiv := Nat.mod_add_div x q
  have he : 2 * π * ((x % q : ℕ) : ℝ) / q = 2 * π * (x : ℝ) / q - ((x / q : ℕ) : ℝ) * (2 * π) := by
    have : ((x % q : ℕ) : ℝ) = x - q * ((x / q : ℕ) : ℝ) := by
      have := congrArg (fun n : ℕ => (n : ℝ)) hdiv; push_cast at this ⊢; linarith
    rw [this]; field_simp
  simp only [un, hval]
  rw [he, cos_sub_nat_mul_two_pi, sin_sub_nat_mul_two_pi]
  simp only [x, Nat.cast_add]

lemma un_neg_int [NeZero q] {a b : Fin q} (h : un q b = -un q a) :
    ∃ n : ℤ, 2 * ((b : ℕ) - (a : ℕ) : ℤ) - q = 2 * q * n := by
  have hq : (0 : ℝ) < q := by have := NeZero.pos q; exact_mod_cast this
  have h1 : cos (2 * π * (b : ℕ) / q) = -cos (2 * π * (a : ℕ) / q) := congrArg Prod.fst h
  have h2 : sin (2 * π * (b : ℕ) / q) = -sin (2 * π * (a : ℕ) / q) := congrArg Prod.snd h
  have hc : cos (2 * π * (b : ℕ) / q - 2 * π * (a : ℕ) / q - π) = 1 := by
    rw [cos_sub_pi, cos_sub, h1, h2]
    have := sin_sq_add_cos_sq (2 * π * (a : ℕ) / q)
    linear_combination this
  obtain ⟨n, hn⟩ := (cos_eq_one_iff _).1 hc
  refine ⟨n, ?_⟩
  have : (2 * (((b : ℕ) : ℝ) - (a : ℕ)) - q : ℝ) = 2 * q * n := by
    have hp := pi_pos
    field_simp at hn
    nlinarith [hn]
  exact_mod_cast this

lemma un_inj [NeZero q] {a b : Fin q} (h : un q a = un q b) : a = b := by
  have hq : (0 : ℝ) < q := by have := NeZero.pos q; exact_mod_cast this
  have h1 : cos (2 * π * (a : ℕ) / q) = cos (2 * π * (b : ℕ) / q) := congrArg Prod.fst h
  have h2 : sin (2 * π * (a : ℕ) / q) = sin (2 * π * (b : ℕ) / q) := congrArg Prod.snd h
  have hc : cos (2 * π * (a : ℕ) / q - 2 * π * (b : ℕ) / q) = 1 := by
    rw [cos_sub, h1, h2]
    have := sin_sq_add_cos_sq (2 * π * (b : ℕ) / q)
    linear_combination this
  obtain ⟨n, hn⟩ := (cos_eq_one_iff _).1 hc
  have hr : (((a : ℕ) : ℝ) - (b : ℕ)) = q * n := by
    have hp := pi_pos
    field_simp at hn
    nlinarith [hn]
  have hz : ((a : ℕ) : ℤ) - (b : ℕ) = q * n := by exact_mod_cast hr
  have ha := a.isLt
  have hb := b.isLt
  have hn0 : n = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith
    · nlinarith
  apply Fin.ext
  rw [hn0, mul_zero] at hz
  omega

/-- The opposite side, for even `q = 2m`. -/
def halfFin (m : ℕ) (hm : 0 < m) : Fin (2 * m) := ⟨m, by omega⟩

lemma un_add_half {m : ℕ} (hm : 0 < m) (a : Fin (2 * m)) :
    un (2 * m) (a + halfFin m hm) = -un (2 * m) a := by
  have : NeZero (2 * m) := ⟨by omega⟩
  rw [un_add]
  simp only [halfFin, un, Prod.neg_mk]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have he : 2 * π * (((a : ℕ) : ℝ) + m) / ((2 * m : ℕ) : ℝ) =
      2 * π * (a : ℕ) / ((2 * m : ℕ) : ℝ) + π := by
    push_cast; field_simp
  rw [he, cos_add_pi, sin_add_pi]

/-! ### The ordered pairs of parallel sides -/

section Pairs

variable {K : Sides q} {r c : ℝ} (hK : IsReg K r c)
include hK

lemma parPairs_odd [NeZero q] (hodd : ¬ Even q) : parPairs K = ∅ := by
  rw [parPairs, Finset.filter_eq_empty_iff]
  rintro ⟨a, b⟩ - h
  simp only [hK.u] at h
  obtain ⟨n, hn⟩ := un_neg_int h
  apply hodd
  have hz : Even (q : ℤ) := ⟨((b : ℕ) : ℤ) - (a : ℕ) - q * n, by linarith [hn]⟩
  exact (Int.even_coe_nat q).1 hz

end Pairs

lemma parPairs_even {m : ℕ} (hm : 0 < m) (K : Sides (2 * m)) (hK : IsReg K r c) :
    parPairs K = Finset.univ.image fun a : Fin (2 * m) => (a, a + halfFin m hm) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  ext ⟨a, b⟩
  simp only [parPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Prod.mk.injEq, hK.u]
  constructor
  · intro h
    exact ⟨a, rfl, un_inj (by rw [un_add_half hm, h])⟩
  · rintro ⟨a', rfl, rfl⟩
    exact un_add_half hm a'


/-! ### The tangent slopes -/

/-- `u_{k+d} · t_k = sin (2πd/q)`. -/
lemma dot_un_tang [NeZero q] (k d : Fin q) :
    dot (un q (k + d)) (-(un q k).2, (un q k).1) = sin (2 * π * (d : ℕ) / q) := by
  rw [un_add]
  simp only [dot, un]
  set A := 2 * π * ((k : ℕ) : ℝ) / q
  set B := 2 * π * ((d : ℕ) : ℝ) / q
  have hAB : 2 * π * (((k : ℕ) : ℝ) + (d : ℕ)) / q = A + B := by simp only [A, B]; ring
  rw [hAB]
  have := sin_sub (A + B) A
  rw [add_sub_cancel_left] at this
  linarith

/-- The pair `(a, a + q/2)` is a pair of parallel sides. -/
lemma parPair_reg {m : ℕ} (hm : 2 ≤ m) {K : Sides (2 * m)} {r c : ℝ} (hK : IsReg K r c)
    (hr : 0 < r) (a : Fin (2 * m)) : ParPair K a (a + halfFin m (by omega)) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hK.u]; simp only [un]; nlinarith [sin_sq_add_cos_sq (2 * π * ((a : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ))]
  · rw [hK.u, hK.u, un_add_half]
  · rw [hK.h, hK.h]; linarith
  · refine ⟨a + ⟨1, by omega⟩, ?_⟩
    rw [tang, hK.u, hK.u, dot_un_tang]
    apply sin_pos_of_pos_of_lt_pi (by positivity)
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have h4 : (4 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by push_cast; linarith
    rw [div_lt_iff₀ (by linarith)]
    simp only [Nat.cast_one]
    nlinarith [pi_pos]

/-- **The slope sum of the regular `2m`-gon**: `S = 2c cot (π/q)`. -/
theorem slopeSum_reg {m : ℕ} (hm : 2 ≤ m) {K : Sides (2 * m)} {r c : ℝ} (hK : IsReg K r c)
    (k : Fin (2 * m)) :
    slopeSum K k = 2 * c * (cos (π / (2 * m)) / sin (π / (2 * m))) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm' : (0 : ℝ) < m := by linarith
  unfold slopeSum positiveSides
  rw [Finset.sum_filter]
  simp only [hK.a, hK.b, hK.u, tang, sub_neg_eq_add]
  rw [← Equiv.sum_comp (Equiv.addLeft k)]
  simp only [Equiv.coe_addLeft, dot_un_tang]
  let F : ℕ → ℝ := fun d =>
    if 0 < sin (2 * π * (d : ℝ) / ((2 * m : ℕ) : ℝ)) then
      (c + c) * sin (2 * π * (d : ℝ) / ((2 * m : ℕ) : ℝ)) else 0
  rw [Fin.sum_univ_eq_sum_range F (2 * m)]
  have hF : ∀ d ∈ Finset.range (2 * m), F d =
      if d ∈ Finset.Ico 1 m then 2 * c * sin (π * d / m) else 0 := by
    intro d hd
    rw [Finset.mem_range] at hd
    have hang : 2 * π * (d : ℝ) / ((2 * m : ℕ) : ℝ) = π * d / m := by push_cast; field_simp
    simp only [F, hang]
    by_cases h1 : d ∈ Finset.Ico 1 m
    · rw [if_pos h1]
      rw [Finset.mem_Ico] at h1
      have hpos : 0 < sin (π * d / m) := by
        apply sin_pos_of_pos_of_lt_pi
        · have : (1 : ℝ) ≤ d := by exact_mod_cast h1.1
          positivity
        · rw [div_lt_iff₀ hm']
          have : (d : ℝ) < m := by exact_mod_cast h1.2
          nlinarith [pi_pos]
      rw [if_pos hpos]; ring
    · rw [if_neg h1]
      rw [Finset.mem_Ico] at h1
      have hle : sin (π * d / m) ≤ 0 := by
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · subst h0; simp
        · have hdm : m ≤ d := by omega
          have h1' : (m : ℝ) ≤ d := by exact_mod_cast hdm
          have h2' : (d : ℝ) < 2 * m := by exact_mod_cast hd
          have hx : π * d / m - π ∈ Icc 0 π := by
            constructor
            · rw [sub_nonneg, le_div_iff₀ hm']; nlinarith [pi_pos]
            · rw [sub_le_iff_le_add, div_le_iff₀ hm']; nlinarith [pi_pos]
          have := sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2
          rw [sin_sub_pi] at this
          linarith
      rw [if_neg (not_lt.2 hle)]
  rw [Finset.sum_congr rfl hF, Finset.sum_ite_mem,
    Finset.inter_eq_right.2 (fun d hd => by
      rw [Finset.mem_Ico] at hd; rw [Finset.mem_range]; omega),
    ← Finset.mul_sum, sum_sin_eq_cot (by omega)]

/-! ### The position density -/

/-- `∫_{-c}^{c} max(x - a, 0)² dx = (c - a)³/3` for `a ∈ [-c, c]`. -/
lemma integral_max_sq_c {c a : ℝ} (ha : a ∈ Icc (-c) c) :
    ∫ x in (-c)..c, (max (x - a) 0) ^ 2 = (c - a) ^ 3 / 3 := by
  have hcont : Continuous fun x : ℝ => (max (x - a) 0) ^ 2 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have h1 : ∫ x in (-c)..a, (max (x - a) 0) ^ 2 = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro x hx
      rw [uIcc_of_le ha.1] at hx
      simp [max_eq_right (by linarith [hx.2] : x - a ≤ 0)]
  have h2 : ∫ x in a..c, (max (x - a) 0) ^ 2 = ∫ x in a..c, (x - a) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ha.2] at hx
    simp only [max_eq_left (by linarith [hx.1] : 0 ≤ x - a)]
  rw [h1, h2, intervalIntegral.integral_comp_sub_right (fun x => x ^ 2), integral_pow]
  ring

/-- **The position density of the regular `q`-gon**: `8 r c⁴ / 3`. -/
theorem segDensity_reg {K : Sides q} {r c : ℝ} (hK : IsReg K r c) (hr : 0 < r) (hc : 0 < c)
    (k kb : Fin q) : segDensity K k kb = ENNReal.ofReal (8 * r * c ^ 4 / 3) := by
  set ν : Measure ℝ := volume.restrict (Icc (-c) c)
  let G : ℝ × ℝ × ℝ → ℝ≥0∞ := {p : ℝ × ℝ × ℝ | p.1 < -p.2.2 ∧ -p.2.2 < p.2.1}.indicator
    (fun p => ENNReal.ofReal ((p.2.1 - p.1) * (r + r)))
  have hGm : Measurable G := by
    refine (ENNReal.measurable_ofReal.comp (by fun_prop)).indicator ?_
    exact (measurableSet_lt (f := fun p : ℝ × ℝ × ℝ => p.1) (g := fun p => -p.2.2)
      (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (f := fun p : ℝ × ℝ × ℝ => -p.2.2) (g := fun p => p.2.1)
        (by fun_prop) (by fun_prop))
  have hmp : MeasurePreserving (fun s : Fin 3 → ℝ => (s 0, s 1, s 2))
      (Measure.pi fun _ => ν) (ν.prod (ν.prod ν)) := by
    have h := ((MeasurePreserving.id ν).prod (measurePreserving_finTwoArrow ν)).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => ν) 0)
    convert h using 1
    funext s
    rfl
  have hint : segDensity K k kb =
      ∫⁻ s : Fin 3 → ℝ, G (s 0, s 1, s 2) ∂(Measure.pi fun _ => ν) := by
    unfold segDensity segRow
    have hm : (Measure.pi fun i : Fin 3 => volume.restrict
        (Icc (K.a (![k, k, kb] i)) (K.b (![k, k, kb] i)))) = Measure.pi fun _ => ν := by
      simp only [hK.a, hK.b, ν]
    rw [hm]
    apply lintegral_congr
    intro s
    simp only [G, Set.indicator, mem_ofPred_eq, hK.h]
  rw [hint, hmp.lintegral_comp hGm, lintegral_prod _ hGm.aemeasurable]
  have hin : ∀ s₀ ∈ Icc (-c) c, ∀ s₁ ∈ Icc (-c) c,
      ∫⁻ s₂, G (s₀, s₁, s₂) ∂ν = ENNReal.ofReal ((r + r) * (max (s₁ - s₀) 0) ^ 2) := by
    intro s₀ h₀ s₁ h₁
    have he : (fun s₂ => G (s₀, s₁, s₂)) =
        (Ioo (-s₁) (-s₀)).indicator (fun _ => ENNReal.ofReal ((s₁ - s₀) * (r + r))) := by
      funext s₂
      simp only [G, Set.indicator, mem_ofPred_eq, mem_Ioo]
      congr 1
      apply propext
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [he, lintegral_indicator_const measurableSet_Ioo,
      Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (Ioo_subset_Icc_self.trans (Icc_subset_Icc (by linarith [h₁.2])
        (by linarith [h₀.1]))), Real.volume_Ioo]
    rcases le_total 0 (s₁ - s₀) with h | h
    · rw [max_eq_left h, ← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos (show -s₀ - -s₁ ≤ 0 by linarith)]; simp
  have hmid : ∀ s₀ ∈ Icc (-c) c,
      ∫⁻ p, G (s₀, p) ∂(ν.prod ν) = ENNReal.ofReal ((r + r) * ((c - s₀) ^ 3 / 3)) := by
    intro s₀ h₀
    rw [lintegral_prod (fun p => G (s₀, p))
      (hGm.comp (measurable_const.prodMk measurable_id)).aemeasurable]
    calc ∫⁻ s₁, ∫⁻ s₂, G (s₀, s₁, s₂) ∂ν ∂ν
        = ∫⁻ s₁, ENNReal.ofReal ((r + r) * (max (s₁ - s₀) 0) ^ 2) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with s₁ h₁
          exact hin s₀ h₀ s₁ h₁
      _ = _ := by
          rw [lintegral_Icc_ofReal (by fun_prop) (by linarith) (fun _ _ => by positivity),
            intervalIntegral.integral_const_mul, integral_max_sq_c h₀]
  calc ∫⁻ s₀, ∫⁻ p, G (s₀, p) ∂(ν.prod ν) ∂ν
      = ∫⁻ s₀, ENNReal.ofReal ((r + r) * ((c - s₀) ^ 3 / 3)) ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s₀ h₀
        exact hmid s₀ h₀
    _ = _ := by
        rw [lintegral_Icc_ofReal (by fun_prop) (by linarith)
          (fun x hx => by have := hx.2; have : 0 ≤ c - x := by linarith
                          positivity)]
        congr 1
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
          intervalIntegral.integral_comp_sub_left (fun x => x ^ 3), integral_pow]
        ring

end Enclosing
