/- The classical Euler-number series, proved from the Entringer triangle. -/
import LeanProofs.Stanley.Entringer

namespace Stanley.Alt

open scoped Nat

/-- Euler polynomials expressed through Bernoulli polynomials. -/
noncomputable def eulerFun (n : ℕ) (x : ℝ) : ℝ :=
  2 / (n + 1) * (bernoulliFun (n + 1) x - 2 ^ (n + 1) * bernoulliFun (n + 1) (x / 2))

theorem eulerFun_zero (x : ℝ) : eulerFun 0 x = 1 := by
  simp [eulerFun]; ring

theorem bernoulliFun_dup (n : ℕ) (x : ℝ) :
    bernoulliFun n x = 2 ^ n / 2 *
      (bernoulliFun n (x / 2) + bernoulliFun n ((x + 1) / 2)) := by
  have h := bernoulliFun_mul n (by decide : (2 : ℕ) ≠ 0) (x / 2)
  simpa [Finset.sum_range_succ, show 2 * (x / 2) = x by ring,
    show x / 2 + (2 : ℝ)⁻¹ = (x + 1) / 2 by ring] using h

theorem eulerFun_reflect (n : ℕ) (x : ℝ) :
    eulerFun n (1 - x) = (-1) ^ n * eulerFun n x := by
  have hdup := bernoulliFun_dup (n + 1) x
  have hr := bernoulliFun_eval_one_sub (k := n + 1) (x := x)
  have hr2 := bernoulliFun_eval_one_sub (k := n + 1) (x := (x + 1) / 2)
  rw [show 1 - (x + 1) / 2 = (1 - x) / 2 by ring] at hr2
  simp only [eulerFun, hr, hr2]
  rw [hdup]
  simp only [pow_succ]
  ring

theorem eulerFun_half_odd (k : ℕ) : eulerFun (2 * k + 1) (1 / 2) = 0 := by
  have h := eulerFun_reflect (2 * k + 1) (1 / 2)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring,
    show (-1 : ℝ) ^ (2 * k + 1) = -1 by simp [pow_add, pow_mul]] at h
  linarith

theorem eulerFun_at_zero_even {k : ℕ} (hk : 1 ≤ k) : eulerFun (2 * k) 0 = 0 := by
  have hb : bernoulli (2 * k + 1) = 0 :=
    bernoulli_eq_zero_of_odd ⟨k, by omega⟩ (by omega)
  simp [eulerFun, bernoulliFun_eval_zero, hb]

theorem hasDerivAt_eulerFun_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (eulerFun (n + 1)) ((n + 1) * eulerFun n x) x := by
  have h := ((hasDerivAt_bernoulliFun (n + 1 + 1) x).sub
    (((hasDerivAt_bernoulliFun (n + 1 + 1) (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2)).const_mul (2 ^ (n + 1 + 1)))).const_mul
        (2 / ((n + 1 : ℕ) + 1 : ℝ))
  convert h using 1
  · ext y; simp only [eulerFun, Function.comp_apply, Nat.cast_add, Nat.cast_one, id_eq,
      Pi.sub_apply]
  · simp only [eulerFun, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp

noncomputable def evenFun (k : ℕ) (x : ℝ) : ℝ :=
  (-1) ^ k * 2 ^ (2 * k) / (2 * k)! * eulerFun (2 * k) (x / 2)

noncomputable def oddFun (k : ℕ) (x : ℝ) : ℝ :=
  (-1) ^ k * 2 ^ (2 * k + 1) / (2 * k + 1)! * eulerFun (2 * k + 1) ((x + 1) / 2)

theorem evenFun_zero (x : ℝ) : evenFun 0 x = 1 := by simp [evenFun, eulerFun_zero]

theorem oddFun_at_zero (k : ℕ) : oddFun k 0 = 0 := by
  unfold oddFun
  rw [zero_add, eulerFun_half_odd, mul_zero]

theorem evenFun_succ_at_zero (k : ℕ) : evenFun (k + 1) 0 = 0 := by
  simp [evenFun, eulerFun_at_zero_even (show 1 ≤ k + 1 by omega)]

theorem hasDerivAt_oddFun (k : ℕ) (x : ℝ) :
    HasDerivAt (oddFun k) (evenFun k (1 - x)) x := by
  have h := (((hasDerivAt_eulerFun_succ (2 * k) ((x + 1) / 2)).comp x
    (((hasDerivAt_id x).add_const 1).div_const 2)).const_mul
    ((-1 : ℝ) ^ k * 2 ^ (2 * k + 1) / (2 * k + 1)!))
  convert h using 1
  · ext y; simp only [oddFun, Function.comp_apply, id_eq]
  · have hr := eulerFun_reflect (2 * k) ((x + 1) / 2)
    rw [show 1 - (x + 1) / 2 = (1 - x) / 2 by ring,
      show (-1 : ℝ) ^ (2 * k) = 1 by simp [pow_mul]] at hr
    simp only [evenFun, one_mul] at *
    rw [hr, Nat.factorial_succ]
    push_cast
    rw [pow_succ]
    field_simp

theorem hasDerivAt_evenFun_succ (k : ℕ) (x : ℝ) :
    HasDerivAt (evenFun (k + 1)) (oddFun k (1 - x)) x := by
  have h := (((hasDerivAt_eulerFun_succ (2 * k + 1) (x / 2)).comp x
    ((hasDerivAt_id x).div_const 2)).const_mul
    ((-1 : ℝ) ^ (k + 1) * 2 ^ (2 * (k + 1)) / (2 * (k + 1))!))
  convert h using 1
  · ext y
    simp only [evenFun, Function.comp_apply, id_eq,
      show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
  · have hr := eulerFun_reflect (2 * k + 1) (x / 2)
    rw [show (-1 : ℝ) ^ (2 * k + 1) = -1 by simp [pow_add, pow_mul]] at hr
    have hx : (1 - x + 1) / 2 = 1 - x / 2 := by ring
    simp only [oddFun, hx, hr, show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
    rw [Nat.factorial_succ (2 * k + 1)]
    push_cast
    simp only [pow_succ]
    field_simp

theorem eq_of_same_derivative {f g d : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (d x) x) (hg : ∀ x, HasDerivAt g (d x) x)
    (hzero : f 0 = g 0) (x : ℝ) : f x = g x := by
  have hdiff : ∀ y, HasDerivAt (fun z => f z - g z) 0 y := by
    intro y; convert (hf y).sub (hg y) using 1; simp
  have hc := is_const_of_deriv_eq_zero (fun y => (hdiff y).differentiableAt)
    (fun y => (hdiff y).deriv) x 0
  simp only [hzero, sub_self] at hc
  exact sub_eq_zero.mp hc

theorem normalizedRow_odd_of_even (k : ℕ)
    (he : ∀ x, normalizedRow (2 * k) x = evenFun k x) (x : ℝ) :
    normalizedRow (2 * k + 1) x = oddFun k x := by
  apply eq_of_same_derivative
    (fun y => by simpa only [he] using hasDerivAt_normalizedRow (2 * k) y)
    (hasDerivAt_oddFun k)
  simp only [normalizedRow_at_zero, oddFun_at_zero]

theorem normalizedRow_even_of_odd (k : ℕ)
    (ho : ∀ x, normalizedRow (2 * k + 1) x = oddFun k x) (x : ℝ) :
    normalizedRow (2 * (k + 1)) x = evenFun (k + 1) x := by
  apply eq_of_same_derivative
    (fun y => by simpa only [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, ho] using
      hasDerivAt_normalizedRow (2 * k + 1) y)
    (hasDerivAt_evenFun_succ k)
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
    normalizedRow_at_zero, evenFun_succ_at_zero]

theorem normalizedRow_even_odd (k : ℕ) :
    (∀ x, normalizedRow (2 * k) x = evenFun k x) ∧
    (∀ x, normalizedRow (2 * k + 1) x = oddFun k x) := by
  induction k with
  | zero =>
    have he : ∀ x, normalizedRow (2 * 0) x = evenFun 0 x := by
      intro x; simp [normalizedRow_zero, evenFun_zero]
    exact ⟨he, normalizedRow_odd_of_even 0 he⟩
  | succ k ih =>
    have he := normalizedRow_even_of_odd k ih.2
    exact ⟨he, normalizedRow_odd_of_even (k + 1) he⟩

theorem E_even_bernoulli (k : ℕ) :
    (E (2 * k) : ℝ) / (2 * k)! =
      (-1) ^ (k + 1) * 2 ^ (4 * k + 2) / (2 * k + 1)! * bernoulliFun (2 * k + 1) (1 / 4) := by
  have h := (normalizedRow_even_odd k).1 1
  rw [normalizedRow_at_one] at h
  rw [h, evenFun, eulerFun]
  have hb := bernoulliFun_eval_half_eq_zero k
  rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, hb]
  rw [show (2 : ℝ)⁻¹ / 2 = 1 / 4 by norm_num]
  rw [Nat.factorial_succ (2 * k)]
  push_cast
  rw [show 4 * k + 2 = 2 * k + (2 * k + 1) + 1 by omega, pow_add, pow_add, pow_succ (-1 : ℝ)]
  field_simp; ring

theorem E_odd_bernoulli (k : ℕ) :
    (E (2 * k + 1) : ℝ) / (2 * k + 1)! =
      (-1) ^ k * 2 ^ (2 * k + 2) * (2 ^ (2 * k + 2) - 1) /
        (2 * k + 2)! * (bernoulli (2 * k + 2) : ℝ) := by
  have h := (normalizedRow_even_odd k).2 1
  rw [normalizedRow_at_one] at h
  rw [h, oddFun, eulerFun]
  norm_num only [show (1 + 1 : ℝ) / 2 = 1 by norm_num, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  have hb1 := bernoulliFun_eval_one (2 * k + 2)
  rw [ite_eq_right (by omega : 2 * k + 2 ≠ 1), add_zero, bernoulliFun_eval_zero] at hb1
  have hb2 := bernoulliFun_eval_half (2 * k + 2)
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega, hb1,
    show (1 : ℝ) / 2 = 2⁻¹ by norm_num, hb2]
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ (2 * k + 1)]
  push_cast
  simp only [pow_succ]
  field_simp; ring

theorem hasSum_odd_inv_pow {p : ℕ} {z : ℝ}
    (hz : HasSum (fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ p) z) :
    HasSum (fun j : ℕ => (1 : ℝ) / (2 * j + 1 : ℝ) ^ p)
      ((1 - 1 / 2 ^ p) * z) := by
  have he : HasSum (fun j : ℕ => (1 : ℝ) / ((2 * j : ℕ) : ℝ) ^ p) ((1 / 2 ^ p) * z) := by
    convert hz.mul_left (1 / 2 ^ p) using 1
    ext j
    push_cast
    simp only [mul_pow, one_div, mul_inv_rev, mul_comm]
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega
  have ho : Summable (fun j : ℕ => (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) ^ p) :=
    hz.summable.comp_injective hinj
  have hu := hz.unique (HasSum.even_add_odd he ho.hasSum)
  have hs : ∑' j : ℕ, (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) ^ p = (1 - 1 / 2 ^ p) * z := by
    linarith
  convert ho.hasSum using 1
  · ext j; push_cast; rfl
  · exact hs.symm

theorem sigma_odd (k : ℕ) :
    σ (2 * k + 1) = (1 - 1 / 2 ^ (2 * k + 2)) *
      ((-1) ^ (k + 2) * 2 ^ (2 * k + 1) * Real.pi ^ (2 * k + 2) *
        (bernoulli (2 * k + 2) : ℝ) / (2 * k + 2)!) := by
  have hz := hasSum_zeta_nat (Nat.succ_ne_zero k)
  have ho := hasSum_odd_inv_pow hz
  rw [show 2 * (k + 1) = 2 * k + 2 by omega,
    show 2 * k + 2 - 1 = 2 * k + 1 by omega] at ho
  simp only [Nat.succ_eq_add_one, show k + 1 + 1 = k + 2 by omega] at ho
  rw [← ho.tsum_eq]
  unfold σ
  congr 1; ext j
  rw [show j * (2 * k + 1 + 1) = 2 * (j * (k + 1)) by ring]
  simp only [pow_mul, neg_one_sq, one_pow]

theorem sin_half_odd (j : ℕ) :
    Real.sin (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / 2) = (-1) ^ j := by
  push_cast
  rw [show Real.pi * (2 * (j : ℝ) + 1) / 2 = j * Real.pi + Real.pi / 2 by ring,
    Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]

theorem sigma_even {k : ℕ} (hk : 1 ≤ k) :
    σ (2 * k) = (-1) ^ (k + 1) * (2 * Real.pi) ^ (2 * k + 1) / 2 /
      (2 * k + 1)! * bernoulliFun (2 * k + 1) (1 / 4) := by
  have hL := hasSum_one_div_nat_pow_mul_sin (show k ≠ 0 by omega)
    (show (1 / 4 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  have hsin : (fun j : ℕ => 1 / (j : ℝ) ^ (2 * k + 1) * Real.sin (2 * Real.pi * j * (1 / 4))) =
      fun j : ℕ => 1 / (j : ℝ) ^ (2 * k + 1) * Real.sin (Real.pi * j / 2) := by
    ext j; congr 1; congr 1; ring
  rw [hsin] at hL
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega
  have hzero : ∀ j ∉ Set.range (fun j : ℕ => 2 * j + 1),
      (1 : ℝ) / (j : ℝ) ^ (2 * k + 1) * Real.sin (Real.pi * j / 2) = 0 := by
    intro j hj
    obtain ⟨i, rfl⟩ : Even j := by
      by_contra hn
      obtain ⟨i, hi⟩ := Nat.not_even_iff_odd.mp hn
      exact hj ⟨i, hi.symm⟩
    have hs : Real.sin (Real.pi * ((i + i : ℕ) : ℝ) / 2) = 0 := by
      push_cast
      rw [show Real.pi * ((i : ℝ) + i) / 2 = i * Real.pi by ring, Real.sin_nat_mul_pi]
    rw [hs, mul_zero]
  have h := (hinj.hasSum_iff hzero).mpr hL
  change HasSum _ (_ * bernoulliFun (2 * k + 1) (1 / 4)) at h
  unfold σ
  rw [← h.tsum_eq]
  congr 1; ext j
  simp only [Function.comp_apply]
  rw [sin_half_odd, mul_comm j (2 * k + 1), pow_mul]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
  push_cast
  ring

theorem eulerSeries : EulerSeries := by
  intro m hm
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨k, rfl⟩ := he
    rw [show k + k = 2 * k by omega]
    have hk : 1 ≤ k := by omega
    rw [E_even_bernoulli, sigma_even hk, div_pow, mul_pow]
    field_simp
    ring
  · obtain ⟨k, rfl⟩ := ho
    rw [E_odd_bernoulli, sigma_odd]
    simp only [show 2 * k + 1 + 1 = 2 * k + 2 by omega, div_pow,
      show k + 2 = k + 1 + 1 by omega, pow_succ]
    field_simp

end Stanley.Alt
