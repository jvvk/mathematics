/-
  An arithmetic form of the remaining Stanley identity. Formal differentiation
  identifies its normalized coefficients with natural-number recurrences.
  This module does not assert the missing identity for the permutation count g.
-/
import LeanProofs.Stanley.Alternating
import Mathlib.RingTheory.PowerSeries.Derivative

namespace Stanley.Alt
open Finset PowerSeries
open scoped Nat

/-- The formal artanh series has derivative 1/(1-X²). -/
theorem u_differential : (1 - X ^ 2) * PowerSeries.derivative u = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_derivative, coeff_X_pow_mul', coeff_one]
  simp only [u, coeff_mk]
  cases n with
  | zero => norm_num
  | succ n =>
    cases n with
    | zero => norm_num
    | succ n =>
      simp only [show 2 ≤ n + 1 + 1 by omega, ite_true,
        show n + 1 + 1 - 2 = n by omega, coeff_derivative, coeff_mk]
      by_cases hn : Odd (n + 1)
      · have hn' : Odd (n + 1 + 1 + 1) := by simpa only [Nat.odd_add_one, Nat.even_add_one, not_not] using hn
        simp only [hn, hn', ite_true, Nat.succ_ne_zero, ite_false]
        have h1 : (n + 1 : ℝ) ≠ 0 := by positivity
        have h3 : (n + 1 + 1 + 1 : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp
        ring
      · have hn' : ¬ Odd (n + 1 + 1 + 1) := by simpa only [Nat.odd_add_one, Nat.even_add_one, not_not] using hn
        simp [hn, hn']

/-- The central-binomial series satisfies its first-order differential equation. -/
theorem s_coeff_recurrence (n : ℕ) :
    coeff (n + 2) s * (n + 2 : ℝ) = (n + 1 : ℝ) * coeff n s := by
  simp only [s, coeff_mk]
  by_cases hn : Even n
  · obtain ⟨k, rfl⟩ := hn
    have he : Even (k + k + 2) := ⟨k + 1, by omega⟩
    rw [ite_eq_left he, ite_eq_left ⟨k, rfl⟩,
      show (k + k + 2) / 2 = k + 1 by omega,
      show (k + k) / 2 = k by omega,
      show k + k + 2 = 2 * (k + 1) by omega,
      show k + k = 2 * k by omega]
    have hb := Nat.succ_mul_centralBinom_succ k
    have hb' : (k + 1 : ℝ) * (Nat.centralBinom (k + 1) : ℝ) =
        2 * (2 * k + 1 : ℝ) * (Nat.centralBinom k : ℝ) := by exact_mod_cast hb
    rw [← Nat.centralBinom_eq_two_mul_choose, ← Nat.centralBinom_eq_two_mul_choose,
      pow_succ]
    push_cast
    field_simp
    nlinarith [hb']
  · have hn' : ¬ Even (n + 2) := by simpa only [show n + 2 = n + 1 + 1 by omega, Nat.even_add_one, Nat.odd_add_one, not_not] using hn
    simp [hn, hn']

theorem s_differential : (1 - X ^ 2) * PowerSeries.derivative s = X * s := by
  ext n
  rw [sub_mul, one_mul, map_sub]
  cases n with
  | zero => simp [coeff_derivative, s]
  | succ n =>
    rw [coeff_derivative, coeff_succ_X_mul]
    have hx : coeff (n + 1) (X ^ 2 * PowerSeries.derivative s) = coeff n s * n := by
      cases n with
      | zero => simp [coeff_X_pow_mul']
      | succ n =>
        rw [show n + 1 + 1 = n + 2 by omega, coeff_X_pow_mul, coeff_derivative]
        simp
    rw [hx]
    have h := s_coeff_recurrence n
    push_cast at h ⊢
    linarith

/-- Allow all cycle lengths (`true`) or only odd lengths (`false`). -/
noncomputable def cycleSeries (all : Bool) (m : ℕ) : PowerSeries ℝ :=
  (if all then s else 1) * u ^ m

theorem cycleSeries_differential (all : Bool) (m : ℕ) :
    (1 - X ^ 2) * PowerSeries.derivative (cycleSeries all m) =
      (if all then X * cycleSeries all m else 0) +
        (m : PowerSeries ℝ) * cycleSeries all (m - 1) := by
  unfold cycleSeries
  cases all with
  | false =>
    simp only [Bool.false_eq_true, ite_false, one_mul, zero_add]
    rw [PowerSeries.derivative_pow]
    calc
      _ = (m : PowerSeries ℝ) * u ^ (m - 1) *
          ((1 - X ^ 2) * PowerSeries.derivative u) := by ring
      _ = _ := by rw [u_differential, mul_one]
  | true =>
    simp only [ite_true]
    rw [Derivation.leibniz, PowerSeries.derivative_pow]
    calc
      _ = ((1 - X ^ 2) * PowerSeries.derivative s) * u ^ m +
          (m : PowerSeries ℝ) * (s * u ^ (m - 1)) *
            ((1 - X ^ 2) * PowerSeries.derivative u) := by ring
      _ = _ := by rw [s_differential, u_differential]; ring

/-- Factorial-normalized coefficients of the cycle series. -/
noncomputable def cycleCoefficient (all : Bool) (n m : ℕ) : ℝ :=
  (n ! : ℝ) / m ! * coeff n (cycleSeries all m)

theorem cycleSeries_coeff_recurrence (all : Bool) (n m : ℕ) :
    coeff (n + 2) (cycleSeries all m) * (n + 2 : ℝ) =
      (n + if all then 1 else 0 : ℝ) * coeff n (cycleSeries all m) +
        m * coeff (n + 1) (cycleSeries all (m - 1)) := by
  have h := congrArg (coeff (n + 1)) (cycleSeries_differential all m)
  rw [sub_mul, one_mul, map_sub, coeff_derivative, map_add, coeff_natCast_mul] at h
  have hx : coeff (n + 1) (X ^ 2 * PowerSeries.derivative (cycleSeries all m)) =
      coeff n (cycleSeries all m) * n := by
    cases n with
    | zero => simp [coeff_X_pow_mul']
    | succ n =>
      rw [show n + 1 + 1 = n + 2 by omega, coeff_X_pow_mul, coeff_derivative]
      simp
  rw [hx] at h
  cases all <;>
    simp_all only [Bool.false_eq_true, ite_false, ite_true, map_zero, coeff_succ_X_mul,
      Nat.cast_add, Nat.cast_one, add_zero] <;> linarith

theorem cycleCoefficient_zero (all : Bool) (m : ℕ) :
    cycleCoefficient all 0 m = if m = 0 then 1 else 0 := by
  cases all <;> cases m <;>
    simp [cycleCoefficient, cycleSeries, coeff_zero_eq_constantCoeff, u, s]

theorem cycleCoefficient_one (all : Bool) (m : ℕ) :
    cycleCoefficient all 1 m = if m = 1 then 1 else 0 := by
  cases all <;> rcases m with _ | _ | m <;>
    simp [cycleCoefficient, cycleSeries, coeff_one_mul, coeff_one_pow, u, s]

theorem cycleCoefficient_recurrence (all : Bool) (n m : ℕ) :
    cycleCoefficient all (n + 2) m =
      (if m = 0 then 0 else cycleCoefficient all (n + 1) (m - 1)) +
        (n + 1 : ℝ) * (n + if all then 1 else 0 : ℝ) * cycleCoefficient all n m := by
  have h := cycleSeries_coeff_recurrence all n m
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  have hm : (m ! : ℝ) ≠ 0 := by positivity
  have hc : coeff (n + 2) (cycleSeries all m) =
      ((n + if all then 1 else 0 : ℝ) * coeff n (cycleSeries all m) +
        m * coeff (n + 1) (cycleSeries all (m - 1))) / (n + 2 : ℝ) :=
    (eq_div_iff hn).mpr h
  unfold cycleCoefficient
  rw [hc, show (n + 2)! = (n + 2) * ((n + 1) * n !) by
    rw [Nat.factorial_succ, Nat.factorial_succ]]
  cases m with
  | zero =>
    simp only [ite_true, Nat.factorial_zero, Nat.cast_one, div_one, Nat.cast_zero,
      zero_mul, add_zero]
    push_cast
    field_simp
    ring
  | succ m =>
    simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    rw [Nat.factorial_succ m, Nat.factorial_succ n]
    push_cast
    field_simp
    ring

/-- Integer recurrence for the two families of normalized coefficients.
The interpretation in terms of permutation cycles is not asserted here. -/
def cycleNumbers (all : Bool) : ℕ → ℕ → ℕ
  | 0, m => if m = 0 then 1 else 0
  | 1, m => if m = 1 then 1 else 0
  | n + 2, m => (if m = 0 then 0 else cycleNumbers all (n + 1) (m - 1)) +
      (n + 1) * (n + if all then 1 else 0) * cycleNumbers all n m

/-- All the normalized coefficients are nonnegative integers. -/
theorem cycleNumbers_eq_coefficient (all : Bool) (n m : ℕ) :
    (cycleNumbers all n m : ℝ) = cycleCoefficient all n m := by
  induction n using Nat.twoStepInduction generalizing m with
  | zero => simp [cycleNumbers, cycleCoefficient_zero]
  | one => simp [cycleNumbers, cycleCoefficient_one]
  | more n ih0 ih1 =>
    rw [cycleNumbers, cycleCoefficient_recurrence]
    push_cast
    rw [ih0, ih1]

/-- The coefficient selector in StanleyGF, after factorial normalization. -/
theorem cycleNumbers_cc (n m : ℕ) :
    (cycleNumbers (decide (Even m)) n m : ℝ) = (n ! : ℝ) / m ! * cc n m := by
  rw [cycleNumbers_eq_coefficient]
  unfold cycleCoefficient cycleSeries cc
  by_cases hm : Odd m
  · have he : ¬ Even m := Nat.not_even_iff_odd.mpr hm
    simp [hm, he]
  · have he : Even m := Nat.not_odd_iff_even.mp hm
    simp [hm, he]

/-- An integer-only statement equivalent to the missing universal GF identity.
No instance of this proposition is assumed or proved by defining it. -/
def StanleyFinite : Prop := ∀ n : ℕ,
  g n * n ! = ∑ m ∈ range (n + 1), E m ^ 2 * cycleNumbers (decide (Even m)) n m

/-- The formal-series manipulation is completely discharged: the unresolved
obligation can instead be proved as this finite natural-number equality. -/
theorem stanley_identity_iff_integer (n : ℕ) :
    ((g n : ℝ) = ∑ m ∈ range (n + 1), a m * cc n m) ↔
      g n * n ! = ∑ m ∈ range (n + 1), E m ^ 2 * cycleNumbers (decide (Even m)) n m := by
  have ht (n m : ℕ) : (n ! : ℝ) * (a m * cc n m) =
      (E m : ℝ) ^ 2 * (cycleNumbers (decide (Even m)) n m : ℝ) := by
    rw [cycleNumbers_cc, a]
    ring
  constructor
  · intro h
    have hr : (g n : ℝ) * (n ! : ℝ) =
        ∑ m ∈ range (n + 1), (E m : ℝ) ^ 2 *
          (cycleNumbers (decide (Even m)) n m : ℝ) := by
      rw [mul_comm, h, mul_sum]
      apply sum_congr rfl
      intro m _
      exact ht n m
    exact_mod_cast hr
  · intro h
    have hr : (g n : ℝ) * (n ! : ℝ) =
        ∑ m ∈ range (n + 1), (E m : ℝ) ^ 2 *
          (cycleNumbers (decide (Even m)) n m : ℝ) := by exact_mod_cast h
    have hn : (n ! : ℝ) ≠ 0 := by positivity
    apply (mul_left_cancel₀ hn)
    rw [mul_sum]
    calc
      (n ! : ℝ) * (g n : ℝ) = ∑ m ∈ range (n + 1), (E m : ℝ) ^ 2 *
          (cycleNumbers (decide (Even m)) n m : ℝ) := by
        simpa only [mul_comm] using hr
      _ = ∑ m ∈ range (n + 1), (n ! : ℝ) * (a m * cc n m) := by
        apply sum_congr rfl
        intro m _
        exact (ht n m).symm

theorem stanleyGF_iff_finite : StanleyGF ↔ StanleyFinite := by
  constructor
  · intro h n
    exact (stanley_identity_iff_integer n).mp (h n)
  · intro h n
    exact (stanley_identity_iff_integer n).mpr (h n)

end Stanley.Alt
