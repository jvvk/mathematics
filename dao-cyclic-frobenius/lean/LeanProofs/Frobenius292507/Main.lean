import LeanProofs.Frobenius292507.Semigroup

/-!
# MO 292507: the headline

With `x`, `P`, `N = P - 1` and `S` (`InS`) as in `Frobenius292507.Defs`:

`frobenius`: for `n ≥ 2`, positive `n`-periodic `a` and `gcd (x₀, …, xₙ₋₁) = 1`,
`(n - 1) N ∉ S` and every `m > (n - 1) N` lies in `S`. So the Frobenius number of
`⟨x₀, …, xₙ₋₁⟩` is `(n - 1)(a₀⋯aₙ₋₁ - 1)`. No minimal-generation hypothesis.

* `not_InS`: step 10 (carry `(n-1)N` down to a digit vector with residue `0`; it must be maximal,
  of weight `nN`).
* `InS_of_gt`: step 11 (`N ∣ m`: `m = nN + kN`; otherwise solve `x₀ t ≡ m`, expand `t` in the mixed
  radix and climb by step 8).
* `example123`: `a = (1, 2, 3)` gives generators `4, 9, 7` and Frobenius number `10`,
  as a corollary.
-/

namespace Frobenius292507

open Finset

variable {n : ℕ} {a : ℕ → ℕ}

/-- **Step 10**: `(n - 1) N ∉ S`. -/
theorem not_InS (hn : 2 ≤ n) (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i)
    (hgcd : (range n).gcd (x n a) = 1) : ¬ InS n a ((n - 1) * N n a) := by
  intro hS
  have hn1 : 1 ≤ n := by omega
  have hN := N_pos hn hper hpos hgcd
  have hcop := coprime_x0_N hper hpos hgcd
  obtain ⟨d, k, hd, hwd, heq⟩ :=
    carry_down hn1 hper hpos hN _ hS (Nat.mul_pos (by omega) hN)
  have h0 : (w n a d : ZMod (N n a)) = 0 := by
    have := congrArg (Nat.cast (R := ZMod (N n a))) heq
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, mul_zero, add_zero] at this
    exact this.symm
  rw [w_cong hper hpos d] at h0
  have hdvd : N n a ∣ v n a d := by
    have : N n a ∣ x n a 0 * v n a d := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast; exact h0
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
  have hvpos : 0 < v n a d := by
    obtain ⟨i, hi, hdi⟩ := (w_pos_iff hn1).1 hwd
    have h1 := single_le_sum (f := fun j => d j * pi n a j) (fun _ _ => Nat.zero_le _)
      (mem_range.2 hi)
    have h2 := pi_pos (n := n) hpos i
    change d i * pi n a i ≤ v n a d at h1
    nlinarith
  have hvN : v n a d = N n a := le_antisymm (v_le hper hpos hd) (Nat.le_of_dvd hvpos hdvd)
  have hmax := v_eq_N hper hpos hd hvN
  have hw : w n a d = n * N n a := by
    rw [← w_max hn1 hper hpos]
    exact sum_congr rfl fun i hi => by rw [hmax i (mem_range.1 hi)]
  rw [hw] at heq
  have : n * N n a = (n - 1) * N n a + N n a := by
    have : N n a ≤ n * N n a := Nat.le_mul_of_pos_left _ (by omega)
    rw [tsub_mul, one_mul]
    omega
  nlinarith [Nat.zero_le (k * N n a)]

/-- **Step 11**: every `m > (n - 1) N` lies in `S`. -/
theorem InS_of_gt (hn : 2 ≤ n) (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i)
    (hgcd : (range n).gcd (x n a) = 1) {m : ℕ} (hm : (n - 1) * N n a < m) : InS n a m := by
  have hn1 : 1 ≤ n := by omega
  have hN := N_pos hn hper hpos hgcd
  have hcop := coprime_x0_N hper hpos hgcd
  have hnN : n * N n a = (n - 1) * N n a + N n a := by
    have : N n a ≤ n * N n a := Nat.le_mul_of_pos_left _ (by omega)
    rw [tsub_mul, one_mul]
    omega
  by_cases hdiv : N n a ∣ m
  · obtain ⟨q, rfl⟩ := hdiv
    have hq : n ≤ q := by
      by_contra h
      have : N n a * q ≤ N n a * (n - 1) := Nat.mul_le_mul_left _ (by omega)
      rw [mul_comm (N n a) (n - 1)] at this
      omega
    have hmaxS : InS n a (n * N n a) := w_max hn1 hper hpos ▸ InS_w _
    have := InS_add_mul_N hn1 hper hpos hmaxS (Nat.mul_pos (by omega) hN) (q - n)
    obtain ⟨r, rfl⟩ : ∃ r, q = n + r := ⟨q - n, by omega⟩
    rw [Nat.add_sub_cancel_left] at this
    convert this using 1
    ring
  · have : NeZero (N n a) := ⟨by omega⟩
    set u : ZMod (N n a) := (m : ZMod (N n a)) * (x n a 0 : ZMod (N n a))⁻¹
    set t := u.val
    have ht : t < N n a := ZMod.val_lt u
    have hxt : ((x n a 0 * t : ℕ) : ZMod (N n a)) = m := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      simp only [u]
      rw [mul_comm (m : ZMod (N n a)), ← mul_assoc,
        ZMod.coe_mul_inv_eq_one _ hcop, one_mul]
    have ht0 : t ≠ 0 := by
      intro h0
      apply hdiv
      rw [← ZMod.natCast_eq_zero_iff, ← hxt, h0]
      simp
    obtain ⟨d, hd, hv⟩ := v_surj hn1 hper hpos ht.le
    have hwpos : 0 < w n a d := by
      rw [w_pos_iff hn1]
      by_contra hc
      push Not at hc
      apply ht0
      rw [← hv]
      exact sum_eq_zero fun i hi => by rw [Nat.le_zero.1 (hc i (mem_range.1 hi)), zero_mul]
    have hwm : (w n a d : ZMod (N n a)) = m := by
      rw [w_cong hper hpos, hv, ← hxt]
      push_cast
      rfl
    have hwle := w_le hn1 hper hpos hd
    have hmod : w n a d ≡ m [MOD N n a] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hwm
    have hle : w n a d ≤ m := by
      by_contra h
      push Not at h
      have hd' : N n a ∣ w n a d - m := (Nat.modEq_iff_dvd' h.le).1 hmod.symm
      have := Nat.le_of_dvd (by omega) hd'
      omega
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).1 hmod
    have := InS_add_mul_N hn1 hper hpos (InS_w d) hwpos k
    convert this using 1
    rw [mul_comm] at hk
    omega

/-- **MO 292507 (Hailong Dao).** For `n ≥ 2` and positive integers `a₀, …, aₙ₋₁` (read mod `n`) with
`gcd (x₀, …, xₙ₋₁) = 1`, the number `(n - 1) N` is not in `S` and every larger integer is: the
Frobenius number of `⟨x₀, …, xₙ₋₁⟩` is `(n - 1)(a₀a₁⋯aₙ₋₁ - 1)`. -/
theorem frobenius (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℕ) (hper : ∀ i, a (i + n) = a i)
    (hpos : ∀ i, 0 < a i) (hgcd : (range n).gcd (x n a) = 1) :
    ¬ InS n a ((n - 1) * N n a) ∧ ∀ m, (n - 1) * N n a < m → InS n a m :=
  ⟨not_InS hn hper hpos hgcd, fun _ hm => InS_of_gt hn hper hpos hgcd hm⟩

/-! ## The example `a = (1, 2, 3)` -/

/-- `a = (1, 2, 3)` repeated with period `3`. -/
def a123 (i : ℕ) : ℕ := if i % 3 = 0 then 1 else if i % 3 = 1 then 2 else 3

lemma a123_periodic (i : ℕ) : a123 (i + 3) = a123 i := by simp [a123]

lemma a123_pos (i : ℕ) : 0 < a123 i := by unfold a123; split_ifs <;> norm_num

/-- The generators: `x₀ = 1 + 1 + 1·2 = 4`, `x₁ = 1 + 2 + 2·3 = 9`, `x₂ = 1 + 3 + 3·1 = 7`. -/
theorem generators123 : x 3 a123 0 = 4 ∧ x 3 a123 1 = 9 ∧ x 3 a123 2 = 7 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [x, a123, sum_range_succ, prod_range_succ]

lemma gcd123 : (range 3).gcd (x 3 a123) = 1 := by
  obtain ⟨h0, h1, h2⟩ := generators123
  rw [show range 3 = {0, 1, 2} by rfl, gcd_insert, gcd_insert, gcd_singleton, h0, h1, h2]
  decide

lemma N123 : N 3 a123 = 5 := by simp [N, P, a123, prod_range_succ]

/-- **Example**: `⟨4, 9, 7⟩` has Frobenius number `10 = (3 - 1)(1·2·3 - 1)`, from `frobenius`. -/
theorem example123 : ¬ InS 3 a123 10 ∧ ∀ m, 10 < m → InS 3 a123 m := by
  have := frobenius 3 (by norm_num) a123 a123_periodic a123_pos gcd123
  rwa [N123] at this

end Frobenius292507
