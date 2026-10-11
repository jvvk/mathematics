import Mathlib

/-!
# Bogner's strange operator carries a √2 twist: the elementary algebra

The note's main theorem is conditional and rests on `p`-adic Frobenius structures (Beukers and
Vlasenko), which are not formalised. This file checks the elementary algebra it uses.

* `hadamard_rec`: if `u` satisfies the recurrence of the third order operator `L`, then
  `binom(2n, n) u_n` satisfies the recurrence of Bogner's operator `P`
  (`P = I ⋆ L`).
* `cp_mod`, `cp_fourth`: `c_p = (2/p) 2^((p-1)/2)` is `1` modulo `p` and `c_p⁴ = 4^(p-1)`
  (the Frobenius lift dictated by the cusp).
* `w_mul`: the twisted multicover weights satisfy `w_d(pk) = c_p^(dk) w_d(k)`, the identity behind
  twisted multicover integrality.
* `choose_vanish`: `p ∣ binom(2p - 2, p - 1)` for odd primes, the Hasse-Witt entry of
  the two Laurent-model obstructions.
* `prime3_reductions`, `prime3_contradiction`: the arithmetic modulo `9` of the
  obstruction at the prime `3`.
-/

namespace StrangeOperator

open Nat

/-! ## The Hadamard product with `binom(2n, n)` -/

/-- The recurrence of `L = θ³ - 4x(2θ+1)(5θ²+5θ+2) + 48x²(θ+1)(3θ+2)(3θ+4)`. -/
def RecL (u : ℕ → ℚ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ((n : ℚ) + 1) ^ 3 * u (n + 1) =
    4 * (2 * n + 1) * (5 * n ^ 2 + 5 * n + 2) * u n - 48 * n * (3 * n - 1) * (3 * n + 1) * u (n - 1)

/-- The recurrence of
`P = θ⁴ - 8x(2θ+1)²(5θ²+5θ+2) + 192x²(2θ+1)(3θ+2)(3θ+4)(2θ+3)`. -/
def RecP (v : ℕ → ℚ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ((n : ℚ) + 1) ^ 4 * v (n + 1) =
    8 * (2 * n + 1) ^ 2 * (5 * n ^ 2 + 5 * n + 2) * v n
      - 192 * (2 * n - 1) * (3 * n - 1) * (3 * n + 1) * (2 * n + 1) * v (n - 1)

lemma centralBinom_succ_q (n : ℕ) :
    ((n : ℚ) + 1) * (centralBinom (n + 1) : ℚ) = 2 * (2 * n + 1) * centralBinom n := by
  exact_mod_cast succ_mul_centralBinom_succ n

theorem hadamard_rec (u : ℕ → ℚ) (hu : RecL u) :
    RecP fun n => (centralBinom n : ℚ) * u n := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 := centralBinom_succ_q (m + 1)
  have h0 := centralBinom_succ_q m
  have hr := hu (m + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hr
  push_cast at h1 h0 hr ⊢
  have hm : (m : ℚ) + 1 ≠ 0 := by positivity
  have hm2 : (m : ℚ) + 1 + 1 ≠ 0 := by positivity
  -- write both central binomials through `c = centralBinom m`
  have e1 : (centralBinom (m + 1 + 1) : ℚ) =
      2 * (2 * ((m : ℚ) + 1) + 1) * centralBinom (m + 1) / ((m : ℚ) + 1 + 1) := by
    field_simp; linarith
  have e0 : (centralBinom (m + 1) : ℚ) =
      2 * (2 * (m : ℚ) + 1) * centralBinom m / ((m : ℚ) + 1) := by
    field_simp; linarith
  rw [e1, e0]
  set c : ℚ := (centralBinom m : ℚ)
  have key : ((m : ℚ) + 1 + 1) ^ 4 * (2 * (2 * ((m : ℚ) + 1) + 1)
      * (2 * (2 * (m : ℚ) + 1) * c / ((m : ℚ) + 1)) / ((m : ℚ) + 1 + 1) * u (m + 1 + 1)) =
      (4 * (2 * (m : ℚ) + 3) * (2 * m + 1) * c / ((m : ℚ) + 1))
        * (((m : ℚ) + 1 + 1) ^ 3 * u (m + 1 + 1)) := by
    field_simp; ring
  rw [key, hr]
  field_simp
  ring

/-! ## The twist constant -/

/-- `c_p = (2/p) 2^((p-1)/2)`. -/
def cp (p : ℕ) : ℤ := jacobiSym 2 p * 2 ^ ((p - 1) / 2)

lemma two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ((2 : ℤ) : ZMod p) ≠ 0 := by
  intro h
  have : (p : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).1 h
  have h2 : p ∣ 2 := by exact_mod_cast this
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h2)

lemma jac_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : jacobiSym 2 p ^ 2 = 1 := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  exact legendreSym.sq_one p (two_ne_zero_zmod p hp)

/-- `c_p ≡ 1 (mod p)`, by Euler's criterion. -/
theorem cp_mod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ((cp p : ℤ) : ZMod p) = 1 := by
  have he : (legendreSym p 2 : ZMod p) = (2 : ZMod p) ^ (p / 2) := by
    have := legendreSym.eq_pow p (2 : ℤ)
    simpa using this
  have hodd : p / 2 = (p - 1) / 2 := by
    have := (Fact.out : p.Prime).eq_one_or_self_of_dvd 2
    omega
  have hsq := jac_sq p hp
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hsq
  unfold cp
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  push_cast
  rw [← hodd, ← he, ← sq]
  exact_mod_cast congrArg (fun z : ℤ => (z : ZMod p)) hsq

/-- `c_p⁴ = 4^(p-1)`. -/
theorem cp_fourth (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : cp p ^ 4 = 4 ^ (p - 1) := by
  have hsq := jac_sq p hp
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨a, ha⟩ := hodd
  subst ha
  unfold cp
  simp only [Nat.add_sub_cancel, Nat.mul_div_cancel_left a (by norm_num : 0 < 2)]
  have : (jacobiSym 2 (2 * a + 1)) ^ 4 = 1 := by
    calc (jacobiSym 2 (2 * a + 1)) ^ 4 = (jacobiSym 2 (2 * a + 1) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hsq]; norm_num
  rw [mul_pow, this, one_mul, ← pow_mul, show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
  ring_nf

/-! ## The multicover weights -/

/-- `w_d(k)`: `(2/k)^d 2^(d(k-1)/2)` for odd `k`; for even `k`, `2^(d(k-1)/2)` if `d` is even and
`0` if `d` is odd. -/
def w (d k : ℕ) : ℤ :=
  if k % 2 = 1 then jacobiSym 2 k ^ d * 2 ^ (d * (k - 1) / 2)
  else if d % 2 = 0 then 2 ^ (d * (k - 1) / 2) else 0

/-- Weight compatibility, the identity behind the twisted multicover formula:
`w_d(pk) = c_p^(dk) w_d(k)` for every odd prime `p` and `k ≥ 1`. -/
theorem w_mul (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (d k : ℕ) (hk : 0 < k) :
    w d (p * k) = cp p ^ (d * k) * w d k := by
  have hsq := jac_sq p hp
  obtain ⟨a, rfl⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have hpa : (2 * a + 1 - 1) / 2 = a := by omega
  unfold w cp
  rw [hpa]
  rcases Nat.even_or_odd k with ⟨b, hb⟩ | ⟨b, hb⟩
  · -- k even
    subst hb
    have hk1 : (2 * a + 1) * (b + b) % 2 = 0 := by
      rw [show (2 * a + 1) * (b + b) = 2 * ((2 * a + 1) * b) by ring]; simp
    have hk2 : (b + b) % 2 = 0 := by omega
    simp only [hk1, hk2, zero_ne_one, ite_false]
    split_ifs with hd
    · obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e := ⟨d / 2, by omega⟩
      have hj : (jacobiSym 2 (2 * a + 1) ^ (2 * e)) ^ (b + b) = 1 := by
        rw [pow_mul, hsq, one_pow, one_pow]
      have ex : 2 * e * ((2 * a + 1) * (b + b) - 1) / 2 =
          a * (2 * e * (b + b)) + 2 * e * (b + b - 1) / 2 := by
        rw [Nat.mul_assoc 2 e, Nat.mul_div_cancel_left _ two_pos, Nat.mul_assoc 2 e (b + b - 1),
          Nat.mul_div_cancel_left _ two_pos]
        have hb0 : 1 ≤ b + b := by omega
        have hb1 : 1 ≤ (2 * a + 1) * (b + b) := by nlinarith
        zify [hb0, hb1]
        ring
      rw [ex, mul_pow, ← pow_mul, pow_mul (jacobiSym 2 (2 * a + 1)) (2 * e) (b + b), hj, one_mul,
        pow_add]
    · simp
  · -- k odd
    subst hb
    have hk1 : (2 * a + 1) * (2 * b + 1) % 2 = 1 := by
      rw [Nat.mul_mod]; simp [Nat.add_mod]
    have hk2 : (2 * b + 1) % 2 = 1 := by omega
    simp only [hk1, hk2, ite_true]
    rw [jacobiSym.mul_right]
    have hj : jacobiSym 2 (2 * a + 1) ^ (d * (2 * b + 1)) = jacobiSym 2 (2 * a + 1) ^ d := by
      rw [show d * (2 * b + 1) = 2 * (d * b) + d by ring, pow_add, pow_mul, hsq, one_pow, one_mul]
    rw [mul_pow, mul_pow, ← pow_mul, hj]
    have e1 : d * ((2 * a + 1) * (2 * b + 1) - 1) / 2 = d * (2 * a * b + a + b) := by
      have : (2 * a + 1) * (2 * b + 1) - 1 = 2 * (2 * a * b + a + b) := by ring_nf; omega
      rw [this, Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    have e2 : d * (2 * b + 1 - 1) / 2 = d * b := by
      rw [show 2 * b + 1 - 1 = 2 * b by omega, Nat.mul_left_comm,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    rw [e1, e2]
    have : (2 : ℤ) ^ (d * (2 * a * b + a + b)) = (2 ^ a) ^ (d * (2 * b + 1)) * 2 ^ (d * b) := by
      rw [← pow_mul, ← pow_add]; ring_nf
    rw [this]; ring

/-! ## A vanishing binomial coefficient -/

/-- `p ∣ binom(2p - 2, p - 1)` for every prime `p ≥ 3`. -/
theorem choose_vanish (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) : p ∣ (2 * p - 2).choose (p - 1) :=
  hp.dvd_choose (by omega) (by omega) (by omega)

/-! ## The prime `3` -/

/-- The reductions modulo `9` in the prime `3` obstruction: `9 A₃,₃ ≡ 4 + α₁` and
`9 A₂,₉ ≡ 7 + 7α₁`. -/
theorem prime3_reductions :
    ((-114512 : ℤ) : ZMod 9) = 4 ∧ ((766216 : ℤ) : ZMod 9) = 1 ∧
    (6125 : ZMod 9) * 7 = (64339413849976508288 : ZMod 9) ∧
    (175 : ZMod 9) * 7 = -(539829813570751232 : ZMod 9) := by
  decide

/-- The two conditions are incompatible. -/
theorem prime3_contradiction (α : ZMod 9) : ¬ (4 + α = 0 ∧ 7 + 7 * α = 0) := by
  revert α; decide

end StrangeOperator
