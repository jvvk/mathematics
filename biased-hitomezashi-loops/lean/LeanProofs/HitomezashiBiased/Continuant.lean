import Mathlib

/-!
# Biased hitomezashi loops: the continuant algebra

Weighted Dyck paths in which an up-step leaving level `i` carries weight `a i` (and down-steps carry
weight `1`) have, by the Continued Fraction Theorem (Flajolet and Sedgewick, *Analytic Combinatorics*,
Proposition V.3(ii)), the height-`≤ k` generating function `P (k+1) / Q (k+1)`, where `P` and `Q` are the
continuants below. This file proves the algebra that the paper builds on top of that citation:

* the Casoratian `P (h+1) Q h - P h Q (h+1) = ∏_{i<h} a i`, hence the exact-height weight
  `excHeight a k = (∏_{i<k} a i) / (Q k Q (k+1))`;
* closed forms of `Q` for the alternating weights `q², p², q², p², …` with `p + q = 1`
  (the discriminant of the two-step transfer matrix vanishes identically);
* the two closed forms for the height-`k` vertical factor `X p k` of the paper.
-/

namespace HitomezashiBiased

open Finset

/-- Denominator continuant: `Q 0 = Q 1 = 1`, `Q (h+2) = Q (h+1) - a h * Q h`. -/
def Q (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (h + 2) => Q a (h + 1) - a h * Q a h

/-- Numerator continuant: `P 0 = 0`, `P 1 = 1`, `P (h+2) = P (h+1) - a h * P h`. -/
def P (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | (h + 2) => P a (h + 1) - a h * P a h

/-- Casoratian of the two continuants. -/
theorem casoratian (a : ℕ → ℝ) (h : ℕ) :
    P a (h + 1) * Q a h - P a h * Q a (h + 1) = ∏ i ∈ range h, a i := by
  induction h with
  | zero => simp [P, Q]
  | succ h ih =>
    rw [prod_range_succ, ← ih]
    show (P a (h + 1) - a h * P a h) * Q a (h + 1) - P a (h + 1) * (Q a (h + 1) - a h * Q a h) = _
    ring

/-- Weight of the Dyck paths of height exactly `k`: difference of consecutive convergents
(the height-`≤ k` weight is `P (k+1) / Q (k+1)`; for `k = 0` the subtracted term is `P 0 / Q 0 = 0`). -/
noncomputable def excHeight (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  P a (k + 1) / Q a (k + 1) - P a k / Q a k

theorem excHeight_eq (a : ℕ → ℝ) (k : ℕ) (h0 : Q a k ≠ 0) (h1 : Q a (k + 1) ≠ 0) :
    excHeight a k = (∏ i ∈ range k, a i) / (Q a k * Q a (k + 1)) := by
  rw [excHeight, ← casoratian, div_sub_div _ _ h1 h0]
  congr 1 <;> ring

/-- Alternating level weights: `s` on even levels, `t` on odd levels. -/
def alt (s t : ℝ) (i : ℕ) : ℝ := if Even i then s else t

theorem prod_alt_even (s t : ℝ) (j : ℕ) : ∏ i ∈ range (2 * j), alt s t i = (s * t) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih]
    simp [alt, pow_succ]
    ring

theorem prod_alt_odd (s t : ℝ) (j : ℕ) :
    ∏ i ∈ range (2 * j + 1), alt s t i = (s * t) ^ j * s := by
  rw [prod_range_succ, prod_alt_even]
  simp [alt]

/-- Closed forms of the continuant for the weights `q², p², q², …` (`p + q = 1`, `r = p q`):
`Q (2j+1) = (j+1) r^j` and `r Q (2j) = r^j p (j+q)`. -/
theorem Q_alt (p q : ℝ) (hpq : p + q = 1) (hr : p * q ≠ 0) (j : ℕ) :
    Q (alt (q ^ 2) (p ^ 2)) (2 * j + 1) = (j + 1) * (p * q) ^ j ∧
    p * q * Q (alt (q ^ 2) (p ^ 2)) (2 * j) = (p * q) ^ j * p * (j + q) := by
  induction j with
  | zero => simp [Q]
  | succ j ih =>
    obtain ⟨h1, h0⟩ := ih
    have e2 : Q (alt (q ^ 2) (p ^ 2)) (2 * (j + 1)) =
        Q (alt (q ^ 2) (p ^ 2)) (2 * j + 1) - q ^ 2 * Q (alt (q ^ 2) (p ^ 2)) (2 * j) := by
      rw [show 2 * (j + 1) = 2 * j + 2 by ring]
      simp [Q, alt]
    have e3 : Q (alt (q ^ 2) (p ^ 2)) (2 * (j + 1) + 1) =
        Q (alt (q ^ 2) (p ^ 2)) (2 * (j + 1)) - p ^ 2 * Q (alt (q ^ 2) (p ^ 2)) (2 * j + 1) := by
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, show 2 * (j + 1) = (2 * j + 1) + 1 by ring]
      simp [Q, alt]
    have hq : q = 1 - p := by linarith
    have E2 : p * q * Q (alt (q ^ 2) (p ^ 2)) (2 * (j + 1)) = (p * q) ^ (j + 1) * p * ((j + 1 : ℕ) + q) := by
      rw [e2, mul_sub, h1, show p * q * (q ^ 2 * Q (alt (q ^ 2) (p ^ 2)) (2 * j)) =
        q ^ 2 * (p * q * Q (alt (q ^ 2) (p ^ 2)) (2 * j)) by ring, h0, hq]
      push_cast; ring
    refine ⟨?_, by exact_mod_cast E2⟩
    apply mul_left_cancel₀ hr
    rw [e3, mul_sub, E2, h1, hq]
    push_cast; ring

/-- The vertical factor of the paper: the sum, over Dyck paths `P` of height exactly `k`, of
`u^{1+odd(P)} v^{even(P)} + v^{1+odd(P)} u^{even(P)}` with `u = p²`, `v = q²`. -/
noncomputable def X (p : ℝ) (k : ℕ) : ℝ :=
  p ^ 2 * excHeight (alt ((1 - p) ^ 2) (p ^ 2)) k + (1 - p) ^ 2 * excHeight (alt (p ^ 2) ((1 - p) ^ 2)) k

private lemma sq_pow (x y : ℝ) (j : ℕ) : (x ^ 2 * y ^ 2) ^ j = ((y * x) ^ j) ^ 2 := by
  rw [show x ^ 2 * y ^ 2 = (y * x) ^ 2 by ring, ← pow_mul, ← pow_mul, Nat.mul_comm]

section closed
variable {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
include hp0 hp1

private lemma Qa (j : ℕ) :
    Q (alt ((1 - p) ^ 2) (p ^ 2)) (2 * j + 1) = (j + 1) * (p * (1 - p)) ^ j ∧
    p * (1 - p) * Q (alt ((1 - p) ^ 2) (p ^ 2)) (2 * j) = (p * (1 - p)) ^ j * p * (j + (1 - p)) :=
  Q_alt p (1 - p) (by ring) (by nlinarith) j

private lemma Qb (j : ℕ) :
    Q (alt (p ^ 2) ((1 - p) ^ 2)) (2 * j + 1) = (j + 1) * (p * (1 - p)) ^ j ∧
    p * (1 - p) * Q (alt (p ^ 2) ((1 - p) ^ 2)) (2 * j) = (p * (1 - p)) ^ j * (1 - p) * (j + p) := by
  have := Q_alt (1 - p) p (by ring) (by nlinarith) j
  rw [show (1 - p) * p = p * (1 - p) by ring] at this
  exact this

/-- `X p (2j) = r/(j+1) · (p/(j+q) + q/(j+p))`. -/
theorem X_even (j : ℕ) :
    X p (2 * j) = p * (1 - p) / (j + 1) * (p / (j + (1 - p)) + (1 - p) / (j + p)) := by
  have hr : 0 < p * (1 - p) := by nlinarith
  have hj : (0 : ℝ) ≤ j := j.cast_nonneg
  obtain ⟨a1, a0⟩ := Qa hp0 hp1 j
  obtain ⟨b1, b0⟩ := Qb hp0 hp1 j
  have qa0 : Q (alt ((1 - p) ^ 2) (p ^ 2)) (2 * j) = (p * (1 - p)) ^ j * p * (j + (1 - p)) / (p * (1 - p)) := by
    rw [eq_div_iff hr.ne', mul_comm]; exact a0
  have qb0 : Q (alt (p ^ 2) ((1 - p) ^ 2)) (2 * j) = (p * (1 - p)) ^ j * (1 - p) * (j + p) / (p * (1 - p)) := by
    rw [eq_div_iff hr.ne', mul_comm]; exact b0
  have hrj : (p * (1 - p)) ^ j ≠ 0 := by positivity
  have ha : (j : ℝ) + (1 - p) ≠ 0 := by linarith
  have hb : (j : ℝ) + p ≠ 0 := by linarith
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  rw [X, excHeight_eq _ _ (by rw [qa0]; positivity) (by rw [a1]; positivity),
    excHeight_eq _ _ (by rw [qb0]; positivity) (by rw [b1]; positivity),
    prod_alt_even, prod_alt_even, qa0, qb0, a1, b1]
  rw [sq_pow, sq_pow, show (1 - p) * p = p * (1 - p) by ring]
  generalize (p * (1 - p)) ^ j = R at *
  field_simp

/-- `X p (2j+1) = r/(j+1) · (q/(j+1+q) + p/(j+1+p))`. -/
theorem X_odd (j : ℕ) :
    X p (2 * j + 1) = p * (1 - p) / (j + 1) * ((1 - p) / (j + 1 + (1 - p)) + p / (j + 1 + p)) := by
  have hr : 0 < p * (1 - p) := by nlinarith
  have hj : (0 : ℝ) ≤ j := j.cast_nonneg
  obtain ⟨a1, -⟩ := Qa hp0 hp1 j
  obtain ⟨b1, -⟩ := Qb hp0 hp1 j
  obtain ⟨-, a2⟩ := Qa hp0 hp1 (j + 1)
  obtain ⟨-, b2⟩ := Qb hp0 hp1 (j + 1)
  have qa2 : Q (alt ((1 - p) ^ 2) (p ^ 2)) (2 * j + 1 + 1) =
      (p * (1 - p)) ^ j * p * (j + 1 + (1 - p)) := by
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
    apply mul_left_cancel₀ hr.ne'
    rw [a2]; push_cast; ring
  have qb2 : Q (alt (p ^ 2) ((1 - p) ^ 2)) (2 * j + 1 + 1) =
      (p * (1 - p)) ^ j * (1 - p) * (j + 1 + p) := by
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
    apply mul_left_cancel₀ hr.ne'
    rw [b2]; push_cast; ring
  have hrj : (p * (1 - p)) ^ j ≠ 0 := by positivity
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  have ha : (j : ℝ) + 1 + (1 - p) ≠ 0 := by linarith
  have hb : (j : ℝ) + 1 + p ≠ 0 := by linarith
  rw [X, excHeight_eq _ _ (by rw [a1]; positivity) (by rw [qa2]; positivity),
    excHeight_eq _ _ (by rw [b1]; positivity) (by rw [qb2]; positivity),
    prod_alt_odd, prod_alt_odd, a1, b1, qa2, qb2]
  rw [sq_pow, sq_pow, show (1 - p) * p = p * (1 - p) by ring]
  generalize (p * (1 - p)) ^ j = R at *
  field_simp

end closed

end HitomezashiBiased
