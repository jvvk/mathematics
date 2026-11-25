import Mathlib

/-!
# Mahonian superdiagonals: definitions

Notation follows `superdiagonals.tex` (the note proving Conjecture 15 of Claesson, Franklín and
Steingrímsson, EJC 30(4) 2023). Everything lives in `PowerSeries ℤ` or `Polynomial ℤ`; no field
division is used.
-/

set_option linter.style.longLine false

open PowerSeries

namespace Mahonian

noncomputable section

/-- The geometric series `1 + X + X^2 + ⋯ = 1/(1-X)` (the paper's `φ`). -/
def geom : PowerSeries ℤ := mk 1

/-- The finite Euler product `E N = ∏_{j=1}^{N} (1 - X^j)`. -/
def E (N : ℕ) : PowerSeries ℤ := ∏ j ∈ Finset.range N, (1 - X ^ (j + 1))

/-- Euler's coefficients `f_s = [q^s] ∏_{j ≥ 1} (1 - q^j)`, read off the finite product `E s`
(stability for larger `N` is `coeff_E_stable`). -/
def f (s : ℕ) : ℤ := coeff s (E s)

/-- Euler's product `F = ∏_{j ≥ 1} (1 - q^j) = ∑ f_s q^s`. -/
def F : PowerSeries ℤ := mk f

/-- `A(n,k) = [q^k] F(q) (1-q)^{-n}` for `n ≥ 0`. -/
def A (n k : ℕ) : ℤ := coeff k (F * geom ^ n)

/-- `A(-r,k) = [q^k] F(q) (1-q)^r` for `r ≥ 1` (the paper's `A` at a negative first argument). -/
def Aneg (r k : ℕ) : ℤ := coeff k (F * (1 - X) ^ r)

/-- The Mahonian polynomial `∏_{j=1}^{n} (1 + q + ⋯ + q^{j-1})`. Its coefficients are the Mahonian numbers
`I_n(k)`, the number of permutations of `[n]` with `k` inversions; this is the standard generating function,
and the combinatorial equivalence with inversion counts is not formalised here. -/
def mahonian (n : ℕ) : Polynomial ℤ :=
  ∏ j ∈ Finset.range n, ∑ t ∈ Finset.range (j + 1), (Polynomial.X : Polynomial ℤ) ^ t

/-- The Mahonian number `I_n(k) = [q^k] mahonian n`. -/
def I (n k : ℕ) : ℤ := (mahonian n).coeff k

/-- The superdiagonal series `S_{-i}(x) = ∑_{n ≥ 0} I_n(n+i) x^n`. -/
def Sneg (i : ℕ) : PowerSeries ℤ := mk fun n => I n (n + i)

/-- The main-diagonal series `S_0(x) = ∑_{n ≥ 0} I_n(n) x^n`. -/
def S0 : PowerSeries ℤ := mk fun n => I n n

/-- The Catalan generating function `C(x) = ∑ catalan n x^n`. -/
def Cat : PowerSeries ℤ := mk fun n => (catalan n : ℤ)

/-- `C(x)^{-1} = 1 - x C(x)` (see `Cinv_mul_Cat`). -/
def Cinv : PowerSeries ℤ := 1 - X * Cat

/-- The correction terms of Lemma 2: `c_n = I_n(n+i) - A(n,n+i) - ∑_{t=0}^{i-1} A(n,t)`. -/
def c (i n : ℕ) : ℤ := I n (n + i) - A n (n + i) - ∑ t ∈ Finset.range i, A n t

/-- The explicit polynomial `P_i` of Theorem 1 of the note:
`P_i = (1-x)^i (∑_{n=0}^{i-2} c_n x^{n+i} - ∑_{r=1}^{i} A(-r,i-r) x^{i-r})
  + x^i ∑_{t=0}^{i-1} (f_t (1-x)^{i-1} + ∑_{s=0}^{t-1} f_s x (1-x)^{i-t+s-1})`. -/
def P (i : ℕ) : Polynomial ℤ :=
  (1 - Polynomial.X) ^ i * (∑ n ∈ Finset.range (i - 1), Polynomial.C (c i n) * Polynomial.X ^ (n + i)
      - ∑ r ∈ Finset.Icc 1 i, Polynomial.C (Aneg r (i - r)) * Polynomial.X ^ (i - r))
    + Polynomial.X ^ i * ∑ t ∈ Finset.range i,
        (Polynomial.C (f t) * (1 - Polynomial.X) ^ (i - 1)
          + ∑ s ∈ Finset.range t, Polynomial.C (f s) * Polynomial.X * (1 - Polynomial.X) ^ (i - t + s - 1))

/-- The geometric series inverts `1 - X`. -/
lemma geom_mul_one_sub : geom * (1 - X) = 1 := mk_one_mul_one_sub_eq_one ℤ

lemma one_sub_mul_geom : (1 - X) * geom = 1 := by rw [mul_comm, geom_mul_one_sub]

/-- Sanity check on `Cinv`: it is the inverse of the Catalan series. -/
theorem Cinv_mul_Cat : Cinv * Cat = 1 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ)) catalanSeries_sq_mul_X_add_one
  have hc : PowerSeries.map (Nat.castRingHom ℤ) catalanSeries = Cat := by
    ext n; simp [Cat, catalanSeries_coeff]
  simp only [map_add, map_mul, map_pow, map_X, map_one, hc] at h
  rw [Cinv]; linear_combination (-1 : PowerSeries ℤ) * h

end

end Mahonian
