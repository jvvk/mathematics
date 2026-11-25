import LeanProofs.Mahonian.Truncation
import LeanProofs.Mahonian.Columns

/-!
# Theorem 1 of the note: assembly

Multiply Lemma 2 by `x^{n+i}` and sum over `n`; Lemma 3 (hypothesis `H3`) turns the first term into
`C^{-i} S_0 - ∑_{r=1}^{i} A(-r,i-r) x^{i-r}`, and Lemma 4 turns the second into `x^i` times a
rational function with denominator dividing `(1-x)^i`. Everything is multiplied through by
`(1-x)^i`, so no division appears.
-/

set_option linter.style.longLine false

open PowerSeries

namespace Mahonian

noncomputable section

/-- **Lemma 3 of the note, multiplied by `x^i` (hypothesis, not formalised).** For `i ≥ 0`,
`x^i ∑_{n≥0} A(n,n+i) x^n + ∑_{r=1}^{i} A(-r,i-r) x^{i-r} = C(x)^{-i} S_0(x)`.

In the note this is Lagrange inversion for Laurent series, Gessel, *Lagrange inversion*, J. Combin. Theory
Ser. A 144 (2016) 212-249, Theorem 2.1.1, eq. (2.1.4), applied with `R = φ = 1/(1-t)`, `w = x C(x)` (so
`w = x φ(w)`) and `ψ(t) = t^{-i} F(t)`, together with the case `i = 0` and `I_n(n) = A(n,n)` (`I_diag`). It is
taken here as an explicit hypothesis; Laurent-series Lagrange inversion is not formalised. -/
def H3 (i : ℕ) : Prop :=
  X ^ i * (mk fun n => A n (n + i)) + ∑ r ∈ Finset.Icc 1 i, C (Aneg r (i - r)) * X ^ (i - r) = Cinv ^ i * S0

/-- `S_0` agrees with the diagonal of `A` (the case `i = 0` of Lemma 2), as used in Lemma 3. -/
theorem S0_eq_diag : S0 = mk fun n => A n n := by
  ext n; simp [S0, I_diag]

/-- `P_i` read as a power series. -/
def Pps (i : ℕ) : PowerSeries ℤ :=
  (1 - X) ^ i * (∑ n ∈ Finset.range (i - 1), C (c i n) * X ^ (n + i)
      - ∑ r ∈ Finset.Icc 1 i, C (Aneg r (i - r)) * X ^ (i - r))
    + X ^ i * ∑ t ∈ Finset.range i,
        (C (f t) * (1 - X) ^ (i - 1) + ∑ s ∈ Finset.range t, C (f s) * X * (1 - X) ^ (i - t + s - 1))

lemma P_coe (i : ℕ) : ((P i : Polynomial ℤ) : PowerSeries ℤ) = Pps i := by
  simp only [P, Pps, ← Polynomial.coeToPowerSeries.ringHom_apply, map_add, map_sub, map_mul, map_pow,
    map_sum, map_one]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C]

/-- Lemma 2 summed over `n`: `S_{-i} = ∑ A(n,n+i) x^n + ∑_{t<i} ∑_n A(n,t) x^n + ∑_{n ≤ i-2} c_n x^n`. -/
lemma Sneg_split (i : ℕ) :
    Sneg i = (mk fun n => A n (n + i)) + ∑ t ∈ Finset.range i, (mk fun n => A n t)
      + ∑ n ∈ Finset.range (i - 1), C (c i n) * X ^ n := by
  ext n
  simp only [Sneg, map_add, map_sum, coeff_mk, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  rw [lemma2 i n]
  congr 1
  split_ifs with h
  · rfl
  · exact c_eq_zero (by omega)

/-- Lemma 4 multiplied by the full denominator `(1-x)^i`, for `t < i`. -/
lemma col_mul {i t : ℕ} (ht : t < i) :
    (1 - X) ^ i * (mk fun n => A n t)
      = C (f t) * (1 - X) ^ (i - 1) + ∑ s ∈ Finset.range t, C (f s) * X * (1 - X) ^ (i - t + s - 1) := by
  rw [show i = (i - 1 - t) + (t + 1) by omega, pow_add, mul_assoc, lemma4, mul_add, Finset.mul_sum]
  have e1 : i - 1 - t + (t + 1) - 1 = (i - 1 - t) + t := by omega
  rw [e1, pow_add]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun s hs => ?_
    have e2 : i - 1 - t + (t + 1) - t + s - 1 = (i - 1 - t) + s := by simp at hs; omega
    rw [e2, pow_add]; ring

/-- **Theorem 1 (Conjecture 15 of Claesson-Franklín-Steingrímsson), conditional on Lemma 3.**
For `i ≥ 1`: `(1-x)^i (x^i S_{-i} - C^{-i} S_0) = P_i`, i.e. `x^i S_{-i} = S_0 C^{-i} + P_i/(1-x)^i`. -/
theorem main (i : ℕ) (h3 : H3 i) :
    (1 - X) ^ i * (X ^ i * Sneg i - Cinv ^ i * S0) = ((P i : Polynomial ℤ) : PowerSeries ℤ) := by
  rw [P_coe, Pps, Sneg_split]
  have e1 : X ^ i * ∑ n ∈ Finset.range (i - 1), C (c i n) * X ^ n
      = ∑ n ∈ Finset.range (i - 1), C (c i n) * (X : PowerSeries ℤ) ^ (n + i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  have e2 : (1 - X) ^ i * ∑ t ∈ Finset.range i, (mk fun n => A n t)
      = ∑ t ∈ Finset.range i, (C (f t) * (1 - X) ^ (i - 1)
          + ∑ s ∈ Finset.range t, C (f s) * X * (1 - X) ^ (i - t + s - 1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t ht => col_mul (Finset.mem_range.mp ht)
  rw [← e1, ← e2]
  unfold H3 at h3
  linear_combination (1 - X) ^ i * h3

end

end Mahonian
