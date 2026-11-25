import LeanProofs.Mahonian.Defs

/-!
# Lemma 2 of the note: truncation of `∏_{j>n} (1-q^j)^{-1}`

The paper writes `∑_k I_n(k) q^k = φ^n F G_n` with `G_n = ∏_{j>n}(1-q^j)^{-1}` and reads off the
partition counts `p_{>n}(m)` for `m ≤ 2n+2`. We follow the same truncation in the inverse direction,
which avoids the infinite product: `φ^n F ≡ (∑_k I_n(k) q^k) · ∏_{j=n+1}^{2n+2} (1-q^j)` modulo
`q^{2n+3}`, and `∏_{j=n+1}^{M} (1-q^j) ≡ 1 - ∑_{m=n+1}^{M} q^m` modulo `q^{2n+3}` (a product of two
factors `q^a q^b` with `n < a < b` has degree at least `2n+3`). This gives `A(n,k) = I_n(k) -
∑_{n<m≤k} I_n(k-m)` for `k ≤ 2n+2` (`A_eq_trunc`), which is the triangular inverse of the paper's
`I_n(k) = ∑_m p_{>n}(m) A(n,k-m)`, and from it the two facts of Lemma 2.
-/

set_option linter.style.longLine false

open PowerSeries

namespace Mahonian

noncomputable section

/-- Coefficients below `m` only see a series modulo `X^m`. -/
lemma coeff_mul_eq_of_dvd {m k : ℕ} {P Q : PowerSeries ℤ} (h : X ^ m ∣ P - Q) (hk : k < m)
    (G : PowerSeries ℤ) : coeff k (P * G) = coeff k (Q * G) := by
  obtain ⟨D, hD⟩ := h
  have : P * G = Q * G + X ^ m * (D * G) := by linear_combination G * hD
  rw [this, map_add, coeff_X_pow_mul', ite_eq_right (by omega), add_zero]

/-- Stability of the finite Euler products: `E (N + d) ≡ E N` modulo `X^(N+1)`. -/
lemma E_stable (N d : ℕ) : X ^ (N + 1) ∣ E (N + d) - E N := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 : X ^ (N + 1) ∣ E (N + d) * X ^ (N + d + 1) :=
      Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _
    have : E (N + (d + 1)) - E N = (E (N + d) - E N) - E (N + d) * X ^ (N + d + 1) := by
      rw [E, ← add_assoc, Finset.prod_range_succ, ← E]; ring
    rw [this]; exact dvd_sub ih h1

lemma coeff_E_stable {s N : ℕ} (h : s ≤ N) : coeff s (E N) = f s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have := coeff_mul_eq_of_dvd (E_stable s d) (Nat.lt_succ_self s) 1
  simpa [f] using this

/-- `F ≡ E M` modulo `X^(k+1)` whenever `k ≤ M`. -/
lemma F_sub_E_dvd {k M : ℕ} (h : k ≤ M) : X ^ (k + 1) ∣ F - E M := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, F, coeff_mk, coeff_E_stable (by omega), sub_self]

/-- `A(n,k)` may be computed from any finite Euler product `E M` with `M ≥ k`. -/
lemma A_eq_E {n k M : ℕ} (h : k ≤ M) : A n k = coeff k (E M * geom ^ n) :=
  coeff_mul_eq_of_dvd (F_sub_E_dvd h) (Nat.lt_succ_self k) _

/-- The Mahonian polynomial as a power series: `φ^n · E n`, i.e. `∏_{j=1}^n (1-q^j)/(1-q)` (eq. (2) with the
Euler factor kept finite). -/
lemma mahonian_coe (n : ℕ) : ((mahonian n : Polynomial ℤ) : PowerSeries ℤ) = E n * geom ^ n := by
  have hj : ∀ j : ℕ, (∑ t ∈ Finset.range (j + 1), (X : PowerSeries ℤ) ^ t) = (1 - X ^ (j + 1)) * geom := by
    intro j
    rw [← geom_sum_mul_neg, mul_assoc, one_sub_mul_geom, mul_one]
  have hc : ((mahonian n : Polynomial ℤ) : PowerSeries ℤ)
      = ∏ j ∈ Finset.range n, ∑ t ∈ Finset.range (j + 1), (X : PowerSeries ℤ) ^ t := by
    rw [mahonian, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [Polynomial.coeToPowerSeries.ringHom_apply]
  rw [hc, Finset.prod_congr rfl fun j _ => hj j, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, E]

/-- The tail product `∏_{j=n+1}^{n+d} (1 - X^j)`. -/
def Q (n d : ℕ) : PowerSeries ℤ := ∏ j ∈ Finset.range d, (1 - X ^ (n + 1 + j))

lemma E_add (n d : ℕ) : E (n + d) = E n * Q n d := by
  rw [E, Finset.prod_range_add, ← E, Q]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  ring_nf

/-- The truncation: `∏_{j=n+1}^{n+d} (1 - X^j) ≡ 1 - ∑_{m=n+1}^{n+d} X^m` modulo `X^(2n+3)`. -/
lemma Q_trunc (n d : ℕ) :
    X ^ (2 * n + 3) ∣ Q n d - (1 - ∑ j ∈ Finset.range d, X ^ (n + 1 + j)) := by
  induction d with
  | zero => simp [Q]
  | succ d ih =>
    have hS : X ^ (2 * n + 3) ∣ (∑ j ∈ Finset.range d, (X : PowerSeries ℤ) ^ (n + 1 + j)) * X ^ (n + 1 + d) := by
      rw [Finset.sum_mul]
      refine Finset.dvd_sum fun j hj => ?_
      rw [← pow_add]
      exact pow_dvd_pow _ (by simp at hj; omega)
    have : Q n (d + 1) - (1 - ∑ j ∈ Finset.range (d + 1), (X : PowerSeries ℤ) ^ (n + 1 + j))
        = (Q n d - (1 - ∑ j ∈ Finset.range d, X ^ (n + 1 + j))) * (1 - X ^ (n + 1 + d))
          + (∑ j ∈ Finset.range d, X ^ (n + 1 + j)) * X ^ (n + 1 + d) := by
      rw [Q, Finset.prod_range_succ, ← Q, Finset.sum_range_succ]; ring
    rw [this]
    exact dvd_add (Dvd.dvd.mul_right ih _) hS

/-- **Truncation identity.** For `k ≤ 2n+2`, `A(n,k) = I_n(k) - ∑_{m=n+1}^{2n+2} [m ≤ k] I_n(k-m)`. -/
theorem A_eq_trunc {n k : ℕ} (hk : k ≤ 2 * n + 2) :
    A n k = I n k - ∑ j ∈ Finset.range (n + 2),
      if n + 1 + j ≤ k then I n (k - (n + 1 + j)) else 0 := by
  have h1 : A n k = coeff k (((mahonian n : Polynomial ℤ) : PowerSeries ℤ) * Q n (n + 2)) := by
    rw [A_eq_E (M := n + (n + 2)) (by omega), E_add, mahonian_coe]; ring_nf
  have h2 := coeff_mul_eq_of_dvd (Q_trunc n (n + 2)) (k := k) (by omega)
    ((mahonian n : Polynomial ℤ) : PowerSeries ℤ)
  rw [h1, mul_comm, h2, sub_mul, one_mul, map_sub, Finset.sum_mul, map_sum, Polynomial.coeff_coe]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_X_pow_mul', Polynomial.coeff_coe, I]

lemma A_eq_I_of_le {n k : ℕ} (hk : k ≤ n) : A n k = I n k := by
  rw [A_eq_trunc (by omega), sub_eq_self]
  exact Finset.sum_eq_zero fun j _ => ite_eq_right (by omega)

/-- The case `i = 0` of Lemma 2: `I_n(n) = A(n,n)`, so `S_0 = ∑ A(n,n) x^n`. -/
theorem I_diag (n : ℕ) : I n n = A n n := (A_eq_I_of_le le_rfl).symm

lemma I_zero (n : ℕ) : I n 0 = 1 := by
  rw [I, Polynomial.coeff_zero_eq_eval_zero, mahonian, Polynomial.eval_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [Polynomial.eval_finsetSum, Finset.sum_range_succ']
  simp

lemma A_succ (n : ℕ) : A n (n + 1) = I n (n + 1) - 1 := by
  rw [A_eq_trunc (by omega), Finset.sum_range_succ', Finset.sum_eq_zero fun j _ => ite_eq_right (by omega),
    ite_eq_left (by omega), zero_add, Nat.sub_self, I_zero]

/-- The sum in Lemma 2, for `i ≤ n + 2`: `I_n(n+i) = A(n,n+i) + ∑_{t=0}^{i-1} I_n(t)`. -/
lemma I_split {n i : ℕ} (hi : i ≤ n + 2) :
    I n (n + i) = A n (n + i) + ∑ t ∈ Finset.range i, I n t := by
  rw [A_eq_trunc (by omega), ← Finset.sum_range_add_sum_Ico _ hi,
    Finset.sum_eq_zero (s := Finset.Ico i (n + 2)) fun j hj => ite_eq_right (by simp at hj; omega), add_zero,
    ← Finset.sum_range_reflect (fun t => I n t) i]
  rw [Finset.sum_congr rfl fun j hj => ite_eq_left (by simp at hj; omega)]
  have : ∀ j ∈ Finset.range i, I n (n + i - (n + 1 + j)) = I n (i - 1 - j) := fun j _ => by
    congr 1; omega
  rw [Finset.sum_congr rfl this]; ring

/-- `c_n = ∑_{t<i} (I_n(t) - A(n,t))` when `i ≤ n + 2` (the paper's Remark, in the range of the lemma). -/
lemma c_eq_sum {i n : ℕ} (hi : i ≤ n + 2) : c i n = ∑ t ∈ Finset.range i, (I n t - A n t) := by
  rw [c, I_split hi, Finset.sum_sub_distrib]; ring

/-- **Lemma 2** (definition of `c_n` rearranged): `I_n(n+i) = A(n,n+i) + ∑_{t=0}^{i-1} A(n,t) + c_n`. -/
theorem lemma2 (i n : ℕ) : I n (n + i) = A n (n + i) + ∑ t ∈ Finset.range i, A n t + c i n := by
  rw [c]; ring

/-- **Lemma 2, first part.** `c_n = 0` for `n ≥ i - 1`. -/
theorem c_eq_zero {i n : ℕ} (hn : i - 1 ≤ n) : c i n = 0 := by
  rw [c_eq_sum (by omega)]
  exact Finset.sum_eq_zero fun t ht => by
    rw [A_eq_I_of_le (by simp at ht; omega), sub_self]

/-- **Lemma 2, second part.** `c_{i-2} = 1` for `i ≥ 2`. -/
theorem c_sub_two {i : ℕ} (hi : 2 ≤ i) : c i (i - 2) = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 2 := ⟨i - 2, by omega⟩
  rw [Nat.add_sub_cancel, c_eq_sum le_rfl, Finset.sum_range_succ,
    Finset.sum_eq_zero fun t ht => by rw [A_eq_I_of_le (by simp at ht; omega), sub_self], A_succ]
  ring

end

end Mahonian
