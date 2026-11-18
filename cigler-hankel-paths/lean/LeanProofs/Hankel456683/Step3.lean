import LeanProofs.Hankel456683.Step2

/-!
# Step 3: `W = H U` with `U` the unitriangular ballot matrix

From now on `c = 0`: the weights are `s_0 = x` and `s_l = 0` for `l > 0` (`ciglerS x 0`).

* `ciglerH_eq`: Cigler's `H_{k,n}(x)` is the leading `n × n` block of the infinite matrix `hE`
  (the answer's "Unpacking your definition").
* `hE_col_zero` (`H_{l,0} = [l = k]`), `hE_succ_succ` (`H_{l+1,i+1} = H_{l,i} + [l+i+2 = k]`, the
  answer's pairing of entries on the same diagonal) and `hE_row_zero`
  (`H_{0,i+1} = x H_{0,i} + [i+1 = k]`, the answer's four cases at `l = 0`).
* `local_identity`: identity (2),
  `H_{l,i+1} + H_{l,i-1} = H_{l-1,i} + H_{l+1,i} + x [l=0] H_{0,i}` with `H_{l,-1} = H_{-1,i} = 0`.
* `ballot_succ`, `ballot_eq_zero_of_lt`, `ballot_self`: the ballot recursion and unitriangularity.
* `walk_eq_sum_hE_ballot`: identity (1), `W_j(l → k) = ∑_{i ≤ j} H_{l,i} B(j,i)`, by induction on
  `j` from (2), exactly as in the answer.
* `W_eq_H_mul_U`, `det_U`, `det_W_eq_det_ciglerH`.
-/

namespace Hankel456683

open Finset Matrix

variable {R : Type*} [CommRing R]

/-! ### The entries of `H` -/

theorem band_iff (k r s : ℕ) :
    (∃ m l : ℕ, m ≤ k ∧ r = k - m + l ∧ s = m + l) ↔
      (r ≤ s + k ∧ s ≤ r + k ∧ k ≤ r + s ∧ (r + s - k) % 2 = 0) := by
  constructor
  · rintro ⟨m, l, hm, hr, hs⟩; omega
  · intro h
    exact ⟨s - (r + s - k) / 2, (r + s - k) / 2, by omega, by omega, by omega⟩

theorem above_iff (k r s : ℕ) :
    (∃ i l : ℕ, 1 ≤ i ∧ r = l ∧ s = k + i + l) ↔ k + r < s := by
  constructor
  · rintro ⟨i, l, hi, hr, hs⟩; omega
  · intro h
    exact ⟨s - k - r, r, by omega, rfl, by omega⟩

/-- The infinite matrix `H` restricted to `0 ≤ l, i < n`. -/
def Hmat (k : ℕ) (x : R) (n : ℕ) : Matrix (Fin n) (Fin n) R := Matrix.of fun l i => hE k x l i

/-- Cigler's `H_{k,n}(x)` is the leading block of `hE` (the answer's unpacking of the
definition). -/
theorem ciglerH_eq (k n : ℕ) (x : R) : ciglerH k n x = Hmat k x n := by
  ext r s
  simp only [ciglerH, Hmat, hE, Matrix.of_apply, band_iff, above_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem pow_eq_of_eq (x : R) {a b : ℕ} (h : a = b) : x ^ a = x ^ b := by rw [h]

theorem pow_eq_mul_pow (x : R) {a b : ℕ} (h : a = b + 1) : x ^ a = x * x ^ b := by
  rw [h, pow_succ']

theorem pow_eq_mul_one (x : R) {a : ℕ} (h : a = 1) : x ^ a = x * 1 := by rw [h, pow_one, mul_one]

/-- `H_{l,0} = [l = k]`. -/
theorem hE_col_zero (k : ℕ) (x : R) (l : ℕ) : hE k x l 0 = if l = k then 1 else 0 := by
  simp only [hE]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Entries on one diagonal agree, except where the band condition `l + s ≥ k` switches on. -/
theorem hE_succ_succ (k : ℕ) (x : R) (l i : ℕ) :
    hE k x (l + 1) (i + 1) = hE k x l i + if l + i + 2 = k then 1 else 0 := by
  simp only [hE]
  split_ifs <;> first | (simp only [add_zero, zero_add]; done) | (exfalso; omega) |
    (simp only [add_zero]; exact pow_eq_of_eq x (by omega))

/-- Row `0`: `H_{0,i+1} = x H_{0,i} + [i + 1 = k]`. -/
theorem hE_row_zero (k : ℕ) (x : R) (i : ℕ) :
    hE k x 0 (i + 1) = x * hE k x 0 i + if i + 1 = k then 1 else 0 := by
  simp only [hE]
  split_ifs <;> first | (simp only [add_zero, zero_add, mul_zero]; done) | (exfalso; omega) |
    (simp only [add_zero]; exact pow_eq_mul_pow x (by omega)) |
    (simp only [add_zero]; exact pow_eq_mul_one x (by omega))

/-- Identity (2): `H_{l,i+1} + H_{l,i-1} = H_{l-1,i} + H_{l+1,i} + x [l = 0] H_{0,i}`, with
`H_{l,-1} = H_{-1,i} = 0`. -/
theorem local_identity (k : ℕ) (x : R) (l i : ℕ) :
    hE k x l (i + 1) + (if i = 0 then 0 else hE k x l (i - 1)) =
      (if l = 0 then 0 else hE k x (l - 1) i) + hE k x (l + 1) i +
        (if l = 0 then x * hE k x 0 i else 0) := by
  rcases l with _ | l <;> rcases i with _ | i
  · simp only [hE_row_zero, hE_col_zero, ↓reduceIte]
    split_ifs <;> first | (exfalso; omega) | ring
  · simp only [hE_row_zero, hE_succ_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel]
    split_ifs <;> first | (exfalso; omega) | ring
  · simp only [hE_succ_succ, hE_col_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel]
  · simp only [hE_succ_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel]
    split_ifs <;> first | (exfalso; omega) | ring

/-! ### Ballot numbers -/

theorem ballot_zero (i : ℕ) : (ballot 0 i : R) = if i = 0 then 1 else 0 := by
  simp [ballot, eq_comm]

/-- The ballot recursion `B(j+1, i) = B(j, i-1) + B(j, i+1)` (`B(j, -1) = 0`). -/
theorem ballot_succ (j i : ℕ) :
    (ballot (j + 1) i : R) = (if i = 0 then 0 else ballot j (i - 1)) + ballot j (i + 1) := by
  simp only [ballot, walk_succ, zero_mul, add_zero]

theorem ballot_eq_zero_of_lt {j i : ℕ} (h : j < i) : (ballot j i : R) = 0 :=
  walk_eq_zero_of_lt _ j 0 i (by omega)

theorem ballot_self (j : ℕ) : (ballot j j : R) = 1 := by
  simpa [ballot] using walk_top (fun _ => (0 : R)) j 0

/-! ### Identity (1) -/

/-- The weights with `c = 0`: `x` at height `0`, `0` elsewhere. -/
theorem ciglerS_zero (x : R) (l : ℕ) : ciglerS x 0 l = if l = 0 then x else 0 := by
  simp [ciglerS]

/-- Identity (1): `W_j(l → k) = ∑_{i ≤ j} H_{l,i} B(j,i)`. -/
theorem walk_eq_sum_hE_ballot (k : ℕ) (x : R) :
    ∀ j l, walk (ciglerS x 0) j l k = ∑ i ∈ range (j + 1), hE k x l i * ballot j i
  | 0, l => by
    simp [hE_col_zero, ballot_zero, eq_comm]
  | j + 1, l => by
    have ih := walk_eq_sum_hE_ballot k x j
    -- the left side by the first step, then (1) for `j`
    have lhs : walk (ciglerS x 0) (j + 1) l k = ∑ i ∈ range (j + 1), ballot j i *
        ((if l = 0 then 0 else hE k x (l - 1) i) + hE k x (l + 1) i +
          (if l = 0 then x * hE k x 0 i else 0)) := by
      rw [walk_succ_left, ciglerS_zero]
      rcases l with _ | l
      · simp only [↓reduceIte, zero_add, ih, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
          zero_mul, add_zero, ih, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    -- the right side by the ballot recursion, re-indexed
    have rhs : ∑ i ∈ range (j + 1 + 1), hE k x l i * ballot (j + 1) i =
        ∑ i ∈ range (j + 1), ballot j i *
          (hE k x l (i + 1) + (if i = 0 then 0 else hE k x l (i - 1))) := by
      simp only [ballot_succ, mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_range_succ']
        simp only [↓reduceIte, mul_zero, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          Nat.add_sub_cancel]
        exact Finset.sum_congr rfl fun i _ => by ring
      · conv_lhs => rw [Finset.sum_range_succ, Finset.sum_range_succ]
        conv_rhs => rw [Finset.sum_range_succ']
        rw [ballot_eq_zero_of_lt (show j < j + 1 by omega),
          ballot_eq_zero_of_lt (show j < j + 1 + 1 by omega)]
        simp only [↓reduceIte, mul_zero, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          Nat.add_sub_cancel]
        exact Finset.sum_congr rfl fun i _ => by ring
    rw [lhs, rhs]
    exact Finset.sum_congr rfl fun i _ => by rw [local_identity]

/-! ### The matrix form -/

/-- `U = (B(j,i))_{0 ≤ i,j < n}`, upper unitriangular, independent of `k` and `x`. -/
def U (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => ballot j i

theorem det_U (n : ℕ) : (U R n).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · exact Finset.prod_eq_one fun i _ => ballot_self i
  · intro i j h
    exact ballot_eq_zero_of_lt (show (j : ℕ) < i from h)

/-- Step 3, `W = H U`. -/
theorem W_eq_H_mul_U (k : ℕ) (x : R) (n : ℕ) : W (ciglerS x 0) k n = Hmat k x n * U R n := by
  ext l j
  simp only [W, Hmat, U, Matrix.of_apply, Matrix.mul_apply]
  rw [walk_eq_sum_hE_ballot, Fin.sum_univ_eq_sum_range (fun i => hE k x l i * ballot j i)]
  refine Finset.sum_subset (fun m hm => ?_) fun m _ hm => ?_
  · simp only [mem_range] at hm ⊢; omega
  · simp only [mem_range, not_lt] at hm
    rw [ballot_eq_zero_of_lt (by omega), mul_zero]

theorem det_W_eq_det_ciglerH (k n : ℕ) (x : R) :
    (W (ciglerS x 0) k n).det = (ciglerH k n x).det := by
  rw [W_eq_H_mul_U, Matrix.det_mul, det_U, mul_one, ciglerH_eq]

end Hankel456683
