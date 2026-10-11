import Mathlib

/-!
# Cycles of length `2^n - 2` in the binary de Bruijn graph (MO 227666)

A cycle of length `2^n - 2` in `B(n)` is an Eulerian circuit of `B(m)`, `m = n - 1`, with two edges
deleted. The rest stays balanced, so the deleted pair is the two loops (case A) or the 2-cycle on the
alternating vertices (case B) (`balanced_pairs`). By the BEST theorem each case counts spanning
arborescences. Case A leaves the Laplacian unchanged (`caseA`). Case B is the rank-one update
`L - w wᵀ` (`lap_delete_two_cycle`), and exact mixing `P^m = J / 2^m` (`pow_P_self`) turns the
determinant lemma into a finite geometric sum (`caseB`). The closed forms are `caseB_closed` and
`total_closed`.

Vertices are residues mod `2^m`, with edges `u → 2u + b`; the alternating vertices are `-1/3` and
`-2/3`.

**Cited, not formalised here** (standard, and not in Mathlib):
* the line-graph correspondence between cycles of `B(m+1)` and closed trails of `B(m)`;
* the BEST theorem (Eulerian circuits = arborescences × ∏ (outdeg - 1)!);
* Tutte's matrix-tree theorem, in the form: for a matrix `L` with zero row and column sums on `N`
  vertices, every arborescence count equals `det(L + J) / N²`;
* the de Bruijn–van Aardenne-Ehrenfest count `2^(2^m - m - 1)` of arborescences of `B(m)`.
-/

open Matrix Finset

namespace DeBruijnCycles

variable (m : ℕ)

/-- Vertices of the binary de Bruijn graph `B(m)`: residues mod `2^m`; the edges are `u → 2u + b`. -/
abbrev V := ZMod (2 ^ m)

/-- One step of the walk that shifts in a uniformly random bit. -/
def P : Matrix (V m) (V m) ℚ := fun u v =>
  (if v = 2 * u then 1 / 2 else 0) + (if v = 2 * u + 1 then 1 / 2 else 0)

/-- `#{c < 2^k : v = 2^k u + c}`. -/
def cnt (k : ℕ) (u v : V m) : ℚ :=
  ∑ c ∈ range (2 ^ k), if v = 2 ^ k * u + (c : V m) then 1 else 0

lemma sum_range_two_mul (n : ℕ) (g : ℕ → ℚ) :
    ∑ c ∈ range (2 * n), g c = ∑ c ∈ range n, (g (2 * c) + g (2 * c + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

lemma sum_indicator_mul (x : V m) (f : V m → ℚ) :
    ∑ w, (if w = x then (1 : ℚ) else 0) * f w = f x := by
  simp [ite_mul]

/-- `P^k (u, v) = 2^{-k} #{c < 2^k : v = 2^k u + c}`. -/
theorem pow_P (k : ℕ) (u v : V m) : (P m ^ k) u v = (1 / 2) ^ k * cnt m k u v := by
  induction k generalizing v with
  | zero =>
    simp only [pow_zero, cnt, Finset.sum_range_one, Nat.cast_zero, add_zero, one_mul,
      Matrix.one_apply]
    by_cases h : u = v
    · simp [h]
    · simp [h, Ne.symm h]
  | succ k ih =>
    rw [pow_succ, mul_apply]
    have step1 : ∑ w, (P m ^ k) u w * P m w v
        = ∑ c ∈ range (2 ^ k), (1 / 2) ^ k * P m (2 ^ k * u + (c : V m)) v := by
      simp_rw [ih, cnt, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← sum_indicator_mul m (2 ^ k * u + (c : V m)) (fun w => (1 / 2) ^ k * P m w v)]
      refine Finset.sum_congr rfl fun w _ => ?_
      split_ifs <;> ring
    rw [step1, cnt, show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k by ring, sum_range_two_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [P]
    push_cast
    have e : (2 ^ (k + 1) * u + (2 * c + 1) : V m) = 2 ^ (k + 1) * u + 2 * c + 1 := by ring
    have e1 : (2 : V m) * (2 ^ k * u + c) = 2 ^ (k + 1) * u + 2 * c := by ring
    have e2 : (2 : V m) * (2 ^ k * u + c) + 1 = 2 ^ (k + 1) * u + 2 * c + 1 := by ring
    simp only [e, e1, e2]
    split_ifs <;> ring


/-- Exact mixing: after `m` steps every vertex is equally likely, `P^m = J / 2^m`. -/
theorem pow_P_self (u v : V m) : (P m ^ m) u v = (1 / 2) ^ m := by
  rw [pow_P, cnt]
  have h0 : (2 : V m) ^ m * u = 0 := by
    have : ((2 ^ m : ℕ) : V m) = 0 := ZMod.natCast_self _
    push_cast at this
    rw [this, zero_mul]
  simp_rw [h0, zero_add]
  rw [Finset.sum_eq_single v.val]
  · simp
  · intro c hc hne
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    intro h
    apply hne
    rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hc)]
  · intro h
    exact absurd (Finset.mem_range.mpr (ZMod.val_lt v)) h

/-! ### The alternating vertices `p = 0101…`, `q = 1010…`, written as `-1/3` and `-2/3`. -/

lemma three_mul_inv : (3 : V m) * (3 : V m)⁻¹ = 1 := by
  have h := ZMod.coe_mul_inv_eq_one (n := 2 ^ m) 3
    (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2))
  exact_mod_cast h

lemma three_cancel {a b : V m} (h : 3 * a = 3 * b) : a = b := by
  have := congrArg (fun x => (3 : V m)⁻¹ * x) h
  simp only [← mul_assoc, mul_comm (3 : V m)⁻¹ 3, three_mul_inv, one_mul] at this
  exact this

/-- `p = -1/3`: the alternating vertex `…0101`. -/
def pv : V m := -(3 : V m)⁻¹

/-- `q = -2/3 = 2p`: the alternating vertex `…1010`. -/
def qv : V m := 2 * pv m

lemma three_p : 3 * pv m = -1 := by
  rw [pv, mul_neg, three_mul_inv]

lemma three_q : 3 * qv m = -2 := by
  rw [qv, mul_left_comm, three_p]; ring

/-- The 2-cycle: `p → q` shifts in a `0`, `q → p` shifts in a `1`. -/
lemma q_eq : qv m = 2 * pv m := rfl

lemma p_eq : pv m = 2 * qv m + 1 := by
  apply three_cancel
  rw [three_p, mul_add, mul_left_comm, three_q]; ring

/-- Complementing every bit, `σ u = -1 - u`, swaps `p` and `q`. -/
lemma compl_p : -1 - pv m = qv m := by
  apply three_cancel
  rw [three_q, mul_sub, three_p]; ring

/-- The walk commutes with complementing every bit. -/
lemma P_compl (u v : V m) : P m (-1 - u) (-1 - v) = P m u v := by
  simp only [P]
  have e1 : (-1 - v = 2 * (-1 - u)) ↔ (v = 2 * u + 1) := by
    constructor <;> intro h <;> linear_combination -h
  have e2 : (-1 - v = 2 * (-1 - u) + 1) ↔ (v = 2 * u) := by
    constructor <;> intro h <;> linear_combination -h
  simp only [e1, e2]
  ring

lemma powP_compl (k : ℕ) (u v : V m) : (P m ^ k) (-1 - u) (-1 - v) = (P m ^ k) u v := by
  induction k generalizing v with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, mul_apply, mul_apply]
    have hbij : Function.Bijective (fun x : V m => -1 - x) :=
      Function.Involutive.bijective (by intro x; ring)
    symm
    refine Fintype.sum_bijective (fun x : V m => -1 - x) hbij _ _ fun w => ?_
    rw [ih, P_compl]

/-! ### Return probabilities between `p` and `q` before mixing (`k < m`) -/

lemma two_pow_mod_three (k : ℕ) : 2 ^ k % 3 = if k % 2 = 0 then 1 else 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    split_ifs at ih with h <;> split_ifs with h' <;> omega

/-- For `c < 2^k`, `k < m` and `r ∈ {2^k - 1, 2^k - 2}`, the congruence `3c ≡ r (mod 2^m)` is the
equation `3c = r`: the only other candidate `3c = r + 2^m` is too big or not divisible by three. -/
lemma mod_eq_iff {k c r : ℕ} (hk : k < m) (hc : c < 2 ^ k) (hr1 : r + 2 ≥ 2 ^ k) (hr2 : r < 2 ^ k) :
    3 * c % 2 ^ m = r % 2 ^ m ↔ 3 * c = r := by
  set X := 2 ^ k with hX
  set Y := 2 ^ m with hY
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have hYX : Y = 2 * X ∨ Y ≥ 4 * X := by
    rcases Nat.lt_or_ge (k + 1) m with h | h
    · right
      have : 2 ^ (k + 2) ∣ 2 ^ m := pow_dvd_pow 2 (by omega)
      have := Nat.le_of_dvd (by positivity) this
      rw [hY]; calc 4 * X = 2 ^ (k + 2) := by rw [hX]; ring
        _ ≤ _ := this
    · left
      rw [hY, hX, show m = k + 1 by omega]; ring
  have hrY : r % Y = r := Nat.mod_eq_of_lt (by omega)
  rw [hrY]
  by_cases h3 : 3 * c < Y
  · rw [Nat.mod_eq_of_lt h3]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

lemma sum_three (X r : ℕ) (hr : r < X) :
    ∑ c ∈ range X, (if 3 * c = r then (1 : ℚ) else 0) = if r % 3 = 0 then 1 else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (r / 3)]
    · rw [if_pos (by omega)]
    · intro c _ hc; rw [if_neg (by omega)]
    · intro hn; exact absurd (Finset.mem_range.mpr (by omega)) hn
  · exact Finset.sum_eq_zero fun c _ => by rw [if_neg (by omega)]

theorem cnt_pp {k : ℕ} (hk : k < m) : cnt m k (pv m) (pv m) = if k % 2 = 0 then 1 else 0 := by
  have hX : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [cnt]
  have key : ∀ c ∈ range (2 ^ k), (if pv m = 2 ^ k * pv m + (c : V m) then (1 : ℚ) else 0)
      = if 3 * c = 2 ^ k - 1 then 1 else 0 := by
    intro c hc
    have hc' := Finset.mem_range.mp hc
    refine if_congr ?_ rfl rfl
    rw [← mod_eq_iff m hk hc' (by omega) (by omega), ← ZMod.natCast_eq_natCast_iff']
    push_cast [Nat.cast_sub hX]
    constructor
    · intro h; linear_combination (-3) * h + (1 - 2 ^ k) * three_p m
    · intro h; apply three_cancel
      linear_combination (-1) * h + (1 - 2 ^ k) * three_p m
  rw [Finset.sum_congr rfl key, sum_three _ _ (by omega)]
  have h3 := two_pow_mod_three k
  generalize 2 ^ k = X at *
  split_ifs at h3 ⊢ <;> first | rfl | omega

theorem cnt_pq {k : ℕ} (hk : k < m) : cnt m k (pv m) (qv m) = if k % 2 = 0 then 0 else 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hm : 1 ≤ m := by omega
    have hne : qv m ≠ pv m := by
      intro h
      have h3 := three_q m
      rw [h, three_p] at h3
      have : ((1 : ℕ) : V m) = ((0 : ℕ) : V m) := by push_cast; linear_combination h3
      rw [ZMod.natCast_eq_natCast_iff'] at this
      have : 2 ≤ 2 ^ m := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at *
      omega
    simp [cnt, hne]
  have hX : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk0
  rw [cnt]
  have key : ∀ c ∈ range (2 ^ k), (if qv m = 2 ^ k * pv m + (c : V m) then (1 : ℚ) else 0)
      = if 3 * c = 2 ^ k - 2 then 1 else 0 := by
    intro c hc
    have hc' := Finset.mem_range.mp hc
    refine if_congr ?_ rfl rfl
    rw [← mod_eq_iff m hk hc' (by omega) (by omega), ← ZMod.natCast_eq_natCast_iff']
    push_cast [Nat.cast_sub hX]
    constructor
    · intro h; linear_combination (-3) * h + three_q m - 2 ^ k * three_p m
    · intro h; apply three_cancel
      linear_combination (-1) * h + three_q m - 2 ^ k * three_p m
  rw [Finset.sum_congr rfl key, sum_three _ _ (by omega)]
  have h3 := two_pow_mod_three k
  generalize 2 ^ k = X at *
  split_ifs at h3 ⊢ <;> first | rfl | omega

/-! ### The rank-one update and its determinant -/

lemma one_ne_zero_V (hm : 1 ≤ m) : (1 : V m) ≠ 0 := by
  intro h
  have : ((1 : ℕ) : V m) = ((0 : ℕ) : V m) := by exact_mod_cast h
  rw [ZMod.natCast_eq_natCast_iff'] at this
  have : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at *
  omega

lemma p_ne_q (hm : 1 ≤ m) : pv m ≠ qv m := by
  intro h
  have h3 := three_q m
  rw [← h, three_p] at h3
  exact one_ne_zero_V m hm (by linear_combination h3)

/-- `w = e_p - e_q`. -/
def w : V m → ℚ := Pi.single (pv m) 1 - Pi.single (qv m) 1

/-- The all-ones matrix. -/
def J : Matrix (V m) (V m) ℚ := Matrix.of fun _ _ => 1

lemma quad_form (M : Matrix (V m) (V m) ℚ) :
    w m ⬝ᵥ (M *ᵥ w m) = M (pv m) (pv m) - M (pv m) (qv m) - M (qv m) (pv m) + M (qv m) (qv m) := by
  simp only [w, Matrix.mulVec_sub, Matrix.mulVec_single_one, sub_dotProduct, single_dotProduct,
    Matrix.col_apply, one_mul, Pi.sub_apply]
  ring

/-- `wᵀ P^k w = 2 (-1/2)^k` before mixing. -/
theorem quad_powP (hm : 1 ≤ m) {k : ℕ} (hk : k < m) :
    w m ⬝ᵥ ((P m ^ k) *ᵥ w m) = 2 * (-1 / 2) ^ k := by
  rw [quad_form m]
  have hqq : (P m ^ k) (qv m) (qv m) = (P m ^ k) (pv m) (pv m) := by
    rw [← compl_p, powP_compl]
  have hqp : (P m ^ k) (qv m) (pv m) = (P m ^ k) (pv m) (qv m) := by
    have e' : -1 - qv m = pv m := by rw [← compl_p]; ring
    calc (P m ^ k) (qv m) (pv m) = (P m ^ k) (-1 - pv m) (-1 - qv m) := by rw [compl_p, e']
      _ = _ := powP_compl m k _ _
  rw [hqq, hqp, pow_P, pow_P, cnt_pp m hk, cnt_pq m hk]
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have : (j + j) % 2 = 0 := by omega
    simp only [this, if_true]
    rw [show j + j = 2 * j by ring, pow_mul, pow_mul]; norm_num; ring
  · have : (2 * j + 1) % 2 ≠ 0 := by omega
    simp only [this, if_false]
    rw [pow_succ, pow_succ, pow_mul, pow_mul]; norm_num; ring

lemma P_rowsum (hm : 1 ≤ m) (u : V m) : ∑ v, P m u v = 1 := by
  have hne : (2 * u + 1 : V m) ≠ 2 * u := by
    intro h; exact one_ne_zero_V m hm (by linear_combination h)
  simp only [P, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

lemma P_mul_J (hm : 1 ≤ m) : P m * J m = J m := by
  ext u v
  simp [J, Matrix.mul_apply, P_rowsum m hm]

lemma powP_self_eq : P m ^ m = (1 / 2 : ℚ) ^ m • J m := by
  ext u v
  simp [pow_P_self, J]

/-- `Z = Σ_{k<m} (P^k - J/2^m)`, so that `(1 - P) Z = 1 - J/2^m` (exact mixing). -/
def Z : Matrix (V m) (V m) ℚ := ∑ k ∈ range m, (P m ^ k - (1 / 2 : ℚ) ^ m • J m)

theorem one_sub_P_mul_Z (hm : 1 ≤ m) : (1 - P m) * Z m = 1 - (1 / 2 : ℚ) ^ m • J m := by
  have hJ : (1 - P m) * J m = 0 := by rw [sub_mul, P_mul_J m hm, one_mul, sub_self]
  rw [Z, Finset.sum_sub_distrib, mul_sub, mul_neg_geom_sum, powP_self_eq, Finset.mul_sum]
  simp [Matrix.mul_smul, hJ]

lemma J_mulVec_w : J m *ᵥ w m = 0 := by
  ext u
  simp [J, w, Matrix.mulVec, dotProduct, Finset.sum_sub_distrib]

/-- Column sums of `P^k` agree at `p` and `q` (complement symmetry). -/
lemma colsum_p_q (k : ℕ) : ∑ u, (P m ^ k) u (pv m) = ∑ u, (P m ^ k) u (qv m) := by
  have hbij : Function.Bijective (fun x : V m => -1 - x) :=
    Function.Involutive.bijective (by intro x; ring)
  refine Fintype.sum_bijective (fun x : V m => -1 - x) hbij _ _ fun u => ?_
  rw [← compl_p, powP_compl]

/-- `y = Z w / 2` solves `(L + J) y = w`, with `L = 2(1 - P)`. -/
def y : V m → ℚ := (1 / 2 : ℚ) • (Z m *ᵥ w m)

theorem LJ_mulVec_y (hm : 1 ≤ m) : (2 • (1 - P m) + J m) *ᵥ y m = w m := by
  have hL : (2 • (1 - P m)) *ᵥ y m = w m := by
    rw [y, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_mulVec,
      one_sub_P_mul_Z m hm, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      J_mulVec_w]
    ext u; simp
  have hsum : ∑ u, (Z m *ᵥ w m) u = 0 := by
    simp only [Z, Matrix.sum_mulVec, Finset.sum_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      J_mulVec_w, smul_zero, sub_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [w, Matrix.mulVec_sub, Matrix.mulVec_single_one, Pi.sub_apply, Matrix.col_apply,
      Finset.sum_sub_distrib, colsum_p_q, sub_self]
  have hJ : J m *ᵥ y m = 0 := by
    ext u
    simp only [J, y, Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul, Pi.smul_apply,
      smul_eq_mul, ← Finset.mul_sum, Pi.zero_apply]
    have : ∑ x, (Z m *ᵥ w m) x = 0 := hsum
    simp only [Matrix.mulVec, dotProduct] at this
    rw [this, mul_zero]
  rw [Matrix.add_mulVec, hL, hJ, add_zero]

/-- The determinant identity behind the count: deleting the 2-cycle multiplies `det(L + J)` by
`1 - w ⬝ y`. -/
theorem det_rank_one (hm : 1 ≤ m) :
    (2 • (1 - P m) + J m - vecMulVec (w m) (w m)).det
      = (2 • (1 - P m) + J m).det * (1 - w m ⬝ᵥ y m) := by
  set M := 2 • (1 - P m) + J m
  have hfac : M - vecMulVec (w m) (w m)
      = M * (1 + replicateCol Unit (-y m) * replicateRow Unit (w m)) := by
    rw [mul_add, mul_one, ← Matrix.mul_assoc, ← replicateCol_mulVec, Matrix.mulVec_neg,
      LJ_mulVec_y m hm, vecMulVec_eq Unit]
    ext i j
    simp [replicateCol, replicateRow, Matrix.mul_apply, sub_eq_add_neg]
  rw [hfac, Matrix.det_mul, det_one_add_replicateCol_mul_replicateRow, dotProduct_neg]
  ring

theorem w_dot_y (hm : 1 ≤ m) : w m ⬝ᵥ y m = ∑ k ∈ range m, (-1 / 2 : ℚ) ^ k := by
  rw [y, dotProduct_smul, Z, Matrix.sum_mulVec, dotProduct_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, J_mulVec_w, smul_zero, sub_zero,
    quad_powP m hm (Finset.mem_range.mp hk)]
  ring

/-- **The ratio.** `1 - Σ_{k<m} (-1/2)^k = (2^{m-1} + (-1)^m) / (3·2^{m-1})`, written with `m = n+1`. -/
theorem ratio (n : ℕ) :
    1 - ∑ k ∈ range (n + 1), (-1 / 2 : ℚ) ^ k = (2 ^ n + (-1) ^ (n + 1)) / (3 * 2 ^ n) := by
  rw [geom_sum_eq (by norm_num), div_pow]
  field_simp
  ring

/-! ### Laplacians: the de Bruijn graph, and the two balanced deletions -/

/-- Out-degree Laplacian of a weighted digraph with adjacency matrix `A`. -/
def lap (A : Matrix (V m) (V m) ℚ) : Matrix (V m) (V m) ℚ :=
  Matrix.diagonal (fun u => ∑ v, A u v) - A

/-- The adjacency matrix of `B(m)` is `2P` (entries `0/1` since `2u ≠ 2u + 1`). -/
theorem lap_debruijn (hm : 1 ≤ m) : lap m (2 • P m) = 2 • (1 - P m) := by
  have hrow : ∀ u, ∑ x, (2 • P m) u x = 2 := by
    intro u; simp only [Matrix.smul_apply, ← Finset.smul_sum, P_rowsum m hm]; norm_num
  have hd : Matrix.diagonal (fun u => ∑ v, (2 • P m) u v) = 2 • (1 : Matrix (V m) (V m) ℚ) := by
    ext u v
    rw [Matrix.diagonal_apply, hrow u]
    by_cases h : u = v <;> simp [h, Matrix.one_apply]
  rw [lap, hd, smul_sub]

lemma adj_pq (hm : 1 ≤ m) : (2 • P m) (pv m) (qv m) = 1 := by
  have hne : qv m ≠ 2 * pv m + 1 := by
    intro h; apply one_ne_zero_V m hm; rw [q_eq] at h; linear_combination -h
  simp [P, ← q_eq, hne, one_ne_zero_V m hm]

lemma adj_qp (hm : 1 ≤ m) : (2 • P m) (qv m) (pv m) = 1 := by
  have hne : pv m ≠ 2 * qv m := by
    intro h; apply one_ne_zero_V m hm; rw [p_eq] at h; linear_combination h
  simp [P, ← p_eq, hne]

lemma rowsum_single (a b i : V m) :
    ∑ v, Matrix.single a b (1 : ℚ) i v = if a = i then 1 else 0 := by
  by_cases h : a = i <;> simp [Matrix.single_apply, h]

/-- Case (A): deleting a loop does not change the Laplacian. -/
theorem lap_delete_loop (A : Matrix (V m) (V m) ℚ) (x : V m) :
    lap m (A - Matrix.single x x 1) = lap m A := by
  ext i j
  simp only [lap, Matrix.sub_apply, Matrix.diagonal_apply, Finset.sum_sub_distrib, rowsum_single]
  simp only [Matrix.single_apply]
  by_cases hij : i = j <;> by_cases hi : x = i
  · subst hij; subst hi; simp
  · subst hij; simp [hi]
  · subst hi; simp [hij]
  · simp [hij, hi]

/-- Case (B): deleting the 2-cycle `p ⇄ q` subtracts the rank-one matrix `w wᵀ`. -/
theorem lap_delete_two_cycle (hm : 1 ≤ m) (A : Matrix (V m) (V m) ℚ) :
    lap m (A - Matrix.single (pv m) (qv m) 1 - Matrix.single (qv m) (pv m) 1)
      = lap m A - vecMulVec (w m) (w m) := by
  have hpq := p_ne_q m hm
  ext i j
  simp only [lap, Matrix.sub_apply, Matrix.diagonal_apply, Finset.sum_sub_distrib,
    Matrix.single_apply, vecMulVec, Matrix.of_apply, w, Pi.sub_apply, Pi.single_apply]
  by_cases hij : i = j <;> by_cases hip : i = pv m <;> by_cases hiq : i = qv m <;>
    by_cases hjp : j = pv m <;> by_cases hjq : j = qv m <;>
    simp_all [Finset.sum_ite_eq, eq_comm] <;> ring

/-! ### Which two-edge deletions stay balanced -/

/-- The head of the edge `(u, b)`, i.e. the edge `u → 2u + b`. -/
def head (u : V m) (b : Bool) : V m := 2 * u + if b then 1 else 0

/-- Deleting the edges `(u₁,b₁)` and `(u₂,b₂)` keeps in-degree = out-degree everywhere. -/
def Balanced (u₁ : V m) (b₁ : Bool) (u₂ : V m) (b₂ : Bool) : Prop :=
  ∀ x : V m, (if u₁ = x then 1 else 0) + (if u₂ = x then 1 else 0)
    = (if head m u₁ b₁ = x then 1 else 0) + (if head m u₂ b₂ = x then (1 : ℕ) else 0)

lemma loop_iff (u : V m) (b : Bool) (h : head m u b = u) :
    (u, b) = (0, false) ∨ (u, b) = (-1, true) := by
  cases b
  · left; simp only [head, Bool.false_eq_true, if_false, add_zero] at h
    simp only [Prod.mk.injEq, and_true]; linear_combination h
  · right; simp only [head, if_true] at h
    simp only [Prod.mk.injEq, and_true]; linear_combination h

/-- **Only two balanced deletions.** Two distinct edges whose deletion keeps `B(m)` balanced are
the two loops, or the 2-cycle between the alternating vertices. -/
theorem balanced_pairs (u₁ u₂ : V m) (b₁ b₂ : Bool) (hne : (u₁, b₁) ≠ (u₂, b₂))
    (hb : Balanced m u₁ b₁ u₂ b₂) :
    ((u₁, b₁) = (0, false) ∧ (u₂, b₂) = (-1, true)) ∨ ((u₁, b₁) = (-1, true) ∧ (u₂, b₂) = (0, false))
    ∨ ((u₁, b₁) = (pv m, false) ∧ (u₂, b₂) = (qv m, true))
    ∨ ((u₁, b₁) = (qv m, true) ∧ (u₂, b₂) = (pv m, false)) := by
  set h₁ := head m u₁ b₁ with hh₁
  set h₂ := head m u₂ b₂ with hh₂
  -- the three instances of balance that we use
  have F1 : u₁ = h₁ ∨ u₂ = h₁ := by
    have := hb h₁
    by_contra hc; simp only [not_or] at hc
    rw [if_neg hc.1, if_neg hc.2, if_pos rfl] at this
    split_ifs at this <;> omega
  have F2 : u₁ = h₂ ∨ u₂ = h₂ := by
    have := hb h₂
    by_contra hc; simp only [not_or] at hc
    rw [if_neg hc.1, if_neg hc.2, if_pos rfl] at this
    split_ifs at this <;> omega
  have F3 := hb u₁
  rw [if_pos rfl] at F3
  by_cases L1 : h₁ = u₁
  · -- e₁ is a loop, so e₂ is a loop too
    have L2 : h₂ = u₂ := by
      rcases F2 with e | e
      · by_contra hc
        have hu : u₂ = u₁ := by
          rw [if_pos L1, if_pos e.symm] at F3
          split_ifs at F3 with h' <;> [exact h'; omega]
        exact hc (by rw [hu]; exact e.symm)
      · exact e.symm
    rcases loop_iff m u₁ b₁ L1 with e1 | e1 <;> rcases loop_iff m u₂ b₂ L2 with e2 | e2
    · exact absurd (e1.trans e2.symm) hne
    · exact Or.inl ⟨e1, e2⟩
    · exact Or.inr (Or.inl ⟨e1, e2⟩)
    · exact absurd (e1.trans e2.symm) hne
  · -- e₁ is not a loop: it ends at u₂ and e₂ ends at u₁
    have ha : h₁ = u₂ := by
      rcases F1 with e | e
      · exact absurd e.symm L1
      · exact e.symm
    have hu : u₂ ≠ u₁ := fun h => L1 (ha.trans h)
    have hb2 : h₂ = u₁ := by
      rw [if_neg hu, if_neg L1] at F3
      split_ifs at F3 with h' <;> [exact h'; omega]
    rw [hh₁, head] at ha
    rw [hh₂, head] at hb2
    right; right
    cases b₁ <;> cases b₂ <;>
      simp only [Bool.false_eq_true, if_false, if_true, add_zero] at ha hb2
    · exact absurd (by
        have h0 : u₁ = 0 := three_cancel m (by linear_combination 2 * ha + hb2)
        rw [← ha, h0]; ring) hu
    · left
      have hp : u₁ = pv m := three_cancel m (by linear_combination 2 * ha + hb2 - three_p m)
      refine ⟨by rw [hp], ?_⟩
      rw [← ha, hp, q_eq]
    · right
      have hq : u₁ = qv m := three_cancel m (by linear_combination 2 * ha + hb2 - three_q m)
      refine ⟨by rw [hq], ?_⟩
      rw [← ha, hq, ← p_eq]
    · exact absurd (by
        have h0 : u₁ = -1 := three_cancel m (by linear_combination 2 * ha + hb2)
        rw [← ha, h0]; ring) hu

/-! ### Assembly -/

/-- **Case (A).** The loops `0 → 0` and `-1 → -1` are edges, and deleting them leaves the
Laplacian (hence the arborescence count) unchanged. -/
theorem caseA (hm : 1 ≤ m) :
    (2 • P m) 0 0 = 1 ∧ (2 • P m) (-1) (-1) = 1 ∧
    lap m (2 • P m - Matrix.single 0 0 1 - Matrix.single (-1) (-1) 1) = lap m (2 • P m) := by
  have h1 := one_ne_zero_V m hm
  refine ⟨?_, ?_, by rw [lap_delete_loop, lap_delete_loop]⟩
  · have : (0 : V m) ≠ 2 * 0 + 1 := by intro h; exact h1 (by linear_combination -h)
    simp [P, this, Ne.symm h1]
  · have e : (-1 : V m) = 2 * -1 + 1 := by ring
    have : (-1 : V m) ≠ 2 * -1 := by intro h; exact h1 (by linear_combination h)
    simp only [Matrix.smul_apply, P, this, if_false, zero_add, ← e, if_true]
    norm_num

/-- **Case (B).** Deleting the 2-cycle `p ⇄ q` from `B(n+1)` multiplies `det(L + J)` by
`(2^n + (-1)^(n+1)) / (3·2^n)`. -/
theorem caseB (n : ℕ) :
    (lap (n + 1) (2 • P (n + 1) - Matrix.single (pv (n + 1)) (qv (n + 1)) 1
        - Matrix.single (qv (n + 1)) (pv (n + 1)) 1) + J (n + 1)).det
      = (lap (n + 1) (2 • P (n + 1)) + J (n + 1)).det * ((2 ^ n + (-1) ^ (n + 1)) / (3 * 2 ^ n)) := by
  have hm : 1 ≤ n + 1 := by omega
  rw [lap_delete_two_cycle _ hm, lap_debruijn _ hm,
    show 2 • (1 - P (n + 1)) - vecMulVec (w (n + 1)) (w (n + 1)) + J (n + 1)
      = 2 • (1 - P (n + 1)) + J (n + 1) - vecMulVec (w (n + 1)) (w (n + 1)) by abel,
    det_rank_one _ hm, w_dot_y _ hm, ratio]

/-! ### Closed forms (`m = n + 1` is the order of `B(m)`; the cycles live in `B(m + 1)`) -/

lemma exp_split (n : ℕ) : 2 ^ (n + 1) - (n + 1) - 1 = (2 ^ (n + 1) - 2 * (n + 1)) + n := by
  have := Nat.lt_two_pow_self (n := n + 1)
  have h2 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  omega

/-- de Bruijn number times the case-(B) ratio. -/
theorem caseB_closed (n : ℕ) :
    (2 : ℚ) ^ (2 ^ (n + 1) - (n + 1) - 1) * ((2 ^ n + (-1) ^ (n + 1)) / (3 * 2 ^ n))
      = 1 / 3 * 2 ^ (2 ^ (n + 1) - 2 * (n + 1)) * (2 ^ n + (-1) ^ (n + 1)) := by
  rw [exp_split, pow_add]
  field_simp

/-- **The total.** With `N = n + 2` (cycles of length `2^N - 2` in `B(N)`):
`2^(2^(N-1) - N) + case (B) = 2^(2^(N-1) - 2N + 2) (2^N - (-1)^N) / 3`. -/
theorem total_closed (n : ℕ) :
    (2 : ℚ) ^ (2 ^ (n + 1) - (n + 1) - 1)
        + 1 / 3 * 2 ^ (2 ^ (n + 1) - 2 * (n + 1)) * (2 ^ n + (-1) ^ (n + 1))
      = 2 ^ (2 ^ (n + 1) - 2 * (n + 1)) * (2 ^ (n + 2) - (-1) ^ (n + 2)) / 3 := by
  rw [exp_split, pow_add]
  ring

end DeBruijnCycles
