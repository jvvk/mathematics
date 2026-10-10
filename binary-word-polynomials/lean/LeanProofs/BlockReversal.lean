import Mathlib

/-!
# Binary words with the same characteristic polynomial (MO 514920)

For a binary word `w = w₁ … wₙ` let `H_w` be the tridiagonal matrix with `w` on the diagonal and `1` beside it. Its
characteristic polynomial satisfies the continuant recurrence `P(w c d) = (t - d) P(w c) - P(w)` (expanding the
determinant along the last row), so it is the `(0,0)` entry of the transfer matrix
`M_w = T(t - w₁) ⋯ T(t - wₙ)` with `T(z) = !![z, -1; 1, 0]`. Here `P` is *defined* as that entry, and `P_snoc` proves
the recurrence.

* `block_reversal`: if `Gᵀ = G`, every block `N` has `N G = G Nᵀ`, `G x = λ y'` and `G x' = λ' y`, then
  `λ' (x ⬝ V y) = λ (x' ⬝ V_rev y')`. No inverses are needed.
* `word_reversal`: the same for words, `λ' P(A Y₁⋯Yₘ B) = λ P(A' Yₘ⋯Y₁ B')`.
* `theorem_R`: block reversal in the class of `X` (first letter ≠ last letter), context `A`, `B` = `X` with its first,
  last letter flipped.
* `interleaving`: `P(W a₁ W ⋯ aᵣ W) = P(W aᵣ W ⋯ a₁ W)`.
* `complement`: `P_{w̄}(t) = (-1)ⁿ P_w(1 - t)`.
-/

namespace BlockReversal

open Matrix Polynomial

section General

variable {R : Type*} [CommRing R]

/-- The `2 × 2` step matrix. -/
def T (z : R) : Matrix (Fin 2) (Fin 2) R := !![z, -1; 1, 0]

/-- The value of a letter. -/
def bv (c : Bool) : R := if c then 1 else 0

/-- The transfer matrix of a word. -/
def M (t : R) (w : List Bool) : Matrix (Fin 2) (Fin 2) R := (w.map fun c => T (t - bv c)).prod

/-- The characteristic polynomial, as the `(0,0)` entry of the transfer matrix. -/
def P (t : R) (w : List Bool) : R := M t w 0 0

def e0 : Fin 2 → R := ![1, 0]

theorem M_nil (t : R) : M t [] = 1 := rfl

theorem M_cons (t : R) (c : Bool) (w : List Bool) : M t (c :: w) = T (t - bv c) * M t w := by
  simp [M]

theorem M_append (t : R) (u v : List Bool) : M t (u ++ v) = M t u * M t v := by
  simp [M, List.prod_append]

theorem M_flatten (t : R) (L : List (List Bool)) : M t L.flatten = (L.map (M t)).prod := by
  induction L with
  | nil => rfl
  | cons Y L ih => rw [List.flatten_cons, M_append, ih, List.map_cons, List.prod_cons]

theorem P_nil (t : R) : P t [] = 1 := by simp [P, M_nil]

theorem P_single (t : R) (c : Bool) : P t [c] = t - bv c := by
  simp [P, M, T]

/-- The continuant recurrence. -/
theorem P_snoc (t : R) (w : List Bool) (c d : Bool) :
    P t (w ++ [c, d]) = (t - bv d) * P t (w ++ [c]) - P t w := by
  simp only [P, M_append]
  simp [M, T, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem P_eq_dot (t : R) (w : List Bool) : P t w = e0 ⬝ᵥ (M t w *ᵥ e0) := by
  simp [P, e0, dotProduct, Fin.sum_univ_two, mulVec]

theorem det_T (z : R) : (T z).det = 1 := by simp [T, det_fin_two]

theorem det_M (t : R) (w : List Bool) : (M t w).det = 1 := by
  induction w with
  | nil => simp [M_nil]
  | cons c w ih => rw [M_cons, det_mul, det_T, ih, one_mul]

/-! ### The block-reversal lemma -/

theorem transpose_prod (G : Matrix (Fin 2) (Fin 2) R) (Ms : List (Matrix (Fin 2) (Fin 2) R))
    (hM : ∀ N ∈ Ms, N * G = G * Nᵀ) : G * Ms.prodᵀ = Ms.reverse.prod * G := by
  induction Ms with
  | nil => simp
  | cons N Ms ih =>
    rw [List.prod_cons, transpose_mul, List.reverse_cons, List.prod_append, List.prod_singleton, ← mul_assoc,
      ih fun N' h => hM N' (List.mem_cons_of_mem _ h), mul_assoc, ← hM N List.mem_cons_self, mul_assoc]

/-- **Block reversal.** -/
theorem block_reversal (G : Matrix (Fin 2) (Fin 2) R) (hG : Gᵀ = G) (Ms : List (Matrix (Fin 2) (Fin 2) R))
    (hM : ∀ N ∈ Ms, N * G = G * Nᵀ) (x x' y y' : Fin 2 → R) (l l' : R)
    (hx : G *ᵥ x = l • y') (hx' : G *ᵥ x' = l' • y) :
    l' * (x ⬝ᵥ (Ms.prod *ᵥ y)) = l * (x' ⬝ᵥ (Ms.reverse.prod *ᵥ y')) := by
  have key := transpose_prod G Ms hM
  calc l' * (x ⬝ᵥ (Ms.prod *ᵥ y)) = x ⬝ᵥ (Ms.prod *ᵥ (l' • y)) := by
          rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
    _ = x ⬝ᵥ ((Ms.prod * G) *ᵥ x') := by rw [← hx', mulVec_mulVec]
    _ = x' ⬝ᵥ ((Ms.prod * G)ᵀ *ᵥ x) := by
          rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    _ = x' ⬝ᵥ ((Ms.reverse.prod * G) *ᵥ x) := by rw [transpose_mul, hG, key]
    _ = l * (x' ⬝ᵥ (Ms.reverse.prod *ᵥ y')) := by
          rw [← mulVec_mulVec, hx, mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- `P(A V B)` as a bilinear form in the boundary vectors. -/
theorem P_split (t : R) (A B : List Bool) (Ys : List (List Bool)) :
    P t (A ++ Ys.flatten ++ B) = ((M t A)ᵀ *ᵥ e0) ⬝ᵥ ((Ys.map (M t)).prod *ᵥ (M t B *ᵥ e0)) := by
  rw [P_eq_dot, M_append, M_append, M_flatten, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    ← mulVec_transpose]

/-- **Block reversal for words.** -/
theorem word_reversal (t : R) (A A' B B' : List Bool) (Ys : List (List Bool)) (G : Matrix (Fin 2) (Fin 2) R)
    (hG : Gᵀ = G) (hY : ∀ Y ∈ Ys, M t Y * G = G * (M t Y)ᵀ) (l l' : R)
    (hx : G *ᵥ ((M t A)ᵀ *ᵥ e0) = l • (M t B' *ᵥ e0)) (hx' : G *ᵥ ((M t A')ᵀ *ᵥ e0) = l' • (M t B *ᵥ e0)) :
    l' * P t (A ++ Ys.flatten ++ B) = l * P t (A' ++ Ys.reverse.flatten ++ B') := by
  rw [P_split, P_split, List.map_reverse]
  exact block_reversal G hG _ (by simpa using hY) _ _ _ _ l l' hx hx'

/-! ### Theorem R -/

/-- `ε = ±1` according to the letter. -/
def eps (c : Bool) : R := if c then 1 else -1

def u (c : Bool) : Fin 2 → R := ![1, eps c]

/-- The symmetric matrix of `Z = M_X`: `p + s` on the diagonal, `h = q + ρ` off it. -/
def Gm (Z : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![Z 0 0 - Z 1 1, Z 1 0 - Z 0 1; Z 1 0 - Z 0 1, Z 0 0 - Z 1 1]

/-- The ratio class: `κ(Y) = κ(X)`, i.e. `(q' + ρ')(p + s) = (p' + s')(q + ρ)`. -/
def SameClass (N Z : Matrix (Fin 2) (Fin 2) R) : Prop :=
  (N 1 0 - N 0 1) * (Z 0 0 - Z 1 1) = (N 0 0 - N 1 1) * (Z 1 0 - Z 0 1)

theorem Gm_symm (Z : Matrix (Fin 2) (Fin 2) R) : (Gm Z)ᵀ = Gm Z := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gm]

theorem sameClass_comm {N Z : Matrix (Fin 2) (Fin 2) R} (h : SameClass N Z) : N * Gm Z = Gm Z * Nᵀ := by
  unfold SameClass at h
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gm, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination h | linear_combination -h

theorem sameClass_self (Z : Matrix (Fin 2) (Fin 2) R) : SameClass Z Z := by unfold SameClass; ring

theorem eps_sq (c : Bool) : (eps c : R) * eps c = 1 := by cases c <;> simp [eps]

/-- Flipping the first letter: `M_{c̄ w}ᵀ e₀ = M_{c w}ᵀ u_c`. -/
theorem row_flip (t : R) (c : Bool) (w : List Bool) :
    (M t ((!c) :: w))ᵀ *ᵥ e0 = (M t (c :: w))ᵀ *ᵥ u c := by
  rw [M_cons, M_cons, transpose_mul, transpose_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  congr 1
  ext i; fin_cases i <;> cases c <;> simp [T, bv, e0, u, eps, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- Flipping the last letter from `c̄` to `c`: `M_{w c} e₀ = M_{w c̄} u_c`. -/
theorem col_flip (t : R) (c : Bool) (w : List Bool) :
    M t (w ++ [c]) *ᵥ e0 = M t (w ++ [!c]) *ᵥ u c := by
  rw [M_append, M_append, ← mulVec_mulVec, ← mulVec_mulVec]
  congr 1
  ext i; fin_cases i <;> cases c <;> simp [M, T, bv, e0, u, eps, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem Gm_u (Z : Matrix (Fin 2) (Fin 2) R) (c : Bool) :
    Gm Z *ᵥ u c = (Z 0 0 - Z 1 1 + eps c * (Z 1 0 - Z 0 1)) • u c := by
  have := eps_sq (R := R) c
  ext i; fin_cases i <;> simp [Gm, u, mulVec, dotProduct, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (Z 1 0 - Z 0 1) * this | linear_combination -(Z 1 0 - Z 0 1) * this

/-- **Theorem R** (with the factor `λ = p + s + ε h` not yet cancelled). Let `X = c m c̄`, `A = c̄ m c̄` (first letter
flipped) and `B = c m c` (last letter flipped). If every block is in the ratio class of `X`, reversing the blocks
multiplies nothing: `λ P(A Y₁⋯Yₘ B) = λ P(A Yₘ⋯Y₁ B)`. -/
theorem theorem_R_mul (t : R) (c : Bool) (m : List Bool) (Ys : List (List Bool))
    (hY : ∀ Y ∈ Ys, SameClass (M t Y) (M t (c :: (m ++ [!c])))) :
    let Z := M t (c :: (m ++ [!c]))
    let l := Z 0 0 - Z 1 1 + eps c * (Z 1 0 - Z 0 1)
    l * P t ((!c) :: (m ++ [!c]) ++ Ys.flatten ++ (c :: (m ++ [c]))) =
      l * P t ((!c) :: (m ++ [!c]) ++ Ys.reverse.flatten ++ (c :: (m ++ [c]))) := by
  intro Z l
  have hx : Gm Z *ᵥ ((M t ((!c) :: (m ++ [!c])))ᵀ *ᵥ e0) = l • (M t (c :: (m ++ [c])) *ᵥ e0) := by
    rw [row_flip, mulVec_mulVec, ← sameClass_comm (sameClass_self Z), ← mulVec_mulVec, Gm_u, mulVec_smul,
      show c :: (m ++ [c]) = (c :: m) ++ [c] by simp, col_flip]
    simp [Z, l]
  exact word_reversal t _ _ _ _ Ys (Gm Z) (Gm_symm Z) (fun Y h => sameClass_comm (hY Y h)) l l hx hx

/-! ### The interleaving family -/

/-- The symmetric matrix for blocks `a W`: `[[1 - ρ², -ρ p], [-ρ p, -p²]]` with `p = Z₀₀`, `ρ = -Z₀₁`. -/
def Gw (Z : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![1 - Z 0 1 ^ 2, Z 0 1 * Z 0 0; Z 0 1 * Z 0 0, -Z 0 0 ^ 2]

theorem Gw_symm (Z : Matrix (Fin 2) (Fin 2) R) : (Gw Z)ᵀ = Gw Z := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gw]

theorem Gw_comm (z : R) (Z : Matrix (Fin 2) (Fin 2) R) (hd : Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0 = 1) :
    T z * Z * Gw Z = Gw Z * (T z * Z)ᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gw, T, Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct] <;>
    first | ring1 | linear_combination (Z 0 0) * hd | linear_combination -(Z 0 0) * hd

theorem block_aW (t : R) (a : Bool) (W : List Bool) :
    M t (a :: W) * Gw (M t W) = Gw (M t W) * (M t (a :: W))ᵀ := by
  have hd := det_M t W
  rw [det_fin_two] at hd
  rw [M_cons]
  exact Gw_comm _ _ hd

/-- **Interleaving** (with the factor `p = P_W` not yet cancelled). -/
theorem interleaving_mul (t : R) (W : List Bool) (as : List Bool) :
    P t W * P t (W ++ (as.map fun a => a :: W).flatten ++ []) =
      P t W * P t (W ++ (as.map fun a => a :: W).reverse.flatten ++ []) := by
  have hx : Gw (M t W) *ᵥ ((M t W)ᵀ *ᵥ e0) = P t W • (M t [] *ᵥ e0) := by
    ext i; fin_cases i <;> simp [Gw, P, M_nil, e0, mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  exact word_reversal t W W [] [] _ (Gw (M t W)) (Gw_symm _)
    (fun Y h => by obtain ⟨a, -, rfl⟩ := List.mem_map.mp h; exact block_aW t a W) _ _ hx hx

/-! ### Complement -/

def D : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]

theorem T_compl (t : R) (c : Bool) : T (t - bv (!c)) = -(D * T ((1 - t) - bv c) * D) := by
  ext i j; fin_cases i <;> fin_cases j <;> cases c <;> simp [T, D, bv, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem M_compl (t : R) (w : List Bool) : M t (w.map (!·)) = (-1) ^ w.length • (D * M (1 - t) w * D) := by
  induction w with
  | nil => ext i j; fin_cases i <;> fin_cases j <;> simp [M_nil, D]
  | cons c w ih =>
    have hDD : (D : Matrix (Fin 2) (Fin 2) R) * D = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [D, Matrix.mul_apply, Fin.sum_univ_two]
    rw [List.map_cons, M_cons, ih, T_compl, M_cons, List.length_cons, pow_succ, Matrix.mul_smul, neg_mul,
      show D * T (1 - t - bv c) * D * (D * M (1 - t) w * D) = D * T (1 - t - bv c) * (D * D) * M (1 - t) w * D by
        noncomm_ring, hDD, mul_one, mul_neg_one, neg_smul, mul_assoc D, smul_neg]

/-- **Complement**: `P_{w̄}(t) = (-1)ⁿ P_w(1 - t)`. -/
theorem complement (t : R) (w : List Bool) : P t (w.map (!·)) = (-1) ^ w.length * P (1 - t) w := by
  rw [P, M_compl]
  simp [D, Matrix.mul_apply, Fin.sum_univ_two, P, vecMul, dotProduct]

end General

/-! ### Cancelling the factor in `ℤ[X]` -/

section Poly

/-- In `ℤ[X]`, the `(0,0)` entry of `M_w` is monic of degree `|w|` and the other entries have degree `≤ |w| - 1`. -/
theorem M_degrees (w : List Bool) :
    (M (X : ℤ[X]) w 0 0).Monic ∧ (M (X : ℤ[X]) w 0 0).natDegree = w.length ∧
      (M (X : ℤ[X]) w 0 1).natDegree ≤ w.length - 1 ∧ (M (X : ℤ[X]) w 1 0).natDegree ≤ w.length - 1 ∧
      (M (X : ℤ[X]) w 1 1).natDegree ≤ w.length - 1 := by
  induction w using List.reverseRecOn with
  | nil => simp [M_nil]
  | append_singleton w c ih =>
    obtain ⟨h0, h0d, h1, h2, h3⟩ := ih
    have hz : ((X : ℤ[X]) - bv c).Monic := by
      cases c
      · simpa [bv] using monic_X (R := ℤ)
      · simpa [bv] using monic_X_sub_C (1 : ℤ)
    have hzd : ((X : ℤ[X]) - bv c).natDegree = 1 := by
      cases c
      · simp [bv]
      · simpa [bv] using natDegree_X_sub_C (1 : ℤ)
    have e : ∀ i j, M (X : ℤ[X]) (w ++ [c]) i j = ∑ k, M X w i k * T ((X : ℤ[X]) - bv c) k j := by
      intro i j; rw [M_append]; simp [M, Matrix.mul_apply]
    simp only [e, Fin.sum_univ_two, T, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, head_cons, mul_neg, mul_one, mul_zero, add_zero, List.length_append, List.length_singleton,
      Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos w.length with hl | hl
    · obtain rfl := List.length_eq_zero_iff.mp hl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [M_nil, hz, hzd]
    have hm : (M X w 0 0 * ((X : ℤ[X]) - bv c)).Monic := h0.mul hz
    have hmd : (M X w 0 0 * ((X : ℤ[X]) - bv c)).natDegree = w.length + 1 := by
      rw [h0.natDegree_mul hz, h0d, hzd]
    have hlt : (M X w 0 1).degree < (M X w 0 0 * ((X : ℤ[X]) - bv c)).degree :=
      degree_lt_degree (by rw [hmd]; omega)
    refine ⟨hm.add_of_left hlt, ?_, ?_, ?_, ?_⟩
    · rw [natDegree_add_eq_left_of_degree_lt hlt, hmd]
    · simp [natDegree_neg, h0d]
    · refine (natDegree_add_le _ _).trans (max_le ?_ (by omega))
      exact natDegree_mul_le.trans (by rw [hzd]; omega)
    · rw [natDegree_neg]; omega

theorem P_monic (w : List Bool) : (P (X : ℤ[X]) w).Monic := (M_degrees w).1

/-- `p + s + ε h` is monic, hence nonzero, for a nonempty word. -/
theorem lam_ne_zero (w : List Bool) (hw : w ≠ []) (e : ℤ[X]) (he : e.natDegree = 0) :
    M (X : ℤ[X]) w 0 0 - M X w 1 1 + e * (M X w 1 0 - M X w 0 1) ≠ 0 := by
  obtain ⟨h0, h0d, h1, h2, h3⟩ := M_degrees w
  have hn : 0 < w.length := List.length_pos_of_ne_nil hw
  have a1 := natDegree_add_le (-M (X : ℤ[X]) w 1 1) (e * (M X w 1 0 - M X w 0 1))
  have a2 := natDegree_mul_le (p := e) (q := M (X : ℤ[X]) w 1 0 - M X w 0 1)
  have a3 := natDegree_sub_le (M (X : ℤ[X]) w 1 0) (M X w 0 1)
  rw [natDegree_neg] at a1
  have hlt : (-M (X : ℤ[X]) w 1 1 + e * (M X w 1 0 - M X w 0 1)).degree < (M X w 0 0).degree :=
    degree_lt_degree (by rw [h0d]; omega)
  have := (h0.add_of_left hlt).ne_zero
  rwa [← add_assoc, ← sub_eq_add_neg] at this

/-- **Theorem R** in `ℤ[X]`. -/
theorem theorem_R (c : Bool) (m : List Bool) (Ys : List (List Bool))
    (hY : ∀ Y ∈ Ys, SameClass (M (X : ℤ[X]) Y) (M X (c :: (m ++ [!c])))) :
    P (X : ℤ[X]) ((!c) :: (m ++ [!c]) ++ Ys.flatten ++ (c :: (m ++ [c]))) =
      P X ((!c) :: (m ++ [!c]) ++ Ys.reverse.flatten ++ (c :: (m ++ [c]))) := by
  have h := theorem_R_mul (X : ℤ[X]) c m Ys hY
  refine mul_left_cancel₀ (lam_ne_zero (c :: (m ++ [!c])) (by simp) (eps c) ?_) h
  cases c <;> simp [eps]

/-- **Interleaving** in `ℤ[X]`: `P(W a₁ W ⋯ aᵣ W) = P(W aᵣ W ⋯ a₁ W)`. -/
theorem interleaving (W : List Bool) (as : List Bool) :
    P (X : ℤ[X]) (W ++ (as.map fun a => a :: W).flatten) =
      P X (W ++ (as.map fun a => a :: W).reverse.flatten) := by
  have h := interleaving_mul (X : ℤ[X]) W as
  simp only [List.append_nil] at h
  exact mul_left_cancel₀ (P_monic W).ne_zero h

end Poly

end BlockReversal
