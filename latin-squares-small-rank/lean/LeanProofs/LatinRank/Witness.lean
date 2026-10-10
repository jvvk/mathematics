import LeanProofs.LatinRank.Bound

/-!
# Latin squares of small rank: exact values r(4) = 3, r(6) = 4, r(8) = 4

Each witness is checked to be Latin and factorised over `ℤ` as `V = A B` with `A` having `r` columns,
so `rank V ≤ r`; the lower bounds are `three_le_rank` and `four_le_rank`. The orders 4 and 8 use the
XOR squares of the question, `V i j = 1 + (i XOR j)`, with `A` = (all-ones, bit vectors). The order-6
square is a rank-minimal one found by `../verify/minrank.py`; its factorisation comes from a Hermite
normal form (`lean-aux/factorise.py`). The finite facts are checked by `decide`.
-/

namespace LatinRank

def L4 : Matrix (Fin 4) (Fin 4) (Fin 4) := !![0, 1, 2, 3; 1, 0, 3, 2; 2, 3, 0, 1; 3, 2, 1, 0]
def L6 : Matrix (Fin 6) (Fin 6) (Fin 6) := !![0, 5, 1, 4, 2, 3; 5, 0, 4, 1, 3, 2; 1, 4, 2, 3, 0, 5; 4, 1, 3, 2, 5, 0; 2, 3, 5, 0, 4, 1; 3, 2, 0, 5, 1, 4]
def A6 : Matrix (Fin 6) (Fin 4) ℤ := !![-34, -6, -21, -8; 34, 6, 28, 15; 0, -1, 7, 7; 0, 1, 0, 0; 0, 0, 7, 6; 0, 0, 0, 1]
def B6 : Matrix (Fin 4) (Fin 6) ℤ := !![0, 0, -1, 1, -1, 1; 5, 2, 4, 3, 6, 1; -3, -2, 0, -5, -1, -4; 4, 3, 1, 6, 2, 5]
def L8 : Matrix (Fin 8) (Fin 8) (Fin 8) := !![0, 1, 2, 3, 4, 5, 6, 7; 1, 0, 3, 2, 5, 4, 7, 6; 2, 3, 0, 1, 6, 7, 4, 5; 3, 2, 1, 0, 7, 6, 5, 4; 4, 5, 6, 7, 0, 1, 2, 3; 5, 4, 7, 6, 1, 0, 3, 2; 6, 7, 4, 5, 2, 3, 0, 1; 7, 6, 5, 4, 3, 2, 1, 0]
def X4 : Matrix (Fin 4) (Fin 3) ℤ := !![1, 0, 0; 1, 1, 0; 1, 0, 1; 1, 1, 1]
def Y4 : Matrix (Fin 3) (Fin 4) ℤ := !![1, 2, 3, 4; 1, -1, 1, -1; 2, 2, -2, -2]
def X8 : Matrix (Fin 8) (Fin 4) ℤ := !![1, 0, 0, 0; 1, 1, 0, 0; 1, 0, 1, 0; 1, 1, 1, 0; 1, 0, 0, 1; 1, 1, 0, 1; 1, 0, 1, 1; 1, 1, 1, 1]
def Y8 : Matrix (Fin 4) (Fin 8) ℤ := !![1, 2, 3, 4, 5, 6, 7, 8; 1, -1, 1, -1, 1, -1, 1, -1; 2, 2, -2, -2, 2, 2, -2, -2; 4, 4, 4, 4, -4, -4, -4, -4]

/-- If `V L = A B` over `ℤ` with `A` having `r` columns, then `rank V ≤ r`. -/
lemma rank_le_of_factor {n r : ℕ} (L : Matrix (Fin n) (Fin n) (Fin n)) (A : Matrix (Fin n) (Fin r) ℤ)
    (B : Matrix (Fin r) (Fin n) ℤ) (h : (fun i j => ((L i j : ℕ) : ℤ) + 1) = A * B) :
    (V L).rank ≤ r := by
  have hV : V L = (A.map (Int.castRingHom ℝ)) * (B.map (Int.castRingHom ℝ)) := by
    rw [← Matrix.map_mul]
    ext i j
    have := congrFun (congrFun h i) j
    simp only [V, Matrix.map_apply, ← this, map_add, map_one, map_natCast]
  rw [hV]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _) |>.trans (by simp)

/-- Latin from the two injectivity conditions, each a finite check. -/
lemma latin_of {n : ℕ} (L : Matrix (Fin n) (Fin n) (Fin n)) (h1 : ∀ i a b, L i a = L i b → a = b)
    (h2 : ∀ j a b, L a j = L b j → a = b) : IsLatin L :=
  ⟨fun i => Finite.injective_iff_bijective.1 fun a b => h1 i a b,
    fun j => Finite.injective_iff_bijective.1 fun a b => h2 j a b⟩

lemma latin4 : IsLatin L4 := latin_of L4 (by decide) (by decide)
lemma latin6 : IsLatin L6 := latin_of L6 (by decide) (by decide)
lemma latin8 : IsLatin L8 := latin_of L8 (by decide) (by decide)

lemma factor4 : (fun i j => ((L4 i j : ℕ) : ℤ) + 1) = X4 * Y4 := by decide
lemma factor6 : (fun i j => ((L6 i j : ℕ) : ℤ) + 1) = A6 * B6 := by decide
lemma factor8 : (fun i j => ((L8 i j : ℕ) : ℤ) + 1) = X8 * Y8 := by decide

/-- `r(4) = 3`. -/
theorem r4 : (∃ L : Matrix (Fin 4) (Fin 4) (Fin 4), IsLatin L ∧ (V L).rank = 3) ∧
    ∀ L : Matrix (Fin 4) (Fin 4) (Fin 4), IsLatin L → 3 ≤ (V L).rank :=
  ⟨⟨L4, latin4, le_antisymm (rank_le_of_factor L4 X4 Y4 factor4) (three_le_rank rfl latin4)⟩,
    fun _ hL => three_le_rank rfl hL⟩

/-- `r(6) = 4`. -/
theorem r6 : (∃ L : Matrix (Fin 6) (Fin 6) (Fin 6), IsLatin L ∧ (V L).rank = 4) ∧
    ∀ L : Matrix (Fin 6) (Fin 6) (Fin 6), IsLatin L → 4 ≤ (V L).rank :=
  ⟨⟨L6, latin6, le_antisymm (rank_le_of_factor L6 A6 B6 factor6) (four_le_rank (by norm_num) latin6)⟩,
    fun _ hL => four_le_rank (by norm_num) hL⟩

/-- `r(8) = 4`. -/
theorem r8 : (∃ L : Matrix (Fin 8) (Fin 8) (Fin 8), IsLatin L ∧ (V L).rank = 4) ∧
    ∀ L : Matrix (Fin 8) (Fin 8) (Fin 8), IsLatin L → 4 ≤ (V L).rank :=
  ⟨⟨L8, latin8, le_antisymm (rank_le_of_factor L8 X8 Y8 factor8) (four_le_rank (by norm_num) latin8)⟩,
    fun _ hL => four_le_rank (by norm_num) hL⟩

end LatinRank
