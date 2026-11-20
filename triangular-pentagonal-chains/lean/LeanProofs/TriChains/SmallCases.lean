import LeanProofs.TriChains.Basic

/-!
# Small cases: explicit chains (`n = 2`, `9 ≤ n ≤ 53`) and necklaces (`12 ≤ n ≤ 53`, `n ≠ 14`)

Certificates from verify/small_certificates.json, each checked by `decide` through `chainB'`/`neckB`.
-/

namespace TriChains

/-- A list of `1..N` without repetition, adjacent sums triangular. -/
def TriChain (N : ℕ) (l : List ℤ) : Prop := l.Nodup ∧ (∀ x, x ∈ l ↔ 1 ≤ x ∧ x ≤ N) ∧ l.IsChain (fun a b => IsTri (a + b))

/-- A triangular chain whose last and first entries also sum to a triangular number. -/
def TriNecklace (N : ℕ) (l : List ℤ) : Prop :=
  TriChain N l ∧ ∃ a b, l.head? = some a ∧ l.getLast? = some b ∧ IsTri (b + a)

def triChainB : List ℤ → Bool
  | a :: b :: rest => triB (a + b) && triChainB (b :: rest)
  | _ => true

theorem triChainB_sound : ∀ l : List ℤ, triChainB l = true → l.IsChain (fun a b => IsTri (a + b))
  | [], _ => List.IsChain.nil
  | [_], _ => List.isChain_singleton _
  | a :: b :: rest, h => by
      simp only [triChainB, Bool.and_eq_true] at h
      exact List.IsChain.cons_cons (isTri_of_triB h.1) (triChainB_sound (b :: rest) h.2)

/-- Boolean check: `l` is `1..N` in some order (as a sorted comparison) with triangular adjacent sums. -/
def chainOK (N : ℕ) (l : List ℤ) : Bool :=
  decide (l.Nodup) && l.length == N && l.all (fun x => decide (1 ≤ x) && decide (x ≤ N)) && triChainB l

def neckOK (N : ℕ) (l : List ℤ) : Bool :=
  chainOK N l && (match l.head?, l.getLast? with | some a, some b => triB (b + a) | _, _ => false)

theorem mem_iff_of_nodup {N : ℕ} {l : List ℤ} (hd : l.Nodup) (hl : l.length = N) (hr : ∀ x ∈ l, 1 ≤ x ∧ x ≤ N) :
    ∀ x, x ∈ l ↔ 1 ≤ x ∧ x ≤ N := by
  have hsub : l.toFinset ⊆ Finset.Icc (1 : ℤ) N := fun x hx => by
    rw [List.mem_toFinset] at hx; exact Finset.mem_Icc.2 (hr x hx)
  have hcard : (Finset.Icc (1 : ℤ) N).card ≤ l.toFinset.card := by
    rw [List.toFinset_card_of_nodup hd, hl, Int.card_Icc]; omega
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  intro x; rw [← Finset.mem_Icc, ← heq, List.mem_toFinset]

theorem triChain_of_chainOK {N : ℕ} {l : List ℤ} (h : chainOK N l = true) : TriChain N l := by
  simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hd, hl⟩, hr⟩, hc⟩ := h
  exact ⟨hd, mem_iff_of_nodup hd hl (fun x hx => by simpa using hr x hx), triChainB_sound l hc⟩

theorem triNecklace_of_neckOK {N : ℕ} {l : List ℤ} (h : neckOK N l = true) : TriNecklace N l := by
  simp only [neckOK, Bool.and_eq_true] at h
  refine ⟨triChain_of_chainOK h.1, ?_⟩
  rcases ha : l.head? with _ | a <;> rcases hb : l.getLast? with _ | b <;> rw [ha, hb] at h <;> simp at h
  exact ⟨a, b, rfl, rfl, isTri_of_triB h.2⟩

theorem chain_2 : chainOK 2 [1, 2] = true := by decide
theorem chain_9 : chainOK 9 [3, 7, 8, 2, 4, 6, 9, 1, 5] = true := by decide
theorem chain_10 : chainOK 10 [3, 7, 8, 2, 4, 6, 9, 1, 5, 10] = true := by decide
theorem chain_11 : chainOK 11 [3, 7, 8, 2, 1, 5, 10, 11, 4, 6, 9] = true := by decide
theorem chain_12 : chainOK 12 [1, 5, 10, 11, 4, 2, 8, 7, 3, 12, 9, 6] = true := by decide
theorem chain_13 : chainOK 13 [1, 5, 10, 11, 4, 6, 9, 12, 3, 7, 8, 2, 13] = true := by decide
theorem chain_14 : chainOK 14 [2, 13, 8, 7, 3, 12, 9, 6, 4, 11, 10, 5, 1, 14] = true := by decide
theorem chain_15 : chainOK 15 [1, 5, 10, 11, 4, 2, 8, 13, 15, 6, 9, 12, 3, 7, 14] = true := by decide
theorem chain_16 : chainOK 16 [1, 14, 7, 3, 12, 9, 6, 15, 13, 8, 2, 4, 11, 10, 5, 16] = true := by decide
theorem chain_17 : chainOK 17 [1, 14, 7, 3, 12, 9, 6, 15, 13, 8, 2, 4, 17, 11, 10, 5, 16] = true := by decide
theorem chain_18 : chainOK 18 [1, 14, 7, 3, 18, 10, 5, 16, 12, 9, 6, 15, 13, 8, 2, 4, 11, 17] = true := by decide
theorem chain_19 : chainOK 19 [1, 14, 7, 3, 18, 10, 5, 16, 12, 9, 6, 15, 13, 8, 2, 19, 17, 4, 11] = true := by decide
theorem chain_20 : chainOK 20 [1, 14, 7, 3, 18, 10, 5, 16, 12, 9, 19, 17, 11, 4, 6, 15, 13, 2, 8, 20] = true := by decide
theorem chain_21 : chainOK 21 [1, 14, 7, 21, 15, 6, 9, 12, 3, 18, 10, 5, 16, 20, 8, 13, 2, 19, 17, 4, 11] = true := by decide
theorem chain_22 : chainOK 22 [1, 5, 10, 18, 3, 12, 16, 20, 8, 7, 14, 22, 6, 9, 19, 17, 11, 4, 2, 13, 15, 21] = true := by decide
theorem chain_23 : chainOK 23 [1, 14, 22, 23, 5, 10, 18, 3, 7, 21, 15, 6, 9, 12, 16, 20, 8, 13, 2, 19, 17, 4, 11] = true := by decide
theorem chain_24 : chainOK 24 [1, 14, 22, 23, 5, 10, 18, 3, 7, 21, 15, 6, 9, 12, 16, 20, 8, 13, 2, 19, 17, 11, 4, 24] = true := by decide
theorem chain_25 : chainOK 25 [1, 14, 22, 23, 5, 10, 18, 3, 7, 21, 15, 6, 9, 19, 17, 11, 25, 20, 16, 12, 24, 4, 2, 8, 13] = true := by decide
theorem chain_26 : chainOK 26 [1, 14, 22, 23, 5, 16, 20, 25, 3, 18, 10, 11, 17, 4, 6, 15, 13, 8, 7, 21, 24, 12, 9, 19, 2, 26] = true := by decide
theorem chain_27 : chainOK 27 [1, 14, 22, 23, 5, 16, 20, 25, 3, 7, 8, 13, 15, 21, 24, 12, 9, 6, 4, 2, 26, 19, 17, 11, 10, 18, 27] = true := by decide
theorem chain_28 : chainOK 28 [1, 14, 22, 23, 5, 16, 20, 25, 3, 7, 21, 15, 6, 9, 12, 24, 4, 11, 10, 18, 27, 28, 17, 19, 26, 2, 8, 13] = true := by decide
theorem chain_29 : chainOK 29 [1, 14, 22, 23, 5, 10, 18, 27, 28, 17, 11, 25, 3, 7, 21, 15, 6, 4, 24, 12, 9, 19, 26, 29, 16, 20, 8, 2, 13] = true := by decide
theorem chain_30 : chainOK 30 [1, 14, 22, 23, 5, 10, 18, 27, 28, 17, 11, 4, 24, 21, 7, 3, 12, 9, 6, 15, 30, 25, 20, 16, 29, 26, 19, 2, 8, 13] = true := by decide
theorem chain_31 : chainOK 31 [1, 14, 22, 23, 5, 31, 24, 21, 7, 29, 16, 12, 3, 18, 10, 26, 19, 9, 27, 28, 17, 11, 4, 2, 8, 13, 15, 6, 30, 25, 20] = true := by decide
theorem chain_32 : chainOK 32 [1, 14, 22, 23, 32, 13, 15, 21, 7, 29, 16, 5, 31, 24, 12, 3, 18, 10, 26, 2, 8, 20, 25, 30, 6, 4, 11, 17, 19, 9, 27, 28] = true := by decide
theorem chain_33 : chainOK 33 [1, 14, 31, 5, 10, 18, 27, 28, 17, 11, 25, 20, 16, 29, 26, 19, 9, 12, 3, 33, 22, 23, 32, 4, 24, 21, 7, 8, 2, 13, 15, 6, 30] = true := by decide
theorem chain_34 : chainOK 34 [1, 14, 31, 5, 10, 18, 27, 28, 17, 11, 25, 20, 16, 29, 26, 19, 9, 12, 3, 33, 22, 23, 32, 34, 2, 4, 24, 21, 7, 8, 13, 15, 6, 30] = true := by decide
theorem chain_35 : chainOK 35 [1, 14, 22, 33, 3, 18, 27, 28, 17, 19, 9, 12, 16, 29, 7, 8, 20, 25, 30, 6, 15, 21, 24, 31, 35, 10, 5, 23, 13, 32, 4, 11, 34, 2, 26] = true := by decide
theorem chain_36 : chainOK 36 [1, 14, 22, 33, 3, 18, 27, 28, 17, 11, 25, 20, 35, 10, 5, 31, 24, 12, 16, 29, 7, 8, 13, 23, 32, 4, 2, 26, 19, 9, 36, 30, 6, 15, 21, 34] = true := by decide
theorem chain_37 : chainOK 37 [1, 14, 22, 33, 3, 7, 21, 15, 6, 30, 25, 20, 35, 31, 24, 12, 16, 5, 23, 13, 32, 34, 11, 4, 17, 28, 8, 2, 19, 36, 9, 27, 18, 10, 26, 29, 37] = true := by decide
theorem chain_38 : chainOK 38 [1, 14, 22, 33, 3, 12, 16, 5, 23, 32, 13, 15, 6, 30, 25, 20, 35, 31, 24, 21, 34, 11, 4, 2, 8, 7, 29, 37, 18, 10, 26, 19, 36, 9, 27, 28, 17, 38] = true := by decide
theorem chain_39 : chainOK 39 [1, 14, 22, 33, 3, 12, 24, 31, 35, 20, 25, 30, 36, 9, 6, 15, 21, 7, 38, 28, 27, 39, 16, 5, 23, 13, 8, 37, 18, 10, 11, 17, 4, 32, 34, 2, 19, 26, 29] = true := by decide
theorem chain_40 : chainOK 40 [1, 14, 22, 33, 3, 12, 24, 31, 35, 20, 25, 30, 36, 9, 6, 39, 16, 5, 23, 32, 4, 11, 10, 18, 27, 28, 17, 19, 26, 29, 37, 8, 2, 13, 15, 40, 38, 7, 21, 34] = true := by decide
theorem chain_41 : chainOK 41 [1, 35, 20, 16, 39, 27, 18, 10, 5, 31, 14, 22, 23, 32, 13, 8, 28, 38, 40, 15, 6, 30, 36, 9, 12, 33, 3, 7, 21, 24, 4, 17, 11, 25, 41, 37, 29, 26, 19, 2, 34] = true := by decide
theorem chain_42 : chainOK 42 [1, 35, 20, 16, 39, 27, 18, 10, 5, 31, 14, 22, 23, 32, 34, 11, 25, 41, 37, 29, 26, 40, 38, 28, 17, 4, 2, 8, 7, 21, 24, 12, 33, 3, 42, 13, 15, 6, 30, 36, 9, 19] = true := by decide
theorem chain_43 : chainOK 43 [1, 14, 22, 33, 3, 18, 27, 39, 6, 9, 12, 16, 20, 25, 30, 36, 42, 24, 31, 35, 43, 23, 5, 10, 11, 34, 21, 15, 40, 26, 19, 2, 13, 32, 4, 41, 37, 29, 7, 8, 28, 17, 38] = true := by decide
theorem chain_44 : chainOK 44 [1, 44, 22, 33, 3, 18, 27, 39, 6, 9, 12, 16, 20, 25, 30, 36, 42, 24, 21, 15, 40, 5, 31, 14, 41, 37, 29, 7, 38, 28, 8, 13, 23, 32, 34, 11, 4, 17, 19, 2, 26, 10, 35, 43] = true := by decide
theorem chain_45 : chainOK 45 [1, 44, 22, 14, 31, 35, 20, 16, 39, 27, 18, 37, 29, 7, 8, 28, 38, 17, 11, 10, 5, 40, 26, 19, 9, 36, 30, 6, 15, 21, 45, 33, 3, 25, 41, 4, 24, 12, 43, 2, 34, 32, 23, 13, 42] = true := by decide
theorem chain_46 : chainOK 46 [1, 44, 22, 14, 31, 35, 43, 23, 5, 40, 38, 28, 17, 11, 10, 18, 27, 39, 16, 20, 25, 41, 37, 29, 26, 19, 36, 30, 6, 9, 46, 45, 33, 12, 3, 7, 8, 2, 4, 24, 42, 13, 15, 21, 34, 32] = true := by decide
theorem chain_47 : chainOK 47 [1, 14, 41, 37, 18, 27, 39, 16, 29, 7, 38, 28, 17, 4, 6, 22, 33, 3, 12, 9, 36, 30, 25, 11, 44, 34, 21, 15, 40, 5, 10, 45, 46, 20, 35, 31, 24, 42, 13, 32, 23, 43, 2, 8, 47, 19, 26] = true := by decide
theorem chain_48 : chainOK 48 [1, 14, 41, 37, 29, 16, 39, 27, 18, 48, 7, 38, 28, 17, 4, 6, 22, 33, 3, 12, 9, 36, 30, 25, 11, 44, 34, 21, 15, 40, 5, 10, 45, 46, 20, 35, 31, 24, 42, 13, 32, 23, 43, 2, 8, 47, 19, 26] = true := by decide
theorem chain_49 : chainOK 49 [1, 14, 41, 37, 18, 27, 39, 16, 29, 49, 42, 36, 9, 46, 20, 25, 3, 12, 33, 45, 10, 35, 31, 5, 40, 26, 19, 47, 44, 22, 6, 30, 15, 21, 24, 4, 11, 17, 28, 38, 7, 48, 43, 23, 32, 34, 2, 8, 13] = true := by decide
theorem chain_50 : chainOK 50 [1, 14, 22, 33, 45, 46, 20, 35, 31, 47, 44, 34, 21, 24, 12, 43, 23, 32, 13, 15, 40, 5, 10, 11, 25, 3, 42, 36, 30, 48, 18, 27, 9, 6, 39, 16, 50, 41, 4, 2, 19, 26, 29, 37, 8, 7, 38, 28, 17, 49] = true := by decide
theorem chain_51 : chainOK 51 [1, 14, 22, 33, 45, 46, 20, 35, 31, 47, 44, 34, 21, 24, 12, 43, 23, 32, 13, 42, 3, 25, 11, 10, 5, 16, 39, 27, 18, 48, 7, 8, 37, 29, 49, 6, 9, 36, 30, 15, 51, 40, 26, 2, 19, 17, 4, 41, 50, 28, 38] = true := by decide
theorem chain_52 : chainOK 52 [1, 35, 20, 46, 45, 33, 22, 44, 47, 31, 14, 52, 39, 16, 50, 5, 10, 11, 25, 41, 37, 18, 3, 12, 24, 21, 34, 32, 23, 43, 48, 7, 29, 26, 40, 38, 28, 8, 2, 13, 42, 49, 17, 4, 51, 27, 9, 19, 36, 30, 6, 15] = true := by decide
theorem chain_53 : chainOK 53 [1, 35, 20, 46, 45, 33, 22, 44, 47, 31, 14, 41, 37, 8, 28, 50, 5, 10, 18, 27, 39, 16, 29, 49, 6, 9, 12, 24, 21, 7, 48, 43, 23, 32, 34, 11, 4, 17, 38, 40, 51, 15, 30, 25, 3, 42, 36, 19, 26, 52, 53, 2, 13] = true := by decide
theorem neck_12 : neckOK 12 [1, 5, 10, 11, 4, 6, 9, 12, 3, 7, 8, 2] = true := by decide
theorem neck_13 : neckOK 13 [1, 5, 10, 11, 4, 6, 9, 12, 3, 7, 8, 13, 2] = true := by decide
theorem neck_15 : neckOK 15 [1, 5, 10, 11, 4, 2, 8, 13, 15, 6, 9, 12, 3, 7, 14] = true := by decide
theorem neck_16 : neckOK 16 [1, 14, 7, 3, 12, 16, 5, 10, 11, 4, 2, 8, 13, 15, 6, 9] = true := by decide
theorem neck_17 : neckOK 17 [1, 14, 7, 3, 12, 16, 5, 10, 11, 17, 4, 2, 8, 13, 15, 6, 9] = true := by decide
theorem neck_18 : neckOK 18 [1, 14, 7, 3, 18, 10, 11, 17, 4, 2, 8, 13, 15, 6, 9, 12, 16, 5] = true := by decide
theorem neck_19 : neckOK 19 [1, 14, 7, 3, 18, 10, 5, 16, 12, 9, 19, 17, 11, 4, 6, 15, 13, 8, 2] = true := by decide
theorem neck_20 : neckOK 20 [1, 14, 7, 3, 18, 10, 5, 16, 12, 9, 19, 17, 11, 4, 6, 15, 13, 2, 8, 20] = true := by decide
theorem neck_21 : neckOK 21 [1, 14, 7, 21, 15, 6, 9, 12, 3, 18, 10, 11, 4, 17, 19, 2, 13, 8, 20, 16, 5] = true := by decide
theorem neck_22 : neckOK 22 [1, 5, 10, 18, 3, 12, 16, 20, 8, 7, 21, 15, 13, 2, 4, 11, 17, 19, 9, 6, 22, 14] = true := by decide
theorem neck_23 : neckOK 23 [1, 14, 22, 23, 5, 10, 18, 3, 7, 21, 15, 6, 4, 11, 17, 19, 9, 12, 16, 20, 8, 13, 2] = true := by decide
theorem neck_24 : neckOK 24 [1, 14, 22, 23, 5, 10, 18, 3, 7, 21, 15, 6, 9, 19, 17, 11, 4, 24, 12, 16, 20, 8, 13, 2] = true := by decide
theorem neck_25 : neckOK 25 [1, 14, 22, 23, 5, 10, 18, 3, 7, 21, 15, 13, 8, 2, 19, 17, 11, 25, 20, 16, 12, 24, 4, 6, 9] = true := by decide
theorem neck_26 : neckOK 26 [1, 14, 22, 23, 5, 16, 20, 25, 3, 18, 10, 11, 17, 4, 6, 15, 13, 8, 7, 21, 24, 12, 9, 19, 26, 2] = true := by decide
theorem neck_27 : neckOK 27 [1, 14, 22, 23, 5, 16, 20, 25, 3, 7, 8, 13, 15, 21, 24, 12, 9, 6, 4, 2, 26, 19, 17, 11, 10, 18, 27] = true := by decide
theorem neck_28 : neckOK 28 [1, 14, 22, 23, 5, 16, 20, 25, 3, 7, 21, 15, 6, 9, 12, 24, 4, 11, 17, 19, 26, 10, 18, 27, 28, 8, 13, 2] = true := by decide
theorem neck_29 : neckOK 29 [1, 14, 22, 23, 5, 10, 18, 27, 28, 17, 11, 25, 3, 7, 21, 15, 6, 4, 24, 12, 9, 19, 26, 29, 16, 20, 8, 13, 2] = true := by decide
theorem neck_30 : neckOK 30 [1, 14, 22, 23, 5, 10, 18, 27, 28, 17, 11, 4, 24, 21, 7, 3, 12, 9, 19, 26, 29, 16, 20, 25, 30, 6, 15, 13, 8, 2] = true := by decide
theorem neck_31 : neckOK 31 [1, 14, 22, 23, 5, 31, 24, 21, 7, 29, 16, 12, 3, 18, 10, 26, 19, 9, 27, 28, 17, 11, 4, 2, 8, 13, 15, 6, 30, 25, 20] = true := by decide
theorem neck_32 : neckOK 32 [1, 14, 22, 23, 32, 13, 15, 21, 7, 29, 16, 5, 31, 24, 12, 3, 18, 10, 26, 2, 8, 28, 27, 9, 19, 17, 11, 4, 6, 30, 25, 20] = true := by decide
theorem neck_33 : neckOK 33 [1, 14, 31, 5, 10, 18, 27, 28, 17, 11, 25, 20, 16, 29, 26, 19, 9, 12, 3, 33, 22, 23, 32, 13, 15, 30, 6, 4, 24, 21, 7, 8, 2] = true := by decide
theorem neck_34 : neckOK 34 [1, 14, 31, 5, 10, 18, 27, 28, 17, 11, 25, 20, 16, 29, 26, 19, 9, 12, 24, 4, 6, 30, 15, 21, 34, 32, 23, 22, 33, 3, 7, 8, 13, 2] = true := by decide
theorem neck_35 : neckOK 35 [1, 14, 22, 33, 3, 18, 27, 28, 17, 19, 9, 12, 16, 29, 7, 8, 20, 25, 30, 6, 15, 21, 24, 31, 35, 10, 26, 2, 4, 11, 34, 32, 13, 23, 5] = true := by decide
theorem neck_36 : neckOK 36 [1, 14, 22, 33, 3, 18, 27, 28, 17, 11, 25, 20, 35, 10, 5, 31, 24, 12, 16, 29, 7, 8, 13, 23, 32, 4, 6, 30, 15, 21, 34, 2, 26, 19, 36, 9] = true := by decide
theorem neck_37 : neckOK 37 [1, 14, 22, 33, 3, 7, 21, 15, 6, 30, 25, 20, 35, 31, 24, 12, 16, 5, 23, 13, 32, 34, 11, 4, 17, 28, 8, 37, 29, 26, 10, 18, 27, 9, 36, 19, 2] = true := by decide
theorem neck_38 : neckOK 38 [1, 14, 22, 33, 3, 12, 16, 5, 23, 32, 13, 15, 6, 30, 25, 20, 35, 31, 24, 21, 34, 11, 4, 2, 8, 37, 18, 10, 26, 29, 7, 38, 28, 17, 19, 36, 9, 27] = true := by decide
theorem neck_39 : neckOK 39 [1, 14, 22, 33, 3, 12, 24, 31, 35, 20, 25, 30, 36, 9, 6, 15, 21, 7, 38, 28, 27, 39, 16, 5, 10, 18, 37, 29, 26, 19, 17, 4, 11, 34, 32, 23, 13, 8, 2] = true := by decide
theorem neck_40 : neckOK 40 [1, 14, 22, 33, 3, 12, 24, 31, 35, 20, 25, 30, 36, 9, 6, 39, 16, 5, 23, 32, 4, 11, 10, 18, 27, 28, 17, 19, 26, 29, 37, 8, 13, 15, 40, 38, 7, 21, 34, 2] = true := by decide
theorem neck_41 : neckOK 41 [1, 35, 20, 16, 39, 27, 18, 10, 5, 31, 14, 22, 23, 32, 13, 8, 28, 38, 40, 15, 6, 30, 36, 9, 12, 33, 3, 7, 21, 24, 4, 17, 19, 26, 29, 37, 41, 25, 11, 34, 2] = true := by decide
theorem neck_42 : neckOK 42 [1, 35, 20, 16, 39, 27, 18, 10, 5, 31, 14, 22, 23, 32, 34, 11, 25, 41, 37, 29, 26, 40, 38, 28, 17, 4, 2, 8, 7, 21, 24, 12, 33, 3, 42, 13, 15, 6, 30, 36, 19, 9] = true := by decide
theorem neck_43 : neckOK 43 [1, 14, 22, 33, 3, 18, 27, 39, 6, 9, 12, 16, 20, 25, 30, 36, 42, 24, 31, 35, 43, 23, 5, 10, 11, 34, 21, 15, 40, 26, 19, 17, 28, 38, 7, 29, 37, 41, 4, 32, 13, 8, 2] = true := by decide
theorem neck_44 : neckOK 44 [1, 44, 22, 33, 3, 18, 27, 39, 6, 9, 12, 16, 20, 25, 30, 36, 42, 24, 21, 15, 40, 5, 31, 14, 41, 37, 29, 7, 38, 28, 8, 13, 23, 32, 34, 11, 4, 17, 19, 26, 10, 35, 43, 2] = true := by decide
theorem neck_45 : neckOK 45 [1, 44, 22, 14, 31, 35, 20, 16, 39, 27, 18, 37, 29, 7, 8, 28, 38, 17, 11, 10, 5, 40, 26, 19, 9, 36, 30, 6, 15, 13, 23, 43, 12, 33, 45, 21, 24, 42, 3, 25, 41, 4, 32, 34, 2] = true := by decide
theorem neck_46 : neckOK 46 [1, 44, 22, 14, 31, 35, 43, 23, 5, 40, 38, 28, 17, 11, 10, 18, 27, 39, 16, 20, 25, 41, 37, 29, 26, 19, 36, 30, 6, 9, 46, 45, 33, 12, 24, 4, 32, 34, 21, 15, 13, 42, 3, 7, 8, 2] = true := by decide
theorem neck_47 : neckOK 47 [1, 14, 41, 37, 18, 27, 39, 16, 29, 7, 38, 28, 17, 4, 6, 22, 33, 3, 12, 9, 36, 30, 25, 11, 44, 34, 21, 15, 40, 5, 10, 45, 46, 20, 8, 47, 19, 26, 2, 43, 23, 32, 13, 42, 24, 31, 35] = true := by decide
theorem neck_48 : neckOK 48 [1, 14, 41, 37, 29, 16, 39, 27, 18, 48, 7, 38, 28, 17, 4, 6, 22, 33, 3, 12, 9, 36, 30, 25, 11, 44, 34, 21, 15, 40, 5, 10, 45, 46, 20, 8, 47, 19, 26, 2, 43, 23, 32, 13, 42, 24, 31, 35] = true := by decide
theorem neck_49 : neckOK 49 [1, 14, 41, 37, 18, 27, 39, 16, 29, 49, 42, 36, 9, 46, 20, 25, 3, 12, 33, 45, 10, 35, 31, 5, 40, 26, 19, 47, 44, 22, 6, 30, 15, 21, 24, 4, 11, 17, 38, 28, 8, 7, 48, 43, 23, 13, 32, 34, 2] = true := by decide
theorem neck_50 : neckOK 50 [1, 14, 22, 33, 45, 46, 20, 35, 31, 47, 44, 34, 21, 24, 12, 43, 23, 32, 13, 15, 40, 5, 10, 11, 25, 3, 42, 36, 30, 48, 18, 27, 9, 6, 39, 16, 50, 28, 38, 7, 8, 37, 41, 4, 17, 49, 29, 26, 19, 2] = true := by decide
theorem neck_51 : neckOK 51 [1, 14, 22, 33, 45, 46, 20, 35, 31, 47, 44, 34, 21, 24, 12, 43, 23, 32, 13, 42, 3, 25, 11, 10, 5, 16, 39, 27, 18, 48, 7, 8, 37, 29, 49, 6, 9, 36, 30, 15, 51, 40, 26, 19, 17, 38, 28, 50, 41, 4, 2] = true := by decide
theorem neck_52 : neckOK 52 [1, 35, 20, 46, 45, 33, 22, 44, 47, 31, 14, 52, 39, 16, 50, 5, 10, 11, 25, 41, 37, 18, 3, 12, 24, 21, 34, 32, 23, 43, 48, 7, 29, 26, 40, 38, 28, 8, 2, 13, 42, 49, 17, 4, 51, 15, 6, 30, 36, 19, 9, 27] = true := by decide
theorem neck_53 : neckOK 53 [1, 35, 20, 46, 45, 33, 22, 44, 47, 31, 14, 41, 37, 8, 28, 50, 5, 10, 18, 27, 39, 16, 29, 49, 6, 9, 12, 24, 21, 7, 48, 43, 23, 32, 34, 11, 4, 17, 38, 40, 51, 15, 30, 25, 3, 42, 36, 19, 26, 52, 53, 13, 2] = true := by decide

theorem small_chains (N : ℕ) (h : N = 2 ∨ (9 ≤ N ∧ N ≤ 53)) : ∃ l, TriChain N l := by
  rcases h with rfl | ⟨h1, h2⟩
  · exact ⟨_, triChain_of_chainOK chain_2⟩
  · interval_cases N
    · exact ⟨_, triChain_of_chainOK chain_9⟩
    · exact ⟨_, triChain_of_chainOK chain_10⟩
    · exact ⟨_, triChain_of_chainOK chain_11⟩
    · exact ⟨_, triChain_of_chainOK chain_12⟩
    · exact ⟨_, triChain_of_chainOK chain_13⟩
    · exact ⟨_, triChain_of_chainOK chain_14⟩
    · exact ⟨_, triChain_of_chainOK chain_15⟩
    · exact ⟨_, triChain_of_chainOK chain_16⟩
    · exact ⟨_, triChain_of_chainOK chain_17⟩
    · exact ⟨_, triChain_of_chainOK chain_18⟩
    · exact ⟨_, triChain_of_chainOK chain_19⟩
    · exact ⟨_, triChain_of_chainOK chain_20⟩
    · exact ⟨_, triChain_of_chainOK chain_21⟩
    · exact ⟨_, triChain_of_chainOK chain_22⟩
    · exact ⟨_, triChain_of_chainOK chain_23⟩
    · exact ⟨_, triChain_of_chainOK chain_24⟩
    · exact ⟨_, triChain_of_chainOK chain_25⟩
    · exact ⟨_, triChain_of_chainOK chain_26⟩
    · exact ⟨_, triChain_of_chainOK chain_27⟩
    · exact ⟨_, triChain_of_chainOK chain_28⟩
    · exact ⟨_, triChain_of_chainOK chain_29⟩
    · exact ⟨_, triChain_of_chainOK chain_30⟩
    · exact ⟨_, triChain_of_chainOK chain_31⟩
    · exact ⟨_, triChain_of_chainOK chain_32⟩
    · exact ⟨_, triChain_of_chainOK chain_33⟩
    · exact ⟨_, triChain_of_chainOK chain_34⟩
    · exact ⟨_, triChain_of_chainOK chain_35⟩
    · exact ⟨_, triChain_of_chainOK chain_36⟩
    · exact ⟨_, triChain_of_chainOK chain_37⟩
    · exact ⟨_, triChain_of_chainOK chain_38⟩
    · exact ⟨_, triChain_of_chainOK chain_39⟩
    · exact ⟨_, triChain_of_chainOK chain_40⟩
    · exact ⟨_, triChain_of_chainOK chain_41⟩
    · exact ⟨_, triChain_of_chainOK chain_42⟩
    · exact ⟨_, triChain_of_chainOK chain_43⟩
    · exact ⟨_, triChain_of_chainOK chain_44⟩
    · exact ⟨_, triChain_of_chainOK chain_45⟩
    · exact ⟨_, triChain_of_chainOK chain_46⟩
    · exact ⟨_, triChain_of_chainOK chain_47⟩
    · exact ⟨_, triChain_of_chainOK chain_48⟩
    · exact ⟨_, triChain_of_chainOK chain_49⟩
    · exact ⟨_, triChain_of_chainOK chain_50⟩
    · exact ⟨_, triChain_of_chainOK chain_51⟩
    · exact ⟨_, triChain_of_chainOK chain_52⟩
    · exact ⟨_, triChain_of_chainOK chain_53⟩

theorem small_necklaces (N : ℕ) (h1 : 12 ≤ N) (h2 : N ≤ 53) (h3 : N ≠ 14) : ∃ l, TriNecklace N l := by
  interval_cases N
  · exact ⟨_, triNecklace_of_neckOK neck_12⟩
  · exact ⟨_, triNecklace_of_neckOK neck_13⟩
  · exact absurd rfl h3
  · exact ⟨_, triNecklace_of_neckOK neck_15⟩
  · exact ⟨_, triNecklace_of_neckOK neck_16⟩
  · exact ⟨_, triNecklace_of_neckOK neck_17⟩
  · exact ⟨_, triNecklace_of_neckOK neck_18⟩
  · exact ⟨_, triNecklace_of_neckOK neck_19⟩
  · exact ⟨_, triNecklace_of_neckOK neck_20⟩
  · exact ⟨_, triNecklace_of_neckOK neck_21⟩
  · exact ⟨_, triNecklace_of_neckOK neck_22⟩
  · exact ⟨_, triNecklace_of_neckOK neck_23⟩
  · exact ⟨_, triNecklace_of_neckOK neck_24⟩
  · exact ⟨_, triNecklace_of_neckOK neck_25⟩
  · exact ⟨_, triNecklace_of_neckOK neck_26⟩
  · exact ⟨_, triNecklace_of_neckOK neck_27⟩
  · exact ⟨_, triNecklace_of_neckOK neck_28⟩
  · exact ⟨_, triNecklace_of_neckOK neck_29⟩
  · exact ⟨_, triNecklace_of_neckOK neck_30⟩
  · exact ⟨_, triNecklace_of_neckOK neck_31⟩
  · exact ⟨_, triNecklace_of_neckOK neck_32⟩
  · exact ⟨_, triNecklace_of_neckOK neck_33⟩
  · exact ⟨_, triNecklace_of_neckOK neck_34⟩
  · exact ⟨_, triNecklace_of_neckOK neck_35⟩
  · exact ⟨_, triNecklace_of_neckOK neck_36⟩
  · exact ⟨_, triNecklace_of_neckOK neck_37⟩
  · exact ⟨_, triNecklace_of_neckOK neck_38⟩
  · exact ⟨_, triNecklace_of_neckOK neck_39⟩
  · exact ⟨_, triNecklace_of_neckOK neck_40⟩
  · exact ⟨_, triNecklace_of_neckOK neck_41⟩
  · exact ⟨_, triNecklace_of_neckOK neck_42⟩
  · exact ⟨_, triNecklace_of_neckOK neck_43⟩
  · exact ⟨_, triNecklace_of_neckOK neck_44⟩
  · exact ⟨_, triNecklace_of_neckOK neck_45⟩
  · exact ⟨_, triNecklace_of_neckOK neck_46⟩
  · exact ⟨_, triNecklace_of_neckOK neck_47⟩
  · exact ⟨_, triNecklace_of_neckOK neck_48⟩
  · exact ⟨_, triNecklace_of_neckOK neck_49⟩
  · exact ⟨_, triNecklace_of_neckOK neck_50⟩
  · exact ⟨_, triNecklace_of_neckOK neck_51⟩
  · exact ⟨_, triNecklace_of_neckOK neck_52⟩
  · exact ⟨_, triNecklace_of_neckOK neck_53⟩

end TriChains
