import LeanProofs.PentChains.Basic

/-!
# Small cases: explicit pentagonal chains (`4 ≤ n ≤ 59`) and necklaces (`9 ≤ n ≤ 59`)

Certificates from verify/small_certificates.json, each checked by `decide` through `chainB'`/`neckB`.
-/

namespace PentChains

/-- A list of `1..N` without repetition, adjacent sums generalized pentagonal. -/
def TriChain (N : ℕ) (l : List ℤ) : Prop := l.Nodup ∧ (∀ x, x ∈ l ↔ 1 ≤ x ∧ x ≤ N) ∧ l.IsChain (fun a b => IsTri (a + b))

/-- A pentagonal chain whose last and first entries also sum to a generalized pentagonal number. -/
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

theorem chain_4 : chainOK 4 [1, 4, 3, 2] = true := by decide
theorem chain_5 : chainOK 5 [1, 4, 3, 2, 5] = true := by decide
theorem chain_6 : chainOK 6 [5, 2, 3, 4, 1, 6] = true := by decide
theorem chain_7 : chainOK 7 [6, 1, 4, 3, 2, 5, 7] = true := by decide
theorem chain_8 : chainOK 8 [3, 2, 5, 7, 8, 4, 1, 6] = true := by decide
theorem chain_9 : chainOK 9 [1, 6, 9, 3, 2, 5, 7, 8, 4] = true := by decide
theorem chain_10 : chainOK 10 [1, 6, 9, 3, 4, 8, 7, 5, 2, 10] = true := by decide
theorem chain_11 : chainOK 11 [1, 6, 9, 3, 2, 10, 5, 7, 8, 4, 11] = true := by decide
theorem chain_12 : chainOK 12 [1, 6, 9, 3, 12, 10, 2, 5, 7, 8, 4, 11] = true := by decide
theorem chain_13 : chainOK 13 [1, 6, 9, 13, 2, 3, 12, 10, 5, 7, 8, 4, 11] = true := by decide
theorem chain_14 : chainOK 14 [1, 6, 9, 13, 2, 10, 5, 7, 8, 14, 12, 3, 4, 11] = true := by decide
theorem chain_15 : chainOK 15 [1, 6, 9, 13, 2, 3, 4, 11, 15, 7, 5, 10, 12, 14, 8] = true := by decide
theorem chain_16 : chainOK 16 [1, 6, 16, 10, 5, 2, 13, 9, 3, 12, 14, 8, 4, 11, 15, 7] = true := by decide
theorem chain_17 : chainOK 17 [1, 6, 16, 10, 12, 14, 8, 4, 11, 15, 7, 5, 17, 9, 3, 2, 13] = true := by decide
theorem chain_18 : chainOK 18 [1, 6, 16, 10, 12, 14, 8, 7, 15, 11, 4, 18, 17, 5, 2, 3, 9, 13] = true := by decide
theorem chain_19 : chainOK 19 [1, 6, 16, 19, 7, 15, 11, 4, 8, 14, 12, 3, 9, 13, 2, 10, 5, 17, 18] = true := by decide
theorem chain_20 : chainOK 20 [1, 11, 15, 20, 6, 16, 19, 7, 5, 10, 2, 13, 9, 17, 18, 4, 3, 12, 14, 8] = true := by decide
theorem chain_21 : chainOK 21 [1, 11, 15, 20, 6, 16, 10, 12, 14, 21, 19, 7, 5, 2, 13, 9, 3, 4, 8, 18, 17] = true := by decide
theorem chain_22 : chainOK 22 [1, 11, 15, 20, 6, 16, 10, 12, 14, 21, 19, 7, 5, 2, 3, 9, 13, 22, 4, 8, 18, 17] = true := by decide
theorem chain_23 : chainOK 23 [1, 11, 15, 20, 6, 16, 10, 2, 13, 9, 17, 5, 7, 19, 21, 14, 8, 18, 22, 4, 3, 12, 23] = true := by decide
theorem chain_24 : chainOK 24 [1, 6, 20, 15, 11, 24, 16, 10, 2, 13, 9, 17, 5, 7, 19, 21, 14, 8, 18, 22, 4, 3, 12, 23] = true := by decide
theorem chain_25 : chainOK 25 [1, 25, 15, 11, 24, 16, 6, 20, 2, 10, 5, 7, 19, 21, 14, 8, 4, 18, 22, 13, 9, 17, 23, 3, 12] = true := by decide
theorem chain_26 : chainOK 26 [1, 6, 20, 15, 11, 24, 16, 19, 7, 8, 4, 18, 22, 13, 2, 3, 9, 17, 23, 12, 10, 5, 21, 14, 26, 25] = true := by decide
theorem chain_27 : chainOK 27 [1, 6, 20, 15, 11, 24, 16, 19, 7, 5, 21, 14, 26, 25, 10, 2, 13, 27, 8, 4, 22, 18, 17, 9, 3, 12, 23] = true := by decide
theorem chain_28 : chainOK 28 [1, 6, 20, 15, 11, 24, 16, 19, 21, 14, 26, 25, 10, 2, 5, 7, 28, 12, 23, 3, 9, 17, 18, 4, 8, 27, 13, 22] = true := by decide
theorem chain_29 : chainOK 29 [1, 21, 14, 26, 25, 15, 20, 6, 9, 13, 27, 8, 7, 19, 16, 24, 11, 29, 22, 4, 18, 17, 5, 2, 10, 12, 3, 23, 28] = true := by decide
theorem chain_30 : chainOK 30 [1, 25, 26, 14, 21, 19, 16, 6, 20, 15, 7, 8, 18, 4, 11, 24, 27, 30, 5, 10, 2, 13, 22, 29, 28, 12, 3, 9, 17, 23] = true := by decide
theorem chain_31 : chainOK 31 [1, 25, 15, 11, 24, 16, 6, 20, 31, 26, 9, 13, 27, 30, 10, 2, 5, 17, 18, 22, 29, 28, 7, 8, 4, 3, 19, 21, 14, 12, 23] = true := by decide
theorem chain_32 : chainOK 32 [1, 6, 16, 24, 11, 29, 22, 13, 27, 30, 21, 14, 26, 9, 31, 20, 15, 25, 10, 2, 5, 17, 18, 4, 8, 7, 19, 32, 3, 12, 23, 28] = true := by decide
theorem chain_33 : chainOK 33 [1, 6, 16, 19, 21, 14, 26, 25, 32, 8, 27, 30, 10, 5, 7, 15, 20, 31, 9, 13, 2, 24, 33, 18, 17, 23, 3, 12, 28, 29, 11, 4, 22] = true := by decide
theorem chain_34 : chainOK 34 [1, 34, 6, 16, 19, 21, 14, 26, 25, 32, 8, 27, 30, 10, 5, 7, 15, 20, 31, 9, 13, 2, 24, 33, 18, 17, 23, 3, 12, 28, 29, 11, 4, 22] = true := by decide
theorem chain_35 : chainOK 35 [1, 34, 6, 20, 15, 11, 29, 28, 23, 12, 14, 21, 30, 27, 13, 22, 35, 16, 24, 33, 2, 10, 5, 7, 19, 3, 32, 25, 26, 9, 17, 18, 8, 4, 31] = true := by decide
theorem chain_36 : chainOK 36 [1, 11, 29, 28, 12, 14, 26, 25, 15, 20, 31, 9, 6, 34, 23, 17, 18, 22, 13, 27, 8, 4, 36, 21, 30, 10, 5, 35, 16, 24, 2, 33, 7, 19, 3, 32] = true := by decide
theorem chain_37 : chainOK 37 [1, 11, 29, 28, 12, 23, 34, 6, 16, 35, 22, 13, 27, 24, 33, 18, 17, 9, 26, 31, 4, 36, 15, 20, 37, 14, 8, 7, 19, 3, 32, 25, 10, 2, 5, 21, 30] = true := by decide
theorem chain_38 : chainOK 38 [1, 11, 29, 28, 12, 23, 34, 6, 16, 35, 22, 13, 27, 24, 33, 18, 17, 9, 26, 31, 4, 36, 15, 20, 37, 14, 8, 7, 5, 21, 30, 10, 25, 32, 3, 2, 38, 19] = true := by decide
theorem chain_39 : chainOK 39 [1, 11, 29, 28, 23, 34, 6, 16, 35, 22, 13, 27, 24, 33, 37, 20, 15, 36, 4, 18, 17, 9, 31, 26, 25, 10, 30, 5, 2, 3, 12, 39, 38, 32, 8, 7, 19, 21, 14] = true := by decide
theorem chain_40 : chainOK 40 [1, 25, 26, 14, 21, 36, 15, 11, 29, 28, 7, 8, 27, 24, 33, 37, 40, 30, 5, 35, 16, 10, 12, 23, 34, 6, 20, 2, 13, 22, 4, 18, 17, 9, 31, 39, 38, 19, 3, 32] = true := by decide
theorem chain_41 : chainOK 41 [1, 25, 26, 14, 21, 30, 27, 8, 32, 19, 38, 13, 9, 31, 39, 12, 28, 7, 15, 20, 6, 29, 11, 40, 37, 3, 23, 34, 17, 5, 35, 22, 4, 18, 33, 2, 24, 16, 10, 41, 36] = true := by decide
theorem chain_42 : chainOK 42 [1, 25, 26, 14, 21, 30, 27, 8, 32, 19, 38, 13, 22, 35, 42, 9, 31, 39, 18, 4, 36, 15, 7, 5, 17, 34, 6, 20, 37, 40, 11, 29, 28, 23, 3, 12, 10, 41, 16, 24, 2, 33] = true := by decide
theorem chain_43 : chainOK 43 [1, 25, 26, 31, 39, 38, 32, 19, 21, 14, 43, 8, 27, 13, 9, 42, 35, 22, 18, 4, 36, 15, 7, 28, 12, 3, 23, 34, 17, 5, 30, 40, 11, 29, 6, 20, 37, 33, 2, 24, 16, 10, 41] = true := by decide
theorem chain_44 : chainOK 44 [1, 25, 26, 44, 13, 22, 35, 42, 9, 31, 39, 38, 32, 19, 16, 6, 20, 15, 7, 28, 29, 41, 36, 21, 5, 10, 30, 27, 24, 2, 33, 18, 4, 11, 40, 17, 34, 23, 12, 3, 37, 14, 8, 43] = true := by decide
theorem chain_45 : chainOK 45 [1, 39, 31, 20, 37, 40, 11, 15, 42, 35, 22, 29, 28, 23, 12, 45, 6, 34, 17, 9, 26, 25, 32, 3, 4, 18, 8, 14, 43, 27, 13, 38, 19, 7, 44, 33, 24, 2, 5, 21, 30, 10, 16, 41, 36] = true := by decide
theorem chain_46 : chainOK 46 [1, 39, 38, 13, 44, 26, 25, 45, 32, 19, 21, 14, 43, 27, 8, 7, 15, 36, 34, 6, 20, 31, 9, 42, 28, 12, 23, 3, 37, 33, 2, 24, 46, 11, 4, 18, 17, 40, 30, 5, 10, 16, 35, 22, 29, 41] = true := by decide
theorem chain_47 : chainOK 47 [1, 39, 38, 13, 44, 26, 25, 32, 45, 47, 23, 12, 28, 42, 35, 22, 29, 41, 10, 16, 6, 9, 31, 20, 15, 36, 34, 17, 18, 4, 3, 19, 7, 8, 43, 14, 21, 5, 2, 33, 37, 40, 30, 27, 24, 11, 46] = true := by decide
theorem chain_48 : chainOK 48 [1, 39, 38, 13, 27, 43, 34, 36, 41, 16, 35, 42, 15, 20, 6, 29, 22, 48, 44, 26, 9, 31, 46, 11, 24, 2, 33, 18, 4, 8, 7, 28, 23, 17, 40, 37, 14, 12, 3, 19, 21, 5, 30, 10, 47, 45, 25, 32] = true := by decide
theorem chain_49 : chainOK 49 [1, 39, 38, 13, 27, 43, 34, 36, 41, 16, 35, 42, 15, 20, 6, 29, 22, 48, 44, 26, 9, 31, 46, 11, 24, 33, 18, 4, 8, 7, 19, 32, 25, 45, 47, 10, 2, 49, 28, 12, 3, 23, 17, 5, 21, 14, 37, 40, 30] = true := by decide
theorem chain_50 : chainOK 50 [1, 39, 38, 13, 44, 26, 25, 32, 45, 47, 23, 12, 14, 37, 40, 17, 34, 43, 27, 30, 10, 41, 36, 21, 19, 16, 6, 9, 3, 48, 29, 22, 35, 5, 46, 31, 4, 11, 24, 2, 20, 15, 42, 50, 7, 28, 49, 8, 18, 33] = true := by decide
theorem chain_51 : chainOK 51 [1, 39, 38, 13, 44, 48, 22, 35, 42, 50, 27, 43, 34, 36, 15, 20, 31, 46, 11, 24, 16, 41, 29, 6, 9, 26, 51, 19, 7, 28, 49, 21, 14, 8, 4, 18, 33, 37, 40, 17, 5, 2, 3, 23, 12, 10, 30, 47, 45, 25, 32] = true := by decide
theorem chain_52 : chainOK 52 [1, 39, 38, 13, 44, 26, 31, 46, 11, 24, 27, 50, 20, 15, 42, 35, 16, 41, 36, 34, 43, 14, 37, 33, 2, 49, 51, 6, 9, 17, 40, 30, 21, 5, 7, 19, 32, 8, 18, 52, 25, 10, 47, 45, 12, 23, 28, 29, 22, 4, 3, 48] = true := by decide
theorem chain_53 : chainOK 53 [1, 50, 42, 35, 16, 41, 36, 15, 20, 37, 40, 11, 46, 24, 27, 30, 21, 14, 43, 34, 6, 29, 22, 13, 38, 19, 51, 49, 28, 7, 8, 32, 45, 25, 26, 44, 33, 2, 5, 10, 12, 23, 47, 53, 17, 9, 3, 48, 52, 18, 4, 31, 39] = true := by decide
theorem chain_54 : chainOK 54 [1, 50, 42, 35, 22, 13, 27, 43, 34, 36, 15, 20, 37, 14, 21, 30, 40, 11, 29, 41, 51, 6, 16, 19, 38, 54, 46, 24, 33, 44, 7, 28, 49, 2, 5, 10, 12, 23, 17, 53, 39, 18, 8, 4, 47, 45, 32, 3, 48, 52, 25, 26, 9, 31] = true := by decide
theorem chain_55 : chainOK 55 [1, 50, 42, 35, 16, 41, 36, 34, 43, 27, 13, 44, 26, 51, 6, 9, 31, 20, 15, 25, 45, 55, 22, 29, 48, 52, 40, 11, 46, 24, 33, 37, 14, 21, 30, 5, 7, 19, 32, 8, 49, 28, 12, 10, 2, 38, 39, 18, 17, 53, 4, 47, 23, 3, 54] = true := by decide
theorem chain_56 : chainOK 56 [1, 50, 42, 35, 16, 41, 51, 6, 20, 15, 36, 34, 43, 27, 13, 9, 26, 31, 39, 38, 54, 46, 11, 24, 53, 17, 40, 30, 47, 23, 28, 29, 22, 4, 18, 52, 48, 44, 56, 14, 8, 49, 21, 5, 7, 19, 32, 25, 10, 12, 45, 55, 2, 3, 37, 33] = true := by decide
theorem chain_57 : chainOK 57 [1, 50, 42, 35, 57, 20, 15, 55, 37, 40, 11, 46, 31, 39, 53, 24, 27, 30, 47, 45, 25, 52, 5, 10, 12, 28, 7, 33, 2, 13, 38, 32, 19, 16, 54, 23, 3, 4, 18, 17, 9, 6, 34, 36, 41, 29, 22, 48, 44, 26, 51, 49, 8, 43, 14, 21, 56] = true := by decide
theorem chain_58 : chainOK 58 [1, 50, 27, 30, 40, 52, 25, 26, 51, 41, 10, 47, 45, 32, 38, 39, 53, 17, 18, 8, 43, 49, 21, 14, 56, 36, 34, 58, 12, 23, 28, 42, 15, 55, 37, 20, 57, 35, 5, 7, 19, 16, 6, 29, 11, 4, 22, 13, 44, 33, 2, 24, 46, 31, 9, 48, 3, 54] = true := by decide
theorem chain_59 : chainOK 59 [1, 50, 27, 30, 40, 52, 25, 26, 51, 41, 59, 58, 42, 35, 57, 43, 34, 36, 56, 14, 21, 49, 8, 32, 19, 16, 6, 45, 47, 10, 5, 7, 15, 20, 37, 55, 2, 33, 44, 13, 38, 54, 46, 24, 11, 29, 28, 12, 23, 3, 48, 9, 17, 53, 39, 31, 4, 18, 22] = true := by decide
theorem neck_9 : neckOK 9 [1, 6, 9, 3, 2, 5, 7, 8, 4] = true := by decide
theorem neck_10 : neckOK 10 [1, 6, 9, 3, 2, 10, 5, 7, 8, 4] = true := by decide
theorem neck_11 : neckOK 11 [1, 6, 9, 3, 2, 10, 5, 7, 8, 4, 11] = true := by decide
theorem neck_12 : neckOK 12 [1, 6, 9, 3, 12, 10, 2, 5, 7, 8, 4, 11] = true := by decide
theorem neck_13 : neckOK 13 [1, 6, 9, 13, 2, 3, 12, 10, 5, 7, 8, 4, 11] = true := by decide
theorem neck_14 : neckOK 14 [1, 6, 9, 13, 2, 10, 5, 7, 8, 14, 12, 3, 4, 11] = true := by decide
theorem neck_15 : neckOK 15 [1, 6, 9, 13, 2, 3, 4, 8, 14, 12, 10, 5, 7, 15, 11] = true := by decide
theorem neck_16 : neckOK 16 [1, 6, 16, 10, 5, 2, 13, 9, 3, 12, 14, 8, 7, 15, 11, 4] = true := by decide
theorem neck_17 : neckOK 17 [1, 6, 16, 10, 12, 14, 8, 4, 3, 2, 13, 9, 17, 5, 7, 15, 11] = true := by decide
theorem neck_18 : neckOK 18 [1, 6, 16, 10, 12, 14, 8, 18, 4, 3, 2, 13, 9, 17, 5, 7, 15, 11] = true := by decide
theorem neck_19 : neckOK 19 [1, 6, 16, 19, 7, 15, 11, 4, 8, 18, 17, 5, 10, 2, 13, 9, 3, 12, 14] = true := by decide
theorem neck_20 : neckOK 20 [1, 11, 15, 20, 6, 16, 19, 7, 5, 10, 2, 13, 9, 17, 18, 8, 4, 3, 12, 14] = true := by decide
theorem neck_21 : neckOK 21 [1, 11, 15, 20, 6, 16, 10, 12, 14, 21, 19, 7, 8, 18, 17, 5, 2, 13, 9, 3, 4] = true := by decide
theorem neck_22 : neckOK 22 [1, 11, 15, 20, 6, 16, 10, 12, 14, 21, 19, 7, 5, 17, 9, 3, 2, 13, 22, 18, 8, 4] = true := by decide
theorem neck_23 : neckOK 23 [1, 11, 15, 20, 6, 16, 10, 2, 13, 9, 17, 5, 21, 14, 12, 23, 3, 19, 7, 8, 18, 22, 4] = true := by decide
theorem neck_24 : neckOK 24 [1, 6, 20, 15, 11, 24, 16, 10, 2, 13, 9, 17, 5, 21, 14, 12, 23, 3, 19, 7, 8, 18, 22, 4] = true := by decide
theorem neck_25 : neckOK 25 [1, 25, 15, 11, 24, 16, 6, 20, 2, 10, 5, 7, 19, 21, 14, 8, 18, 17, 23, 12, 3, 9, 13, 22, 4] = true := by decide
theorem neck_26 : neckOK 26 [1, 6, 20, 15, 11, 24, 16, 19, 7, 8, 4, 18, 22, 13, 2, 3, 9, 17, 23, 12, 10, 5, 21, 14, 26, 25] = true := by decide
theorem neck_27 : neckOK 27 [1, 6, 20, 15, 11, 24, 16, 19, 7, 5, 21, 14, 26, 25, 10, 2, 3, 12, 23, 17, 9, 13, 27, 8, 18, 22, 4] = true := by decide
theorem neck_28 : neckOK 28 [1, 6, 20, 15, 11, 24, 16, 19, 21, 14, 26, 25, 10, 2, 5, 7, 28, 12, 23, 3, 9, 17, 18, 8, 27, 13, 22, 4] = true := by decide
theorem neck_29 : neckOK 29 [1, 21, 14, 26, 25, 15, 20, 6, 9, 13, 27, 8, 7, 19, 16, 24, 11, 29, 22, 18, 17, 5, 2, 10, 12, 28, 23, 3, 4] = true := by decide
theorem neck_30 : neckOK 30 [1, 25, 26, 14, 21, 19, 16, 6, 20, 15, 7, 8, 18, 4, 22, 29, 28, 12, 23, 3, 9, 17, 5, 10, 30, 27, 13, 2, 24, 11] = true := by decide
theorem neck_31 : neckOK 31 [1, 25, 15, 11, 24, 16, 6, 20, 31, 26, 9, 13, 27, 30, 10, 2, 5, 17, 18, 22, 29, 28, 23, 12, 3, 4, 8, 7, 19, 21, 14] = true := by decide
theorem neck_32 : neckOK 32 [1, 6, 16, 24, 11, 29, 22, 13, 27, 30, 21, 14, 26, 9, 31, 20, 15, 25, 10, 2, 5, 17, 18, 8, 32, 19, 7, 28, 12, 23, 3, 4] = true := by decide
theorem neck_33 : neckOK 33 [1, 6, 16, 19, 21, 14, 26, 25, 32, 8, 27, 30, 10, 5, 7, 15, 20, 31, 9, 13, 2, 24, 33, 18, 17, 23, 3, 12, 28, 29, 22, 4, 11] = true := by decide
theorem neck_34 : neckOK 34 [1, 34, 6, 16, 19, 21, 14, 26, 25, 32, 8, 27, 30, 10, 5, 7, 15, 20, 31, 9, 13, 2, 24, 33, 18, 17, 23, 3, 12, 28, 29, 22, 4, 11] = true := by decide
theorem neck_35 : neckOK 35 [1, 34, 6, 20, 15, 11, 29, 28, 23, 12, 14, 21, 30, 27, 13, 22, 35, 16, 24, 33, 2, 10, 5, 7, 19, 3, 32, 25, 26, 31, 9, 17, 18, 8, 4] = true := by decide
theorem neck_36 : neckOK 36 [1, 11, 29, 28, 12, 14, 26, 25, 15, 20, 31, 9, 6, 34, 23, 17, 18, 22, 13, 27, 8, 32, 3, 19, 7, 33, 24, 2, 10, 16, 35, 5, 30, 21, 36, 4] = true := by decide
theorem neck_37 : neckOK 37 [1, 11, 29, 28, 12, 23, 34, 6, 16, 35, 22, 13, 27, 24, 33, 18, 17, 9, 26, 31, 4, 36, 15, 20, 37, 14, 8, 7, 19, 3, 32, 25, 10, 2, 5, 30, 21] = true := by decide
theorem neck_38 : neckOK 38 [1, 11, 29, 28, 12, 23, 34, 6, 16, 35, 22, 13, 27, 24, 33, 18, 17, 9, 26, 31, 4, 36, 15, 20, 37, 14, 8, 7, 5, 21, 30, 10, 2, 3, 19, 38, 32, 25] = true := by decide
theorem neck_39 : neckOK 39 [1, 11, 29, 28, 23, 34, 6, 16, 35, 22, 13, 27, 24, 33, 37, 20, 15, 36, 4, 18, 17, 9, 31, 26, 25, 10, 30, 5, 2, 3, 12, 39, 38, 32, 8, 7, 19, 21, 14] = true := by decide
theorem neck_40 : neckOK 40 [1, 25, 26, 14, 21, 36, 15, 11, 29, 28, 7, 8, 27, 24, 33, 37, 40, 30, 5, 35, 16, 10, 12, 23, 34, 6, 20, 2, 13, 22, 18, 17, 9, 31, 4, 3, 19, 32, 38, 39] = true := by decide
theorem neck_41 : neckOK 41 [1, 25, 26, 14, 21, 30, 27, 8, 32, 19, 38, 13, 9, 31, 39, 12, 28, 7, 15, 20, 6, 29, 11, 40, 37, 3, 23, 34, 17, 5, 35, 22, 18, 33, 2, 24, 16, 10, 41, 36, 4] = true := by decide
theorem neck_42 : neckOK 42 [1, 25, 26, 14, 21, 30, 27, 8, 32, 19, 38, 13, 22, 35, 42, 9, 31, 39, 18, 4, 36, 15, 7, 5, 17, 34, 6, 20, 2, 33, 24, 16, 10, 41, 29, 28, 12, 23, 3, 37, 40, 11] = true := by decide
theorem neck_43 : neckOK 43 [1, 25, 26, 31, 39, 38, 32, 19, 21, 14, 43, 8, 27, 13, 9, 42, 35, 22, 18, 4, 36, 15, 7, 28, 12, 3, 23, 34, 17, 5, 30, 40, 11, 29, 41, 10, 16, 24, 2, 33, 37, 20, 6] = true := by decide
theorem neck_44 : neckOK 44 [1, 25, 26, 44, 13, 22, 35, 42, 9, 31, 39, 38, 32, 19, 16, 6, 20, 15, 7, 28, 29, 41, 36, 21, 5, 10, 30, 27, 24, 2, 33, 18, 4, 11, 40, 17, 23, 12, 3, 37, 14, 8, 43, 34] = true := by decide
theorem neck_45 : neckOK 45 [1, 39, 31, 20, 37, 40, 11, 15, 42, 35, 22, 29, 28, 23, 12, 45, 6, 34, 17, 9, 26, 25, 32, 3, 4, 18, 8, 14, 43, 27, 13, 38, 19, 7, 44, 33, 24, 2, 5, 30, 10, 16, 41, 36, 21] = true := by decide
theorem neck_46 : neckOK 46 [1, 39, 38, 13, 44, 26, 25, 45, 32, 19, 21, 14, 43, 27, 8, 7, 15, 36, 34, 6, 20, 31, 9, 42, 28, 12, 23, 3, 37, 33, 2, 24, 46, 11, 29, 41, 16, 10, 30, 40, 17, 5, 35, 22, 18, 4] = true := by decide
theorem neck_47 : neckOK 47 [1, 39, 38, 13, 44, 26, 25, 32, 45, 47, 23, 12, 28, 42, 35, 22, 29, 41, 10, 16, 6, 9, 31, 20, 15, 36, 34, 17, 18, 4, 3, 19, 7, 8, 43, 14, 21, 5, 2, 33, 37, 40, 30, 27, 24, 46, 11] = true := by decide
theorem neck_48 : neckOK 48 [1, 39, 38, 13, 27, 43, 34, 36, 41, 16, 35, 42, 15, 20, 6, 29, 22, 48, 44, 26, 9, 31, 46, 11, 24, 2, 33, 18, 4, 8, 7, 28, 23, 17, 40, 37, 14, 12, 3, 19, 21, 5, 30, 10, 47, 45, 32, 25] = true := by decide
theorem neck_49 : neckOK 49 [1, 39, 38, 13, 27, 43, 34, 36, 41, 16, 35, 42, 15, 20, 6, 29, 22, 48, 44, 26, 9, 31, 46, 11, 24, 33, 18, 4, 8, 7, 19, 32, 25, 45, 47, 10, 2, 49, 28, 12, 3, 23, 17, 5, 21, 30, 40, 37, 14] = true := by decide
theorem neck_50 : neckOK 50 [1, 39, 38, 13, 44, 26, 25, 32, 45, 47, 23, 12, 14, 37, 40, 17, 34, 43, 27, 30, 10, 41, 36, 21, 19, 16, 6, 9, 3, 48, 29, 22, 35, 5, 46, 31, 4, 11, 24, 2, 20, 15, 42, 28, 49, 8, 18, 33, 7, 50] = true := by decide
theorem neck_51 : neckOK 51 [1, 39, 38, 13, 44, 48, 22, 35, 42, 50, 27, 43, 34, 36, 15, 20, 31, 46, 11, 24, 16, 41, 29, 6, 9, 26, 51, 19, 7, 28, 49, 21, 14, 8, 4, 18, 33, 37, 40, 17, 5, 2, 3, 23, 12, 10, 30, 47, 45, 32, 25] = true := by decide
theorem neck_52 : neckOK 52 [1, 39, 38, 13, 44, 26, 31, 46, 11, 24, 27, 50, 20, 15, 42, 35, 16, 41, 36, 34, 43, 14, 37, 33, 2, 49, 51, 6, 9, 17, 40, 30, 21, 5, 7, 19, 32, 8, 18, 52, 25, 10, 47, 45, 12, 23, 28, 29, 22, 48, 3, 4] = true := by decide
theorem neck_53 : neckOK 53 [1, 50, 42, 35, 16, 41, 36, 15, 20, 37, 40, 11, 46, 24, 27, 30, 21, 14, 43, 34, 6, 29, 22, 13, 38, 19, 51, 49, 28, 7, 8, 32, 45, 25, 26, 44, 33, 2, 5, 10, 12, 23, 47, 53, 17, 9, 3, 48, 52, 18, 4, 31, 39] = true := by decide
theorem neck_54 : neckOK 54 [1, 50, 42, 35, 22, 13, 27, 43, 34, 36, 15, 20, 37, 14, 21, 30, 40, 11, 29, 41, 51, 6, 16, 19, 38, 54, 46, 24, 33, 44, 7, 28, 49, 2, 5, 10, 12, 23, 17, 53, 39, 18, 8, 32, 45, 47, 4, 31, 26, 9, 3, 48, 52, 25] = true := by decide
theorem neck_55 : neckOK 55 [1, 50, 42, 35, 16, 41, 36, 34, 43, 27, 13, 44, 26, 51, 6, 9, 31, 20, 15, 25, 45, 55, 22, 29, 48, 52, 40, 11, 46, 24, 33, 37, 14, 21, 30, 5, 7, 19, 32, 8, 49, 28, 12, 10, 2, 38, 39, 18, 17, 53, 47, 23, 54, 3, 4] = true := by decide
theorem neck_56 : neckOK 56 [1, 50, 42, 35, 16, 41, 51, 6, 20, 15, 36, 34, 43, 27, 13, 9, 26, 31, 39, 38, 54, 46, 11, 24, 53, 17, 40, 30, 47, 23, 28, 29, 22, 4, 18, 52, 48, 44, 56, 14, 8, 49, 21, 5, 7, 19, 32, 3, 12, 10, 2, 33, 37, 55, 45, 25] = true := by decide
theorem neck_57 : neckOK 57 [1, 50, 42, 35, 57, 20, 15, 55, 37, 40, 11, 46, 31, 39, 53, 24, 27, 30, 47, 45, 25, 52, 5, 10, 12, 28, 7, 33, 2, 13, 38, 32, 19, 16, 54, 23, 3, 4, 18, 17, 9, 6, 34, 36, 41, 29, 22, 48, 44, 26, 51, 49, 8, 43, 14, 21, 56] = true := by decide
theorem neck_58 : neckOK 58 [1, 50, 27, 30, 40, 52, 25, 26, 51, 41, 10, 47, 45, 32, 38, 39, 53, 17, 18, 8, 43, 49, 21, 14, 56, 36, 34, 58, 12, 23, 28, 42, 15, 55, 37, 20, 57, 35, 5, 7, 19, 16, 6, 29, 11, 24, 33, 2, 3, 54, 46, 31, 9, 13, 44, 48, 22, 4] = true := by decide
theorem neck_59 : neckOK 59 [1, 50, 27, 30, 40, 52, 25, 26, 51, 41, 59, 58, 42, 35, 57, 43, 34, 36, 56, 14, 21, 49, 8, 32, 19, 16, 6, 45, 47, 10, 5, 7, 15, 20, 37, 55, 2, 33, 44, 13, 38, 54, 46, 24, 11, 29, 28, 12, 23, 3, 48, 9, 31, 39, 53, 17, 18, 22, 4] = true := by decide

theorem small_chains (N : ℕ) (h1 : 4 ≤ N) (h2 : N ≤ 59) : ∃ l, TriChain N l := by
  interval_cases N
  · exact ⟨_, triChain_of_chainOK chain_4⟩
  · exact ⟨_, triChain_of_chainOK chain_5⟩
  · exact ⟨_, triChain_of_chainOK chain_6⟩
  · exact ⟨_, triChain_of_chainOK chain_7⟩
  · exact ⟨_, triChain_of_chainOK chain_8⟩
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
  · exact ⟨_, triChain_of_chainOK chain_54⟩
  · exact ⟨_, triChain_of_chainOK chain_55⟩
  · exact ⟨_, triChain_of_chainOK chain_56⟩
  · exact ⟨_, triChain_of_chainOK chain_57⟩
  · exact ⟨_, triChain_of_chainOK chain_58⟩
  · exact ⟨_, triChain_of_chainOK chain_59⟩

theorem small_necklaces (N : ℕ) (h1 : 9 ≤ N) (h2 : N ≤ 59) : ∃ l, TriNecklace N l := by
  interval_cases N
  · exact ⟨_, triNecklace_of_neckOK neck_9⟩
  · exact ⟨_, triNecklace_of_neckOK neck_10⟩
  · exact ⟨_, triNecklace_of_neckOK neck_11⟩
  · exact ⟨_, triNecklace_of_neckOK neck_12⟩
  · exact ⟨_, triNecklace_of_neckOK neck_13⟩
  · exact ⟨_, triNecklace_of_neckOK neck_14⟩
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
  · exact ⟨_, triNecklace_of_neckOK neck_54⟩
  · exact ⟨_, triNecklace_of_neckOK neck_55⟩
  · exact ⟨_, triNecklace_of_neckOK neck_56⟩
  · exact ⟨_, triNecklace_of_neckOK neck_57⟩
  · exact ⟨_, triNecklace_of_neckOK neck_58⟩
  · exact ⟨_, triNecklace_of_neckOK neck_59⟩

end PentChains
