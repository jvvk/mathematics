import LeanProofs.ZeroSumGame.Dimension

/-!
# The game of order three: the basic criterion

Rows `A`, `B`, `C` of length 3; the Enemy selects one position of `A`, two of `B` and all of `C`.
The matrix is winning exactly when every entry `a` of `A` has at least two positions `j` of `B`
with `-a - b_j ∈ C`; equivalently, for every position `i` of `A` and every position `j₀` of `B`
(the one the Enemy leaves out) some `j ≠ j₀` and some `l` give `a_i + b_j + c_l = 0`.
-/

open Finset

namespace ZeroSumGame

/-- The square game of order 3. -/
abbrev N3 : Fin 3 → ℕ := fun _ => 3
abbrev k3 : Fin 3 → ℕ := fun i => i.val + 1

lemma sum_three (a : Array N3) (t : Transversal N3) :
    transversalSum a t = a ⟨0, t 0⟩ + a ⟨1, t 1⟩ + a ⟨2, t 2⟩ := by
  simp [transversalSum, Fin.sum_univ_three]

/-- A two-element subset of `Fin 3` is the complement of a point. -/
lemma card_two_eq_erase (S : Finset (Fin 3)) (h : S.card = 2) : ∃ j₀, S = univ.erase j₀ := by
  have hc : Sᶜ.card = 1 := by rw [card_compl, Fintype.card_fin, h]
  obtain ⟨j₀, hj₀⟩ := card_eq_one.mp hc
  refine ⟨j₀, ?_⟩
  ext j
  simp only [mem_erase, mem_univ, and_true]
  constructor
  · intro hj e
    have : j ∈ Sᶜ := by rw [hj₀, e]; exact mem_singleton_self _
    exact (mem_compl.mp this) hj
  · intro hj
    by_contra hn
    have : j ∈ Sᶜ := mem_compl.mpr hn
    rw [hj₀, mem_singleton] at this
    exact hj this

/-- **The order-three criterion.** -/
theorem order3_criterion (a : Array N3) :
    Winning k3 a ↔ ∀ i j₀ : Fin 3, ∃ j l : Fin 3, j ≠ j₀ ∧ a ⟨0, i⟩ + a ⟨1, j⟩ + a ⟨2, l⟩ = 0 := by
  constructor
  · intro hw i j₀
    let S : (r : Fin 3) → Finset (Fin (N3 r)) := fun r =>
      if r = 0 then {i} else if r = 1 then univ.erase j₀ else univ
    have hS : ∀ r, (S r).card = k3 r := by
      intro r
      fin_cases r <;> simp [S, card_erase_of_mem, k3, N3]
    obtain ⟨t, ht, hz⟩ := hw S hS
    have h0 : t 0 = i := by simpa [S] using ht 0
    have h1 : t 1 ≠ j₀ := by simpa [S] using ht 1
    refine ⟨t 1, t 2, h1, ?_⟩
    rw [sum_three, h0] at hz
    exact hz
  · intro hc S hS
    obtain ⟨i, hi⟩ := card_eq_one.mp (hS 0)
    obtain ⟨j₀, hj₀⟩ := card_two_eq_erase (S 1) (hS 1)
    have h2 : S 2 = univ := eq_univ_of_card _ (by rw [hS 2]; rfl)
    obtain ⟨j, l, hj, hz⟩ := hc i j₀
    refine ⟨fun r => if r = 0 then i else if r = 1 then j else l, ?_, ?_⟩
    · intro r
      fin_cases r
      · simp [hi]
      · simp [hj₀, hj]
      · simp [h2]
    · rw [sum_three]
      simpa using hz

end ZeroSumGame
