/-
  Stanley, MathOverflow 486548: descent sets of a permutation and of its inverse.

  Part A. An abstract descent lemma. A function `w` on `{0, …, n-1}` with a set `P` of marked
  positions, a pivot `p ∈ P` with `w p = v`, marked values decreasing, unmarked values increasing,
  marked values above `v` exactly before the pivot and unmarked values below `v` exactly before
  the pivot (`Good`), has descent set `{i | (i ∈ P ∧ i < p) ∨ (i + 1 ∈ P ∧ p ≤ i)}`.
  Positions and descents are 0-indexed: `i` is a descent when `w (i+1) < w i`.
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

namespace Stanley

/-- Descent set of `w` on positions `0, …, n-1`. -/
def desc (n : ℕ) (w : ℕ → ℕ) : Finset ℕ :=
  (Finset.range (n - 1)).filter (fun i => w (i + 1) < w i)

/-- The order conditions of the pivot construction. -/
structure Good (n : ℕ) (w : ℕ → ℕ) (P : Finset ℕ) (p v : ℕ) : Prop where
  pP : p ∈ P
  wp : w p = v
  A : ∀ q ∈ P, ∀ q' ∈ P, q < q' → w q' < w q
  B : ∀ q < n, ∀ q' < n, q ∉ P → q' ∉ P → q < q' → w q < w q'
  C : ∀ q ∈ P, (q < p ↔ v < w q)
  D : ∀ q < n, q ∉ P → (q < p ↔ w q < v)

theorem desc_eq {n : ℕ} {w : ℕ → ℕ} {P : Finset ℕ} {p v : ℕ} (h : Good n w P p v) :
    desc n w = (Finset.range (n - 1)).filter
      (fun i => (i ∈ P ∧ i < p) ∨ (i + 1 ∈ P ∧ p ≤ i)) := by
  ext i
  simp only [desc, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, hd⟩
    refine ⟨hi, ?_⟩
    by_cases hP : i ∈ P <;> by_cases hP1 : i + 1 ∈ P
    · rcases lt_or_ge i p with hlt | hge
      · exact Or.inl ⟨hP, hlt⟩
      · exact Or.inr ⟨hP1, hge⟩
    · rcases lt_or_ge i p with hlt | hge
      · exact Or.inl ⟨hP, hlt⟩
      · exfalso
        have h1 : w i ≤ v := by
          rcases eq_or_lt_of_le hge with heq | hgt
          · rw [← heq, h.wp]
          · have := (h.C i hP).not.mp (by omega)
            omega
        have h2 : ¬ w (i + 1) < v := (h.D (i + 1) (by omega) hP1).not.mp (by omega)
        omega
    · rcases lt_or_ge i p with hlt | hge
      · exfalso
        have h1 : w i < v := (h.D i (by omega) hP).mp hlt
        have h2 : v ≤ w (i + 1) := by
          rcases eq_or_lt_of_le (show i + 1 ≤ p by omega) with heq | hlt'
          · rw [heq, h.wp]
          · exact le_of_lt ((h.C (i + 1) hP1).mp hlt')
        omega
      · exact Or.inr ⟨hP1, hge⟩
    · exact absurd hd (not_lt.mpr (le_of_lt (h.B i (by omega) (i + 1) (by omega) hP hP1 (by omega))))
  · rintro ⟨hi, hc⟩
    refine ⟨hi, ?_⟩
    by_cases hP : i ∈ P <;> by_cases hP1 : i + 1 ∈ P
    · exact h.A i hP (i + 1) hP1 (by omega)
    · rcases hc with ⟨_, hlt⟩ | ⟨h1, _⟩
      · have hne : i + 1 ≠ p := fun e => hP1 (e ▸ h.pP)
        have h1 : v < w i := (h.C i hP).mp hlt
        have h2 : w (i + 1) < v := (h.D (i + 1) (by omega) hP1).mp (by omega)
        omega
      · exact absurd h1 hP1
    · rcases hc with ⟨h1, _⟩ | ⟨_, hge⟩
      · exact absurd h1 hP
      · have hne : i ≠ p := fun e => hP (e ▸ h.pP)
        have h1 : w (i + 1) < v := by
          rw [← h.wp]; exact h.A p h.pP (i + 1) hP1 (by omega)
        have h2 : ¬ w i < v := (h.D i (by omega) hP).not.mp (by omega)
        omega
    · rcases hc with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd h1 hP
      · exact absurd h1 hP1

/-- The inverse of a `Good` bijection is `Good`, with positions and values swapped. -/
theorem Good.inv {n : ℕ} {w u : ℕ → ℕ} {P : Finset ℕ} {p v : ℕ} (h : Good n w P p v)
    (hPn : ∀ q ∈ P, q < n) (hw : ∀ q < n, w q < n) (hu : ∀ x < n, u x < n)
    (huw : ∀ q < n, u (w q) = q) (hwu : ∀ x < n, w (u x) = x) :
    Good n u (P.image w) v p := by
  have hpn : p < n := hPn p h.pP
  -- membership of `w`-images in the image set
  have memV : ∀ x < n, x ∈ P.image w ↔ u x ∈ P := by
    intro x hx
    constructor
    · intro hm
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
      rw [huw q (hPn q hq)]; exact hq
    · intro hm
      exact Finset.mem_image.mpr ⟨u x, hm, hwu x hx⟩
  have hVn : ∀ x ∈ P.image w, x < n := by
    intro x hm
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
    exact hw q (hPn q hq)
  have hv : v < n := h.wp ▸ hw p hpn
  refine ⟨Finset.mem_image.mpr ⟨p, h.pP, h.wp⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.wp, huw p hpn]
  · intro x hx x' hx' hlt
    have hxn := hVn x hx; have hxn' := hVn x' hx'
    have hq := (memV x hxn).mp hx; have hq' := (memV x' hxn').mp hx'
    rcases lt_trichotomy (u x') (u x) with h1 | h1 | h1
    · exact h1
    · have := congrArg w h1; rw [hwu x hxn, hwu x' hxn'] at this; omega
    · have := h.A (u x) hq (u x') hq' h1; rw [hwu x hxn, hwu x' hxn'] at this; omega
  · intro x hx x' hx' hm hm' hlt
    have hq : u x ∉ P := fun c => hm ((memV x hx).mpr c)
    have hq' : u x' ∉ P := fun c => hm' ((memV x' hx').mpr c)
    rcases lt_trichotomy (u x) (u x') with h1 | h1 | h1
    · exact h1
    · have := congrArg w h1; rw [hwu x hx, hwu x' hx'] at this; omega
    · have := h.B (u x') (hu x' hx') (u x) (hu x hx) hq' hq h1
      rw [hwu x hx, hwu x' hx'] at this; omega
  · intro x hx
    have hxn := hVn x hx
    have hq := (memV x hxn).mp hx
    have key := h.C (u x) hq
    rw [hwu x hxn] at key
    constructor
    · intro hlt
      rcases lt_trichotomy (u x) p with h1 | h1 | h1
      · have := key.mp h1; omega
      · have := congrArg w h1; rw [hwu x hxn, h.wp] at this; omega
      · exact h1
    · intro hlt
      have hnot : ¬ v < x := fun c => (lt_irrefl _ (lt_trans (key.mpr c) hlt))
      have hne : x ≠ v := by
        intro e
        have := congrArg u e
        rw [← h.wp, huw p hpn] at this
        omega
      omega
  · intro x hx hm
    have hq : u x ∉ P := fun c => hm ((memV x hx).mpr c)
    have key := h.D (u x) (hu x hx) hq
    rw [hwu x hx] at key
    exact key.symm

end Stanley
