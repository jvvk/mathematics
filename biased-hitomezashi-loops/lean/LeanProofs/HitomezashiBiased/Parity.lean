import Mathlib

/-!
# Biased hitomezashi loops: labels seen from a loop

Grid lines carry labels in `ZMod 2`: the vertical line `x = i` has label `ε i`, the horizontal line `y = j`
has label `η j`. The unit segment from `(i, j)` to `(i, j+1)` is a stitch iff `j = ε i (mod 2)`; the unit
segment from `(i, j)` to `(i+1, j)` is a stitch iff `i = η j (mod 2)` (Defant and Kravitz's convention).

Every lattice point meets exactly one vertical and one horizontal stitch, so any walk along stitches
alternates vertical and horizontal steps. For such a walk, starting with a vertical step at `z 0`, put
`σ = x₀ + y₀ (mod 2)`. Then the label of every vertical line the walk uses is
`ε i = σ + i + [the step goes down]`, and the label of every horizontal line it uses is
`η j = σ + 1 + j + [the step goes left]`. In particular all vertical steps of a loop on one line point the
same way (Defant and Kravitz, Lemma 2.3), and the labels of the lines met by a loop are fixed by `σ`, the
line index and the direction of travel (Lemma 2 of the paper).
-/

namespace HitomezashiBiased

/-- A vertical stitch step from `a` to `b`, up or down, along a stitch of the pattern. -/
def VStep (ε : ℤ → ZMod 2) (a b : ℤ × ℤ) : Prop :=
  b.1 = a.1 ∧ ((b.2 = a.2 + 1 ∧ (a.2 : ZMod 2) = ε a.1) ∨ (b.2 = a.2 - 1 ∧ ((a.2 - 1 : ℤ) : ZMod 2) = ε a.1))

/-- A horizontal stitch step from `a` to `b`, right or left, along a stitch of the pattern. -/
def HStep (η : ℤ → ZMod 2) (a b : ℤ × ℤ) : Prop :=
  b.2 = a.2 ∧ ((b.1 = a.1 + 1 ∧ (a.1 : ZMod 2) = η a.2) ∨ (b.1 = a.1 - 1 ∧ ((a.1 - 1 : ℤ) : ZMod 2) = η a.2))

/-- An alternating stitch walk of length `L`: even-numbered steps vertical, odd-numbered horizontal. -/
def AltWalk (ε η : ℤ → ZMod 2) (z : ℕ → ℤ × ℤ) (L : ℕ) : Prop :=
  ∀ t < L, (Even t → VStep ε (z t) (z (t + 1))) ∧ (Odd t → HStep η (z t) (z (t + 1)))

private lemma two_eq_zero : (2 : ZMod 2) = 0 := by decide

/-- Every step changes `x + y` by `±1`, so `x + y` at time `t` has parity `σ + t`. -/
theorem parity_along (ε η : ℤ → ZMod 2) (z : ℕ → ℤ × ℤ) (L : ℕ) (hz : AltWalk ε η z L) :
    ∀ t ≤ L, (((z t).1 + (z t).2 : ℤ) : ZMod 2) = (((z 0).1 + (z 0).2 : ℤ) : ZMod 2) + t := by
  intro t ht
  induction t with
  | zero => simp
  | succ t ih =>
    have ih := ih (by omega)
    obtain ⟨hv, hh⟩ := hz t (by omega)
    have step : (((z (t + 1)).1 + (z (t + 1)).2 : ℤ) : ZMod 2) = (((z t).1 + (z t).2 : ℤ) : ZMod 2) + 1 := by
      rcases Nat.even_or_odd t with he | ho
      · obtain ⟨h1, (⟨h2, -⟩ | ⟨h2, -⟩)⟩ := hv he <;> rw [h1, h2] <;> push_cast
        · ring
        · linear_combination (-1 : ZMod 2) * two_eq_zero
      · obtain ⟨h1, (⟨h2, -⟩ | ⟨h2, -⟩)⟩ := hh ho <;> rw [h1, h2] <;> push_cast
        · ring
        · linear_combination (-1 : ZMod 2) * two_eq_zero
    rw [step, ih]
    push_cast; ring

/-- **Vertical labels along a loop.** At a vertical step from `(i, j)`, `ε i = σ + i + [down]`. -/
theorem vertical_label (ε η : ℤ → ZMod 2) (z : ℕ → ℤ × ℤ) (L : ℕ) (hz : AltWalk ε η z L)
    (t : ℕ) (ht : t < L) (he : Even t) :
    let σ : ZMod 2 := (((z 0).1 + (z 0).2 : ℤ) : ZMod 2)
    ((z (t + 1)).2 = (z t).2 + 1 ∧ ε (z t).1 = σ + (z t).1) ∨
    ((z (t + 1)).2 = (z t).2 - 1 ∧ ε (z t).1 = σ + (z t).1 + 1) := by
  intro σ
  have hp := parity_along ε η z L hz t ht.le
  obtain ⟨-, h⟩ := (hz t ht).1 he
  have hk : (t : ZMod 2) = 0 := by
    obtain ⟨k, rfl⟩ := he; push_cast; rw [← two_mul, two_eq_zero, zero_mul]
  rw [hk, add_zero] at hp
  have hσ : σ = (((z t).1 + (z t).2 : ℤ) : ZMod 2) := hp.symm
  rcases h with ⟨h2, hε⟩ | ⟨h2, hε⟩
  · left
    refine ⟨h2, ?_⟩
    rw [← hε, hσ]
    push_cast
    linear_combination (-((z t).1 : ZMod 2)) * two_eq_zero
  · right
    refine ⟨h2, ?_⟩
    rw [← hε, hσ]
    push_cast
    linear_combination (-((z t).1 : ZMod 2) - 1) * two_eq_zero

/-- **Horizontal labels along a loop.** At a horizontal step from `(i, j)`,
`η j = σ + 1 + j + [left]`. -/
theorem horizontal_label (ε η : ℤ → ZMod 2) (z : ℕ → ℤ × ℤ) (L : ℕ) (hz : AltWalk ε η z L)
    (t : ℕ) (ht : t < L) (ho : Odd t) :
    let σ : ZMod 2 := (((z 0).1 + (z 0).2 : ℤ) : ZMod 2)
    ((z (t + 1)).1 = (z t).1 + 1 ∧ η (z t).2 = σ + 1 + (z t).2) ∨
    ((z (t + 1)).1 = (z t).1 - 1 ∧ η (z t).2 = σ + 1 + (z t).2 + 1) := by
  intro σ
  have hp := parity_along ε η z L hz t ht.le
  obtain ⟨-, h⟩ := (hz t ht).2 ho
  have hk : (t : ZMod 2) = 1 := by
    obtain ⟨k, rfl⟩ := ho; push_cast; rw [two_eq_zero, zero_mul, zero_add]
  rw [hk] at hp
  have hσ : σ = (((z t).1 + (z t).2 : ℤ) : ZMod 2) - 1 := by rw [hp]; ring
  rcases h with ⟨h2, hη⟩ | ⟨h2, hη⟩
  · left
    refine ⟨h2, ?_⟩
    rw [← hη, hσ]
    push_cast
    linear_combination (-((z t).2 : ZMod 2)) * two_eq_zero
  · right
    refine ⟨h2, ?_⟩
    rw [← hη, hσ]
    push_cast
    linear_combination (-((z t).2 : ZMod 2) - 1) * two_eq_zero

end HitomezashiBiased
