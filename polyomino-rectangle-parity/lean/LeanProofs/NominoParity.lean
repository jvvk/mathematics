import Mathlib

/-!
# Checkerboard parity for rectangles tiled by polyominoes (MO 378923)

Colour the cell `(x, y)` of `ℤ²` with `χ(x, y) = (-1)^(x + y)`; the imbalance of a finite set of cells is the sum of
`χ`. A placed tile is the image of a piece under one of the eight symmetries of the square grid followed by a
translation.

* `chi_place`: placing multiplies `χ` by `χ(t)`, so a placed tile has imbalance `± imb P` (`imb_place`).
* `imb_tiling`: a region tiled by placed pieces has imbalance `∑ χ(tᵢ) imb Pᵢ`.
* `imb_rect_even`: a rectangle with an even side has imbalance `0`.
* `no_rectangle`: if every piece has an even number of cells and `∑ |imb Pᵢ| ≡ 2 (mod 4)`, no rectangle is tiled.

The sums `∑ |imb P|` over all hole-free free `n`-ominoes (278 for `n = 8`, 4010 for `n = 10`, 13329078 for `n = 16`)
come from two independent enumerations; here they enter as the hypothesis of `no_rectangle`.
-/

namespace NominoParity

open Finset

abbrev Cell := ℤ × ℤ

/-- The checkerboard colour. -/
def chi (p : Cell) : ℤ := if (p.1 + p.2) % 2 = 0 then 1 else -1

/-- The eight symmetries of the grid: optional swap of coordinates, then optional sign changes. -/
def lin (k : Fin 8) (p : Cell) : Cell :=
  let q : Cell := if k.val / 4 = 1 then (p.2, p.1) else p
  ((if k.val % 2 = 1 then -q.1 else q.1), (if (k.val / 2) % 2 = 1 then -q.2 else q.2))

/-- Place a piece: a symmetry, then a translation. -/
def place (k : Fin 8) (t : Cell) (p : Cell) : Cell := lin k p + t

theorem chi_eq_neg_one_pow (p : Cell) : chi p = (-1) ^ (p.1 + p.2).natAbs := by
  unfold chi
  rcases Int.emod_two_eq_zero_or_one (p.1 + p.2) with h | h
  · rw [if_pos h, Even.neg_one_pow]
    exact (Int.natAbs_even.mpr (Int.even_iff.mpr h))
  · rw [if_neg (by omega), Odd.neg_one_pow]
    exact (Int.natAbs_odd.mpr (Int.odd_iff.mpr h))

theorem chi_of_mod {a b : Cell} (h : (a.1 + a.2) % 2 = (b.1 + b.2) % 2) : chi a = chi b := by
  unfold chi; rw [h]

theorem chi_add (p t : Cell) : chi (p + t) = chi p * chi t := by
  unfold chi
  simp only [Prod.fst_add, Prod.snd_add]
  rcases Int.emod_two_eq_zero_or_one (p.1 + p.2) with h | h <;>
  rcases Int.emod_two_eq_zero_or_one (t.1 + t.2) with h' | h' <;>
  · simp only [h, h']
    split_ifs <;> omega

theorem chi_lin (k : Fin 8) (p : Cell) : chi (lin k p) = chi p := by
  apply chi_of_mod
  unfold lin
  fin_cases k <;> simp <;> omega

theorem chi_sq (p : Cell) : chi p * chi p = 1 := by
  unfold chi; split_ifs <;> norm_num

theorem chi_cases (p : Cell) : chi p = 1 ∨ chi p = -1 := by
  unfold chi; split_ifs <;> simp

theorem chi_place (k : Fin 8) (t p : Cell) : chi (place k t p) = chi t * chi p := by
  rw [place, chi_add, chi_lin, mul_comm]

theorem lin_injective (k : Fin 8) : Function.Injective (lin k) := by
  intro p q h
  unfold lin at h
  fin_cases k <;> simp [Prod.ext_iff] at h ⊢ <;> omega

theorem place_injective (k : Fin 8) (t : Cell) : Function.Injective (place k t) := fun _ _ h =>
  lin_injective k (add_right_cancel h)

/-- Imbalance: black cells minus white cells. -/
def imb (S : Finset Cell) : ℤ := ∑ p ∈ S, chi p

theorem imb_place (k : Fin 8) (t : Cell) (S : Finset Cell) :
    imb (S.image (place k t)) = chi t * imb S := by
  rw [imb, sum_image fun _ _ _ _ h => place_injective k t h, imb, mul_sum]
  exact sum_congr rfl fun p _ => chi_place k t p

/-- Imbalance and size have the same parity. -/
theorem imb_mod_two (S : Finset Cell) : imb S % 2 = (S.card : ℤ) % 2 := by
  induction S using Finset.induction_on with
  | empty => simp [imb]
  | insert a S ha ih =>
    rw [imb, sum_insert ha, card_insert_of_notMem ha, ← imb]
    push_cast
    rcases chi_cases a with h | h <;> rw [h] <;> omega

/-! ### Tilings -/

/-- `R` is tiled by the pieces `P i`, placed by `k i` and `t i`. -/
def Tiles {N : ℕ} (R : Finset Cell) (P : Fin N → Finset Cell) (k : Fin N → Fin 8) (t : Fin N → Cell) : Prop :=
  (Set.PairwiseDisjoint ((univ : Finset (Fin N)) : Set (Fin N)) fun i => (P i).image (place (k i) (t i))) ∧
    univ.biUnion (fun i => (P i).image (place (k i) (t i))) = R

theorem imb_tiling {N : ℕ} {R : Finset Cell} {P : Fin N → Finset Cell} {k : Fin N → Fin 8} {t : Fin N → Cell}
    (h : Tiles R P k t) : imb R = ∑ i, chi (t i) * imb (P i) := by
  rw [← h.2, imb, sum_biUnion h.1]
  exact sum_congr rfl fun i _ => by rw [← imb, imb_place]

theorem card_tiling {N : ℕ} {R : Finset Cell} {P : Fin N → Finset Cell} {k : Fin N → Fin 8} {t : Fin N → Cell}
    (h : Tiles R P k t) : R.card = ∑ i, (P i).card := by
  rw [← h.2, card_biUnion h.1]
  exact sum_congr rfl fun i _ => card_image_of_injective _ (place_injective _ _)

/-! ### Rectangles -/

/-- The `a × b` rectangle `[0, a) × [0, b)`. -/
def rect (a b : ℕ) : Finset Cell :=
  ((range a).map Nat.castEmbedding) ×ˢ ((range b).map Nat.castEmbedding)

theorem card_rect (a b : ℕ) : (rect a b).card = a * b := by simp [rect]

theorem sum_alternating {f : ℕ → ℤ} (hf : ∀ i, f (2 * i + 1) = -f (2 * i)) (m : ℕ) :
    ∑ x ∈ range (2 * m), f x = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, hf]; ring

theorem chi_succ_fst (x y : ℤ) : chi (x + 1, y) = -chi (x, y) := by
  unfold chi; simp only
  rcases Int.emod_two_eq_zero_or_one (x + y) with h | h
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg (by omega)]; norm_num

theorem chi_succ_snd (x y : ℤ) : chi (x, y + 1) = -chi (x, y) := by
  unfold chi; simp only
  rcases Int.emod_two_eq_zero_or_one (x + y) with h | h
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg (by omega)]; norm_num

theorem imb_rect (a b : ℕ) : imb (rect a b) = ∑ x ∈ range a, ∑ y ∈ range b, chi ((x : ℤ), (y : ℤ)) := by
  rw [imb, rect, sum_product, sum_map]
  exact sum_congr rfl fun x _ => by rw [sum_map]; rfl

/-- A rectangle with an even side is balanced. -/
theorem imb_rect_even {a b : ℕ} (h : Even a ∨ Even b) : imb (rect a b) = 0 := by
  rw [imb_rect]
  rcases h with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [← two_mul]
    exact sum_alternating (f := fun x => ∑ y ∈ range b, chi ((x : ℤ), (y : ℤ)))
      (fun i => by rw [← sum_neg_distrib]; refine sum_congr rfl fun y _ => ?_; push_cast; exact chi_succ_fst _ _) m
  · rw [← two_mul]
    exact sum_eq_zero fun x _ => sum_alternating (f := fun y => chi ((x : ℤ), (y : ℤ)))
      (fun i => by push_cast; exact chi_succ_snd _ _) m

/-! ### The obstruction -/

/-- An even integer and its negative agree modulo 4. -/
theorem neg_mod_four {c : ℤ} (h : c % 2 = 0) : (-c) % 4 = c % 4 := by omega

/-- **The parity obstruction.** If every piece has an even number of cells and the imbalances satisfy
`∑ |imb Pᵢ| ≡ 2 (mod 4)`, then no rectangle is tiled by the placed pieces. -/
theorem no_rectangle {N : ℕ} (P : Fin N → Finset Cell) (heven : ∀ i, Even (P i).card)
    (hsum : (∑ i, (imb (P i)).natAbs) % 4 = 2) (a b : ℕ) (k : Fin N → Fin 8) (t : Fin N → Cell) :
    ¬ Tiles (rect a b) P k t := by
  intro h
  -- the area is even, so the rectangle has an even side and is balanced
  have hab : Even (a * b) := by
    rw [← card_rect, card_tiling h]
    exact Finset.even_sum _ fun i _ => heven i
  have h0 : imb (rect a b) = 0 := imb_rect_even (Nat.even_mul.mp hab)
  rw [imb_tiling h] at h0
  -- each signed imbalance is even, so it agrees mod 4 with its absolute value
  have hc : ∀ i, (chi (t i) * imb (P i)) % 4 = ((imb (P i)).natAbs : ℤ) % 4 := by
    intro i
    have he : imb (P i) % 2 = 0 := by
      rw [imb_mod_two]; obtain ⟨m, hm⟩ := heven i; rw [hm]; push_cast; omega
    rcases chi_cases (t i) with h1 | h1 <;> rcases Int.natAbs_eq (imb (P i)) with h2 | h2 <;>
      rw [h1] <;> omega
  have hmod : (∑ i, chi (t i) * imb (P i)) % 4 = (∑ i, ((imb (P i)).natAbs : ℤ)) % 4 := by
    rw [Finset.sum_int_mod univ 4, Finset.sum_int_mod univ 4 (fun i => ((imb (P i)).natAbs : ℤ))]
    exact congrArg (· % 4) (sum_congr rfl fun i _ => hc i)
  rw [h0, ← Nat.cast_sum] at hmod
  omega

/-- **`n = 8`, `10`, `16`.** For any family of pieces of size `n ∈ {8, 10, 16}` whose imbalances add up to `278`,
`4010` or `13329078` (the values for all hole-free free `n`-ominoes, from the enumerations), no rectangle is tiled. -/
theorem no_rectangle_8_10_16 {N n : ℕ} (hn : n = 8 ∨ n = 10 ∨ n = 16) (P : Fin N → Finset Cell)
    (hcard : ∀ i, (P i).card = n)
    (hsum : (n = 8 ∧ ∑ i, (imb (P i)).natAbs = 278) ∨ (n = 10 ∧ ∑ i, (imb (P i)).natAbs = 4010) ∨
      (n = 16 ∧ ∑ i, (imb (P i)).natAbs = 13329078))
    (a b : ℕ) (k : Fin N → Fin 8) (t : Fin N → Cell) : ¬ Tiles (rect a b) P k t := by
  refine no_rectangle P (fun i => ?_) ?_ a b k t
  · rw [hcard i]; rcases hn with rfl | rfl | rfl <;> decide
  · rcases hsum with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]

end NominoParity
