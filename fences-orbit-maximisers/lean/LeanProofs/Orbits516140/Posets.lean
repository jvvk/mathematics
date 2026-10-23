import LeanProofs.Orbits516140.Count
import LeanProofs.Orbits516140.Aut

/-!
# The explicit posets of the answer

All posets here have height at most one, so each is given by the list `D m` of the elements
below `m` (these are also its covers). Labels `a, b, c, …` are `0, 1, 2, …`.
-/

namespace Orbits516140

/-- A height-one poset on `Fin n`: `x < m` iff `x ∈ D m`. -/
def Bip (n : ℕ) (_D : Fin n → List (Fin n)) : Type := Fin n

namespace Bip

variable {n : ℕ} {D : Fin n → List (Fin n)}

/-- Height one: nothing below an element that is itself below something. -/
class Ok (D : Fin n → List (Fin n)) : Prop where
  ok : ∀ x m, x ∈ D m → D x = []

/-- The label of a point. -/
def mk (x : Fin n) : Bip n D := x

/-- The elements below `m`, as points of `Bip n D`. -/
def down (m : Bip n D) : List (Bip n D) := D m

instance : Fintype (Bip n D) := inferInstanceAs (Fintype (Fin n))
instance : DecidableEq (Bip n D) := inferInstanceAs (DecidableEq (Fin n))

theorem card_eq : Fintype.card (Bip n D) = n := Fintype.card_fin n

theorem two [h : Ok D] {a b c : Bip n D} (hab : a ∈ down b) (hbc : b ∈ down c) : False := by
  have h1 : down b = [] := h.ok b c hbc
  rw [h1] at hab; simp at hab

theorem irrefl [Ok D] {a : Bip n D} (ha : a ∈ down a) : False := two ha ha

instance [Ok D] : PartialOrder (Bip n D) where
  le a b := a = b ∨ a ∈ down b
  lt a b := a ∈ down b
  le_refl a := Or.inl rfl
  le_trans a b c := by
    rintro (rfl | hab) (rfl | hbc)
    · exact Or.inl rfl
    · exact Or.inr hbc
    · exact Or.inr hab
    · exact (two hab hbc).elim
  lt_iff_le_not_ge a b := by
    constructor
    · intro hab
      refine ⟨Or.inr hab, ?_⟩
      rintro (rfl | hba)
      · exact irrefl hab
      · exact two hab hba
    · rintro ⟨rfl | hab, hba⟩
      · exact absurd (Or.inl rfl) hba
      · exact hab
  le_antisymm a b := by
    rintro (rfl | hab) (hba | hba)
    · rfl
    · rfl
    · exact hba.symm
    · exact (two hab hba).elim

instance [Ok D] : DecidableRel (α := Bip n D) (· < ·) :=
  fun a b => inferInstanceAs (Decidable (a ∈ down b))

instance [Ok D] : DecidableRel (α := Bip n D) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (a = b ∨ a ∈ down b))

instance [Ok D] : DecidableRel (α := Bip n D) (· ⋖ ·) :=
  fun a b => inferInstanceAs (Decidable (a < b ∧ ∀ c, a < c → ¬ c < b))

theorem lt_iff [Ok D] (x m : Bip n D) : x < m ↔ x ∈ down m := Iff.rfl

/-- `e(Bip n D)` by the certified counter. -/
theorem card_linExt [Ok D] : Nat.card (LinExt (Bip n D)) = cnt (down (D := D)) n Finset.univ := by
  rw [card_linExt_eq_cnt (α := Bip n D) down lt_iff, card_eq]

end Bip


/-- The identity candidate table. -/
def Tid {n : ℕ} {D : Fin n → List (Fin n)} (x : Bip n D) : Finset (Bip n D) := {x}

/-! ## `Q`: the fence `a<b>c<d>e<f` with `g<d` -/

/-- Down-sets of `Q`. -/
def DQ : Fin 7 → List (Fin 7) := ![[], [0, 2], [], [2, 4, 6], [], [4], []]
instance : Bip.Ok DQ := ⟨by decide⟩
/-- `Q`, seven points. -/
abbrev Q := Bip 7 DQ

/-- The cover relations of `Q` are exactly those of the answer (and its Sage line). -/
theorem Q_covBy : ∀ x y : Fin 7, (Bip.mk x : Q) ⋖ Bip.mk y ↔
    (x, y) ∈ [((0 : Fin 7), (1 : Fin 7)), (2, 1), (2, 3), (4, 3), (4, 5), (6, 3)] := by
  decide

theorem e_Q : Nat.card (LinExt Q) = 298 := by
  rw [Bip.card_linExt]; decide

theorem aut_Q : Nat.card (Q ≃o Q) = 1 := by
  rw [card_aut_eq Tid (by decide)]; decide

/-- `Q` is not self-dual, so `Q` and `Q*` are different maximisers' components. -/
theorem Q_not_selfDual : IsEmpty (Q ≃o Qᵒᵈ) :=
  isEmpty_iso_dual (Bip.mk 3 : Q) (by decide)

/-! ## `Q + •` (eight points): the maximiser at `n = 8` -/

/-- Down-sets of `Q + •`; the extra point is `7`. -/
def DQ1 : Fin 8 → List (Fin 8) := ![[], [0, 2], [], [2, 4, 6], [], [4], [], []]
instance : Bip.Ok DQ1 := ⟨by decide⟩
/-- `Q + •`. -/
abbrev Q1 := Bip 8 DQ1

theorem e_Q1 : Nat.card (LinExt Q1) = 2384 := by
  rw [Bip.card_linExt]; decide

theorem aut_Q1 : Nat.card (Q1 ≃o Q1) = 1 := by
  rw [card_aut_eq Tid (by decide)]; decide

theorem orbits_Q1 : orbitCount Q1 = 2384 := by
  rw [orbitCount_eq_div, e_Q1, aut_Q1]

/-- `Q + •` is not a disjoint union of fences: `d` is comparable with `c`, `e` and `g`. -/
theorem Q1_not_fenceUnion : ¬ IsFenceUnion Q1 :=
  not_isFenceUnion (x := (Bip.mk 3 : Q1)) (by decide)

theorem Q1_not_selfDual : IsEmpty (Q1 ≃o Q1ᵒᵈ) :=
  isEmpty_iso_dual (Bip.mk 3 : Q1) (by decide)

/-! ## `Z₂ + Z₄ + 2•`: the best disjoint union of fences at `n = 8` -/

/-- Down-sets of `Z₂ + Z₄ + 2•`: `0 < 1`, `2 < 3 > 4 < 5`, points `6`, `7`. -/
def DF : Fin 8 → List (Fin 8) := ![[], [0], [], [2, 4], [], [4], [], []]
instance : Bip.Ok DF := ⟨by decide⟩
/-- `Z₂ + Z₄ + 2•`. -/
abbrev F := Bip 8 DF

/-- Candidate table for `F`: everything fixed except the two isolated points. -/
def TF (x : F) : Finset F :=
  if x = Bip.mk 6 ∨ x = Bip.mk 7 then {Bip.mk 6, Bip.mk 7} else {x}

theorem e_F : Nat.card (LinExt F) = 4200 := by
  rw [Bip.card_linExt]; decide +kernel

theorem aut_F : Nat.card (F ≃o F) = 2 := by
  rw [card_aut_eq TF (by decide)]; decide

theorem orbits_F : orbitCount F = 2100 := by
  rw [orbitCount_eq_div, e_F, aut_F]

theorem F_isFenceUnion : IsFenceUnion F :=
  ⟨Equiv.refl _, by decide⟩

/-- The counterexample at `n = 8`: `f(Q + •) = 2384 > 2100 = f(Z₂ + Z₄ + 2•)`. -/
theorem orbits_F_lt_Q1 : orbitCount F < orbitCount Q1 := by
  rw [orbits_F, orbits_Q1]; norm_num

/-! ## `R`: the fence `a<b>c<d>e<f` with `g<d` and `h>c` -/

/-- Down-sets of `R`; `h = 7` lies above `c = 2`. -/
def DR : Fin 8 → List (Fin 8) := ![[], [0, 2], [], [2, 4, 6], [], [4], [], [2]]
instance : Bip.Ok DR := ⟨by decide⟩
/-- `R`. -/
abbrev R := Bip 8 DR

theorem R_covBy : ∀ x y : Fin 8, (Bip.mk x : R) ⋖ Bip.mk y ↔
    (x, y) ∈ [((0 : Fin 8), (1 : Fin 8)), (2, 1), (2, 3), (4, 3), (4, 5), (6, 3), (2, 7)] := by
  decide

theorem e_R : Nat.card (LinExt R) = 1613 := by
  rw [Bip.card_linExt]; decide

theorem aut_R : Nat.card (R ≃o R) = 1 := by
  rw [card_aut_eq Tid (by decide)]; decide

/-- The duality `a ↔ f, b ↔ e, c ↔ d, g ↔ h`. -/
def pR : R → R := fun x => Bip.mk (![5, 4, 3, 2, 1, 0, 7, 6] (x : Fin 8))

theorem pR_pR : ∀ x, pR (pR x) = x := by decide

theorem pR_le : ∀ a b : R, pR b ≤ pR a ↔ a ≤ b := by decide

/-- `R` is self-dual. -/
def R_selfDual : R ≃o Rᵒᵈ where
  toFun x := OrderDual.toDual (pR x)
  invFun y := pR (OrderDual.ofDual y)
  left_inv := pR_pR
  right_inv := pR_pR
  map_rel_iff' {a b} := pR_le a b

/-! ## Small checks: `E₄`, `E₆`, and the maximiser `Z₂ + Z₄ + •` at `n = 7` -/

/-- `Z₄`: `0 < 1 > 2 < 3`. -/
def DZ4 : Fin 4 → List (Fin 4) := ![[], [0, 2], [], [2]]
instance : Bip.Ok DZ4 := ⟨by decide⟩

/-- `Z₆`: `0 < 1 > 2 < 3 > 4 < 5`. -/
def DZ6 : Fin 6 → List (Fin 6) := ![[], [0, 2], [], [2, 4], [], [4]]
instance : Bip.Ok DZ6 := ⟨by decide⟩

theorem e_Z4 : Nat.card (LinExt (Bip 4 DZ4)) = 5 := by
  rw [Bip.card_linExt]; decide

theorem e_Z6 : Nat.card (LinExt (Bip 6 DZ6)) = 61 := by
  rw [Bip.card_linExt]; decide

/-- `Z₂ + Z₄ + •`. -/
def DF7 : Fin 7 → List (Fin 7) := ![[], [0], [], [2, 4], [], [4], []]
instance : Bip.Ok DF7 := ⟨by decide⟩

theorem orbits_F7 : orbitCount (Bip 7 DF7) = 525 := by
  rw [orbitCount_eq_div, Bip.card_linExt, card_aut_eq Tid (by decide)]; decide

/-! ## The answer's arithmetic

With the standard product formula `e(P + P') = C(|P|+|P'|, |P|) e(P) e(P')` (cited, not
formalised here) and trivial automorphism groups, the table entries at `n = 10, 11` and the
lower bound at `n = 7, 9` reduce to these identities. -/

theorem arith_n8 : 8 * 298 = 2384 := by norm_num
theorem arith_n10 : Nat.factorial 10 / (Nat.factorial 7 * Nat.factorial 2) * 298 = 107280 := by
  decide
theorem arith_n11 : Nat.factorial 11 / (Nat.factorial 8 * Nat.factorial 2) * 1613 = 798435 := by
  decide
theorem arith_bound7 : 7 * 6 * 5 / 2 * 5 = 525 := by norm_num
theorem arith_bound9 : 9 * 8 * 7 / 2 * 61 = 15372 := by norm_num

end Orbits516140
