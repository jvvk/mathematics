import Mathlib.Tactic

/-!
# Acute tetrahedron (MO 498296): the finite counting core

Signs `σ : Fin 4 → Bool` are the 16 flip variants of four unit vectors `A 0, …, A 3`
(`σ` and its complement give the same tetrahedron up to a central reflection).
An *edge* `(l, b₁, b₂)` is a signed sum over the face opposite `l`:
`A f₀ + s(b₁) A f₁ + s(b₂) A f₂`, where `f₀ < f₁ < f₂` are the other three indices.
It is *incident* to `σ` when its signs agree with `σ` on the face up to a global sign.

`c : Fin 4 → Option (Bool × Bool)` records, for each face, which (at most one) signed sum is short.
This file proves, by a kernel-checked finite computation, that under the three combinatorial
constraints coming from geometry (some edge short; not all four edges at one sign vector short; two disjoint
short edges are joined by a third), the number of signs covering all short edges satisfies
`nCover + 4·#short = 8 + Σ_σ C(deg σ, 2)`.
-/

namespace AcuteTetra

abbrev Sign := Fin 4 → Bool
abbrev Edge := Fin 4 × Bool × Bool

/-- The face opposite `l`, listed in increasing order. -/
def face (l : Fin 4) (t : Fin 3) : Fin 4 :=
  if t.val < l.val then ⟨t.val, by omega⟩ else ⟨t.val + 1, by omega⟩

/-- Edge `e` is incident to the sign vector `σ`. -/
def inc (e : Edge) (σ : Sign) : Bool :=
  let f := face e.1
  ((σ (f 1) == σ (f 0)) == e.2.1) && ((σ (f 2) == σ (f 0)) == e.2.2)

/-- The edge in direction `l` incident to `σ`. -/
def incP (σ : Sign) (l : Fin 4) : Bool × Bool :=
  (σ (face l 1) == σ (face l 0), σ (face l 2) == σ (face l 0))

def allSigns : List Sign :=
  (List.finRange 16).map fun n i => n.val.testBit i.val

def shortList (c : Fin 4 → Option (Bool × Bool)) : List Edge :=
  (List.finRange 4).filterMap fun l => (c l).map fun p => (l, p)

def deg (c : Fin 4 → Option (Bool × Bool)) (σ : Sign) : ℕ :=
  ((shortList c).filter fun e => inc e σ).length

def covers (c : Fin 4 → Option (Bool × Bool)) (σ : Sign) : Bool :=
  (shortList c).all fun e => inc e σ

def disjointE (e f : Edge) : Bool := allSigns.all fun σ => !(inc e σ && inc f σ)

def joined (c : Fin 4 → Option (Bool × Bool)) (e f : Edge) : Bool :=
  (shortList c).any fun g => allSigns.any (fun σ => inc g σ && inc e σ) &&
    allSigns.any (fun σ => inc g σ && inc f σ)

def constraints (c : Fin 4 → Option (Bool × Bool)) : Bool :=
  !(shortList c).isEmpty &&
  allSigns.all (fun σ => !((List.finRange 4).all fun l => c l == some (incP σ l))) &&
  (shortList c).all fun e => (shortList c).all fun f => !disjointE e f || joined c e f

def identity (c : Fin 4 → Option (Bool × Bool)) : Bool :=
  (allSigns.filter (covers c)).length + 4 * (shortList c).length ==
    8 + (allSigns.map fun σ => (deg c σ).choose 2).sum

theorem comb : ∀ c : Fin 4 → Option (Bool × Bool), constraints c = true → identity c = true := by
  decide +kernel

end AcuteTetra
