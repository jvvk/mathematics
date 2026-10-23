import LeanProofs.Orbits516140.Basic

/-!
# Automorphisms and isomorphism invariants

* `card_below_map`, `card_above_map`: order isomorphisms preserve the number of elements
  below and above a point.
* `refine`: one round of refinement of candidate images. If every automorphism maps `x` into
  `C x`, it maps `x` into `refine C x`.
* `card_aut_eq`: given a table `T` containing the refined candidate sets, `#Aut(α)` is the
  number of injective, order-reflecting maps `f` with `f x ∈ T x` for all `x` (a finite check).
* `IsFenceUnion`, `card_comp_le_two`: in a disjoint union of fences no element is comparable
  with more than two others.
* `isEmpty_iso_dual`: a poset with a point having `k` elements below and no point having `k`
  elements above is not self-dual.
-/

namespace Orbits516140

open Finset

section Below

variable {α : Type*} [Fintype α] [PartialOrder α] [DecidableRel (α := α) (· < ·)]

/-- The elements strictly below `x`. -/
def below (x : α) : Finset α := univ.filter (· < x)

/-- The elements strictly above `x`. -/
def above (x : α) : Finset α := univ.filter (x < ·)

variable {β : Type*} [Fintype β] [PartialOrder β] [DecidableRel (α := β) (· < ·)]

theorem card_below_map (φ : α ≃o β) (x : α) : (below (φ x)).card = (below x).card := by
  have : below (φ x) = (below x).map φ.toEquiv.toEmbedding := by
    ext y
    simp only [below, mem_filter, mem_univ, true_and, mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro h; exact ⟨φ.symm y, by simpa using (φ.symm.lt_iff_lt).2 h, by simp⟩
    · rintro ⟨z, hz, rfl⟩; exact φ.lt_iff_lt.2 hz
  rw [this, card_map]

theorem card_above_map (φ : α ≃o β) (x : α) : (above (φ x)).card = (above x).card := by
  have : above (φ x) = (above x).map φ.toEquiv.toEmbedding := by
    ext y
    simp only [above, mem_filter, mem_univ, true_and, mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro h; exact ⟨φ.symm y, by simpa using (φ.symm.lt_iff_lt).2 h, by simp⟩
    · rintro ⟨z, hz, rfl⟩; exact φ.lt_iff_lt.2 hz
  rw [this, card_map]

end Below

section Aut

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]
  [DecidableRel (α := α) (· < ·)] [DecidableRel (α := α) (· ≤ ·)]

/-- Candidate images by the numbers of elements below and above. -/
def sig (x : α) : Finset α :=
  univ.filter fun y => (below y).card = (below x).card ∧ (above y).card = (above x).card

/-- One round of refinement: `y` stays a candidate for `x` only if each point below (above) `x`
has a candidate below (above) `y`. -/
def refine (C : α → Finset α) (x : α) : Finset α :=
  (C x).filter fun y =>
    (∀ z, z < x → ∃ w ∈ C z, w < y) ∧ (∀ z, x < z → ∃ w ∈ C z, y < w)

omit [DecidableEq α] [DecidableRel (α := α) (· ≤ ·)] in
theorem mem_sig (φ : α ≃o α) (x : α) : φ x ∈ sig x := by
  simp [sig, card_below_map, card_above_map]

omit [DecidableEq α] [DecidableRel (α := α) (· ≤ ·)] in
theorem mem_refine (φ : α ≃o α) {C : α → Finset α} (h : ∀ x, φ x ∈ C x) (x : α) :
    φ x ∈ refine C x := by
  simp only [refine, mem_filter]
  exact ⟨h x, fun z hz => ⟨φ z, h z, φ.lt_iff_lt.2 hz⟩, fun z hz => ⟨φ z, h z, φ.lt_iff_lt.2 hz⟩⟩

/-- The maps checked by `card_aut_eq`. -/
def autCands (T : α → Finset α) : Finset (α → α) :=
  (Fintype.piFinset T).filter fun f => Function.Injective f ∧ ∀ a b, a ≤ b ↔ f a ≤ f b

/-- `#Aut(α)` equals the number of order-reflecting injections inside a candidate table that
contains one round of refinement of `sig`. -/
theorem card_aut_eq (T : α → Finset α) (hT : ∀ x, refine sig x ⊆ T x) :
    Nat.card (α ≃o α) = (autCands T).card := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.ofBijective
    (fun φ => ⟨(φ : α → α), ?_⟩) ⟨fun φ ψ h => ?_, fun ⟨f, hf⟩ => ?_⟩)
  · simp only [autCands, mem_filter, Fintype.mem_piFinset]
    exact ⟨fun x => hT x (mem_refine φ (mem_sig φ) x), φ.injective,
      fun a b => φ.le_iff_le.symm⟩
  · exact OrderIso.ext (congrArg Subtype.val h)
  · simp only [autCands, mem_filter] at hf
    obtain ⟨-, hinj, hle⟩ := hf
    have hbij : Function.Bijective f := Finite.injective_iff_bijective.1 hinj
    exact ⟨{ toEquiv := Equiv.ofBijective f hbij, map_rel_iff' := fun {a b} => (hle a b).symm },
      rfl⟩

end Aut

section Fence

variable (α : Type*) [Fintype α] [PartialOrder α]

/-- `α` is a disjoint union of fences: the elements can be listed so that comparable elements are
adjacent in the list. A disjoint union of fences has such a listing (each fence in its zigzag
order, one after another); conversely the comparability graph is then a union of paths, and
transitivity forces each path to alternate (a chain `x < y < z` would make `x < z`, at distance 2).
-/
def IsFenceUnion : Prop :=
  ∃ e : α ≃ Fin (Fintype.card α),
    ∀ a b : α, a < b → (e a).val + 1 = (e b).val ∨ (e b).val + 1 = (e a).val

variable {α} [DecidableRel (α := α) (· < ·)]

/-- The elements comparable with `x`, other than `x`. -/
def comp (x : α) : Finset α := univ.filter fun y => x < y ∨ y < x

/-- In a disjoint union of fences no element is comparable with more than two others. -/
theorem card_comp_le_two (h : IsFenceUnion α) (x : α) : (comp x).card ≤ 2 := by
  obtain ⟨e, he⟩ := h
  have key : ∀ y ∈ comp x, (e y).val ∈ ({(e x).val + 1, (e x).val - 1} : Finset ℕ) := by
    intro y hy
    simp only [comp, mem_filter, mem_univ, true_and] at hy
    simp only [mem_insert, mem_singleton]
    rcases hy with hy | hy
    · rcases he x y hy with h | h <;> omega
    · rcases he y x hy with h | h <;> omega
  calc (comp x).card ≤ ({(e x).val + 1, (e x).val - 1} : Finset ℕ).card :=
        card_le_card_of_injOn (fun y => (e y).val) key
          (fun a _ b _ hab => e.injective (Fin.ext hab))
    _ ≤ 2 := card_le_two

/-- A poset with a point comparable with three others is not a disjoint union of fences. -/
theorem not_isFenceUnion {x : α} (hx : 3 ≤ (comp x).card) : ¬ IsFenceUnion α :=
  fun h => absurd (card_comp_le_two h x) (by omega)

end Fence

section Dual

variable {α : Type*} [Fintype α] [PartialOrder α] [DecidableRel (α := α) (· < ·)]

/-- A point with `k` elements below, and no point with `k` elements above, rule out
self-duality. -/
theorem isEmpty_iso_dual (x : α) (h : ∀ y : α, (above y).card ≠ (below x).card) :
    IsEmpty (α ≃o αᵒᵈ) := by
  classical
  refine ⟨fun φ => h (OrderDual.ofDual (φ x)) ?_⟩
  rw [← card_below_map φ x]
  apply card_bij (fun y _ => OrderDual.toDual y)
  · intro y hy
    simp only [above, mem_filter, mem_univ, true_and] at hy
    simp only [below, mem_filter, mem_univ, true_and]
    exact hy
  · intro a _ b _ hab; exact hab
  · intro y hy
    exact ⟨OrderDual.ofDual y, by simpa [above, below] using hy, rfl⟩

end Dual

end Orbits516140
