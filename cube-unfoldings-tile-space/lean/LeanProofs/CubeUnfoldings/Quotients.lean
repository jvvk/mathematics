import Mathlib

/-!
# Unfoldings of the cube: periodic tilings as finite quotients (Section 3)

A family of finite sets of cells `S` (cell `b` sitting at `c b`) tiles `V` under a subgroup `L`
when every point of `V` is `c b + ℓ` for exactly one `b ∈ S` and `ℓ ∈ L`.
For `L = ker φ` with `φ : V →+ G` onto a finite group:
* `tilesBy_ker_iff`: tiling iff every `g : G` is `φ (c b)` for exactly one `b ∈ S`;
* `tilesBy_ker_iff_card`: iff `φ ∘ c` is injective on `S` and `|S| = |G|`;
* `tiles_one_iff` (Lemma 3): one tile `P` tiles iff `φ` is injective on `P` and `|P| = |G|`;
* `tiles_two_iff` (Lemma 4): with `|G| = |P| + |Q|`, the tiles `P` and `Q` tile iff `φ` is
  injective on each and their images are disjoint;
* `tiles_neg_iff` (Lemma 5): with `|G| = 2|P|` and `φ` injective on `P`, the tiles `P` and
  `t - P` tile iff `φ t ∉ A + A`, `A = φ(P)`; so some `t` works iff `A + A ≠ G`.
-/

open Pointwise

namespace CubeUnfoldings

set_option linter.unusedSectionVars false

variable {V G β : Type*} [AddCommGroup V] [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The translates `c b + ℓ`, `b ∈ S`, `ℓ ∈ L`, cover `V` exactly once. -/
def TilesBy (S : Finset β) (c : β → V) (L : AddSubgroup V) : Prop :=
  ∀ x : V, ∃! q : β × L, q.1 ∈ S ∧ x = c q.1 + q.2

theorem tilesBy_ker_iff {S : Finset β} {c : β → V} {φ : V →+ G}
    (hφ : Function.Surjective φ) :
    TilesBy S c φ.ker ↔ ∀ g : G, ∃! b, b ∈ S ∧ φ (c b) = g := by
  constructor
  · intro h g
    obtain ⟨x, rfl⟩ := hφ g
    obtain ⟨⟨b, ℓ⟩, ⟨hb, hx⟩, hu⟩ := h x
    refine ⟨b, ⟨hb, ?_⟩, ?_⟩
    · rw [hx, map_add, (AddMonoidHom.mem_ker).1 ℓ.2, add_zero]
    · rintro b' ⟨hb', e⟩
      have hk : x - c b' ∈ φ.ker := by
        rw [AddMonoidHom.mem_ker, map_sub, e, sub_self]
      have := hu ⟨b', ⟨x - c b', hk⟩⟩ ⟨hb', by simp⟩
      exact congrArg Prod.fst this
  · intro h x
    obtain ⟨b, ⟨hb, e⟩, hu⟩ := h (φ x)
    have hk : x - c b ∈ φ.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, e, sub_self]
    refine ⟨⟨b, ⟨x - c b, hk⟩⟩, ⟨hb, by simp⟩, ?_⟩
    rintro ⟨b', ℓ'⟩ ⟨hb', hx⟩
    have e' : φ (c b') = φ x := by
      rw [hx, map_add, (AddMonoidHom.mem_ker).1 ℓ'.2, add_zero]
    obtain rfl := hu b' ⟨hb', e'⟩
    refine Prod.ext rfl (Subtype.ext ?_)
    change ℓ'.1 = x - c b'
    rw [hx]; abel

/-- Exactly-once covering of a finite group by the image of a finite set: injective, right size. -/
theorem existsUnique_iff_card {S : Finset β} {f : β → G} :
    (∀ g : G, ∃! b, b ∈ S ∧ f b = g) ↔ Set.InjOn f S ∧ S.card = Fintype.card G := by
  classical
  constructor
  · intro h
    have inj : Set.InjOn f S := by
      intro a ha b hb e
      obtain ⟨_, _, hu⟩ := h (f a)
      exact (hu a ⟨ha, rfl⟩).trans (hu b ⟨hb, e.symm⟩).symm
    refine ⟨inj, ?_⟩
    rw [← Finset.card_image_of_injOn inj, ← Finset.card_univ]
    congr 1
    refine Finset.eq_univ_of_forall fun g => ?_
    obtain ⟨b, ⟨hb, e⟩, _⟩ := h g
    exact Finset.mem_image.2 ⟨b, hb, e⟩
  · rintro ⟨inj, hc⟩ g
    have him : S.image f = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn inj, hc]
    obtain ⟨b, hb, e⟩ := Finset.mem_image.1 (him ▸ Finset.mem_univ g : g ∈ S.image f)
    exact ⟨b, ⟨hb, e⟩, fun b' ⟨hb', e'⟩ => inj hb' hb (e'.trans e.symm)⟩

theorem tilesBy_ker_iff_card {S : Finset β} {c : β → V} {φ : V →+ G}
    (hφ : Function.Surjective φ) :
    TilesBy S c φ.ker ↔ Set.InjOn (φ ∘ c) S ∧ S.card = Fintype.card G :=
  (tilesBy_ker_iff hφ).trans existsUnique_iff_card

/-- Lemma 3: the translates of one tile `P` by `ker φ` tile `V` iff `P` is a transversal. -/
theorem tiles_one_iff {P : Finset V} {φ : V →+ G} (hφ : Function.Surjective φ) :
    TilesBy P id φ.ker ↔ Set.InjOn φ P ∧ P.card = Fintype.card G :=
  tilesBy_ker_iff_card hφ

/-- Two tiles, as cells of `V ⊕ V`: the left copy is `P`, the right copy is `Q`. -/
abbrev TilesTwo (P Q : Finset V) (L : AddSubgroup V) : Prop :=
  TilesBy (P.disjSum Q) (Sum.elim id id) L

/-- Lemma 4. -/
theorem tiles_two_iff [DecidableEq V] {P Q : Finset V} {φ : V →+ G}
    (hφ : Function.Surjective φ) (hG : Fintype.card G = P.card + Q.card) :
    TilesTwo P Q φ.ker ↔
      Set.InjOn φ P ∧ Set.InjOn φ Q ∧ Disjoint (P.image φ) (Q.image φ) := by
  rw [TilesTwo, tilesBy_ker_iff_card hφ, Finset.card_disjSum, hG]
  simp only [and_true]
  constructor
  · intro h
    refine ⟨fun a ha b hb e => ?_, fun a ha b hb e => ?_, ?_⟩
    · have := h (Finset.inl_mem_disjSum.2 ha) (Finset.inl_mem_disjSum.2 hb) e
      exact Sum.inl_injective this
    · have := h (Finset.inr_mem_disjSum.2 ha) (Finset.inr_mem_disjSum.2 hb) e
      exact Sum.inr_injective this
    · rw [Finset.disjoint_left]
      intro g hgP hgQ
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hgP
      obtain ⟨b, hb, e⟩ := Finset.mem_image.1 hgQ
      have := h (Finset.inl_mem_disjSum.2 ha) (Finset.inr_mem_disjSum.2 hb) e.symm
      exact Sum.inl_ne_inr this
  · rintro ⟨hP, hQ, hd⟩
    rintro (a | a) ha (b | b) hb e
    · exact congrArg _ (hP (Finset.inl_mem_disjSum.1 ha) (Finset.inl_mem_disjSum.1 hb) e)
    · have e' : φ a = φ b := e
      refine (Finset.disjoint_left.1 hd
        (Finset.mem_image_of_mem φ (Finset.inl_mem_disjSum.1 ha)) ?_).elim
      rw [e']; exact Finset.mem_image_of_mem φ (Finset.inr_mem_disjSum.1 hb)
    · have e' : φ a = φ b := e
      refine (Finset.disjoint_right.1 hd
        (Finset.mem_image_of_mem φ (Finset.inr_mem_disjSum.1 ha)) ?_).elim
      rw [e']; exact Finset.mem_image_of_mem φ (Finset.inl_mem_disjSum.1 hb)
    · exact congrArg _ (hQ (Finset.inr_mem_disjSum.1 ha) (Finset.inr_mem_disjSum.1 hb) e)

/-- The point reflection of `P` translated by `t`. -/
def refl [DecidableEq V] (P : Finset V) (t : V) : Finset V := P.image (fun p => t - p)

lemma card_refl [DecidableEq V] (P : Finset V) (t : V) : (refl P t).card = P.card :=
  Finset.card_image_of_injective _ (sub_right_injective)

lemma injOn_refl [DecidableEq V] {P : Finset V} {φ : V →+ G} (t : V) (h : Set.InjOn φ P) :
    Set.InjOn φ (refl P t) := by
  intro x hx y hy e
  simp only [refl, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [map_sub, map_sub, sub_right_inj] at e
  rw [h ha hb e]

lemma disjoint_refl_iff [DecidableEq V] {P : Finset V} {φ : V →+ G} (t : V) :
    Disjoint (P.image φ) ((refl P t).image φ) ↔ φ t ∉ P.image φ + P.image φ := by
  rw [Finset.disjoint_left, Finset.mem_add]
  simp only [refl, Finset.image_image, Finset.mem_image, Function.comp_def, map_sub]
  constructor
  · rintro h ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, e⟩
    exact h ⟨a, ha, rfl⟩ ⟨b, hb, by rw [← e]; abel⟩
  · rintro h _ ⟨a, ha, rfl⟩ ⟨b, hb, e⟩
    exact h ⟨φ a, ⟨a, ha, rfl⟩, φ b, ⟨b, hb, rfl⟩, by rw [← e]; abel⟩

/-- Lemma 5, for a given translation `t`. -/
theorem tiles_refl_iff [DecidableEq V] {P : Finset V} {φ : V →+ G}
    (hφ : Function.Surjective φ) (hG : Fintype.card G = 2 * P.card) (hP : Set.InjOn φ P)
    (t : V) :
    TilesTwo P (refl P t) φ.ker ↔ φ t ∉ P.image φ + P.image φ := by
  rw [tiles_two_iff hφ (by rw [card_refl, hG, two_mul]), disjoint_refl_iff]
  exact ⟨fun h => h.2.2, fun h => ⟨hP, injOn_refl t hP, h⟩⟩

/-- Lemma 5: `P` and some `t - P` tile under `ker φ` iff the sumset `A + A` misses a point. -/
theorem exists_tiles_refl_iff [DecidableEq V] {P : Finset V} {φ : V →+ G}
    (hφ : Function.Surjective φ) (hG : Fintype.card G = 2 * P.card) (hP : Set.InjOn φ P) :
    (∃ t, TilesTwo P (refl P t) φ.ker) ↔ P.image φ + P.image φ ≠ Finset.univ := by
  simp only [tiles_refl_iff hφ hG hP, ne_eq, Finset.eq_univ_iff_forall, not_forall]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨φ t, ht⟩
  · rintro ⟨s, hs⟩
    obtain ⟨t, rfl⟩ := hφ s
    exact ⟨t, hs⟩

end CubeUnfoldings
