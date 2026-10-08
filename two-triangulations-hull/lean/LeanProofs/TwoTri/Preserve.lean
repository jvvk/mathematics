import LeanProofs.TwoTri.Insert

/-!
# Insertion keeps the hull and the shared edges
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- All points of `P` other than `a, b` lie strictly to the left of `a → b`. -/
def HullPos (P : Finset (K × K)) (a b : K × K) : Prop :=
  ∀ c ∈ P, c ≠ a → c ≠ b → 0 < orient a b c

lemma hullP_iff {P : Finset (K × K)} {a b : K × K} :
    HullP P a b ↔ HullPos P a b ∨ HullPos P b a := by
  unfold HullP HullPos
  simp only [orient_swap12 a b, neg_pos]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr fun c hc h1 h2 => h c hc h2 h1
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr fun c hc h1 h2 => h c hc h2 h1

/-- A point inside a triangle is strictly left of a line that has every vertex not on it
strictly to its left. -/
lemma bary_hull {x y z p a b : K × K} (hp : InTri x y z p) (hxy : x ≠ y) (hyz : y ≠ z)
    (hzx : z ≠ x)
    (h : ∀ v, (v = x ∨ v = y ∨ v = z) → v ≠ a → v ≠ b → 0 < orient a b v) :
    0 < orient a b p := by
  have hD := hp.ccw
  obtain ⟨p1, p2, p3⟩ := hp
  have nn : ∀ v, (v = x ∨ v = y ∨ v = z) → 0 ≤ orient a b v := by
    intro v hv
    by_cases hva : v = a
    · subst hva; simp
    by_cases hvb : v = b
    · subst hvb; simp
    exact (h v hv hva hvb).le
  have B := orient_bary x y z p a b
  have nx := nn x (Or.inl rfl)
  have ny := nn y (Or.inr (Or.inl rfl))
  have nz := nn z (Or.inr (Or.inr rfl))
  have strict : 0 < orient a b x ∨ 0 < orient a b y ∨ 0 < orient a b z := by
    by_contra hc
    push Not at hc
    have ex : x = a ∨ x = b := by
      by_contra hn; push Not at hn; linarith [h x (Or.inl rfl) hn.1 hn.2]
    have ey : y = a ∨ y = b := by
      by_contra hn; push Not at hn; linarith [h y (Or.inr (Or.inl rfl)) hn.1 hn.2]
    have ez : z = a ∨ z = b := by
      by_contra hn; push Not at hn; linarith [h z (Or.inr (Or.inr rfl)) hn.1 hn.2]
    rcases ex with rfl | rfl <;> rcases ey with rfl | rfl <;> rcases ez with rfl | rfl <;>
      simp_all
  have hR : 0 < orient y z p * orient a b x + orient z x p * orient a b y +
      orient x y p * orient a b z := by
    rcases strict with s | s | s <;> nlinarith [mul_nonneg p2.le nx, mul_nonneg p3.le ny,
      mul_nonneg p1.le nz, mul_pos p2 s, mul_pos p3 s, mul_pos p1 s]
  rw [← B] at hR
  exact pos_of_mul_pos_right hR hD.le

/-- Inserting a point inside a face does not change the hull edges. -/
theorem hullEdges_insert {P : Finset (K × K)} {T : Finset (Sym2 (K × K))} {x y z p : K × K}
    (hf : Face P T x y z) (hp : InTri x y z p) : hullEdges (insert p P) = hullEdges P := by
  obtain ⟨hx, hy, hz, -, -, -, -, -⟩ := id hf
  obtain ⟨hxy, hyz, hzx⟩ := hf.ne
  have hpP := hf.not_mem hp
  have hvP : ∀ v, (v = x ∨ v = y ∨ v = z) → v ∈ P := by
    rintro v (rfl | rfl | rfl) <;> assumption
  have up : ∀ a b, HullPos P a b → HullPos (insert p P) a b := by
    intro a b h c hc hca hcb
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact bary_hull hp hxy hyz hzx fun v hv hva hvb => h v (hvP v hv) hva hvb
    · exact h c hc hca hcb
  have down : ∀ a b, HullPos (insert p P) a b → HullPos P a b :=
    fun a b h c hc => h c (Finset.mem_insert_of_mem hc)
  have nonew : ∀ a b, (a = p ∨ b = p) → ¬ HullPos (insert p P) a b := by
    intro a b hab h
    have := bary_hull hp hxy hyz hzx fun v hv hva hvb =>
      h v (Finset.mem_insert_of_mem (hvP v hv)) hva hvb
    rcases hab with rfl | rfl <;> simp at this
  ext s
  induction s using Sym2.ind with
  | _ a b =>
    rw [mk_mem_hullEdges, mk_mem_hullEdges, hullP_iff, hullP_iff]
    constructor
    · rintro ⟨ha, hb, hab, hh⟩
      have ha' : a ∈ P := by
        rcases Finset.mem_insert.mp ha with rfl | ha
        · rcases hh with hh | hh
          · exact (nonew _ _ (Or.inl rfl) hh).elim
          · exact (nonew _ _ (Or.inr rfl) hh).elim
        · exact ha
      have hb' : b ∈ P := by
        rcases Finset.mem_insert.mp hb with rfl | hb
        · rcases hh with hh | hh
          · exact (nonew _ _ (Or.inr rfl) hh).elim
          · exact (nonew _ _ (Or.inl rfl) hh).elim
        · exact hb
      exact ⟨ha', hb', hab, hh.imp (down a b) (down b a)⟩
    · rintro ⟨ha, hb, hab, hh⟩
      exact ⟨Finset.mem_insert_of_mem ha, Finset.mem_insert_of_mem hb, hab,
        hh.imp (up a b) (up b a)⟩

/-- Subdividing two triangulations in faces with no common vertex keeps the shared edges. -/
theorem star_inter {P : Finset (K × K)} {A B : Finset (Sym2 (K × K))} (hA : A ⊆ segs P)
    (hB : B ⊆ segs P) {p x y z b₁ b₂ b₃ : K × K} (hpP : p ∉ P) (hb₁ : b₁ ∈ P) (hb₂ : b₂ ∈ P)
    (hb₃ : b₃ ∈ P) (hdisj : ∀ v, (v = x ∨ v = y ∨ v = z) → v ≠ b₁ ∧ v ≠ b₂ ∧ v ≠ b₃) :
    star A p x y z ∩ star B p b₁ b₂ b₃ = A ∩ B := by
  have notin : ∀ (T : Finset (Sym2 (K × K))), T ⊆ segs P → ∀ v, s(p, v) ∉ T := by
    intro T hT v hv
    exact hpP (mk_mem_segs.mp (hT hv)).1
  have hbP : ∀ w, (w = b₁ ∨ w = b₂ ∨ w = b₃) → w ∈ P := by
    rintro w (rfl | rfl | rfl) <;> assumption
  have pair : ∀ v w, (v = x ∨ v = y ∨ v = z) → (w = b₁ ∨ w = b₂ ∨ w = b₃) →
      s(p, v) ≠ s(p, w) := by
    intro v w hv hw e
    rcases Sym2.eq_iff.mp e with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · obtain ⟨h1, h2, h3⟩ := hdisj v hv
      rcases hw with rfl | rfl | rfl <;> simp_all
    · exact hpP (hbP _ hw)
  ext s
  simp only [star, Finset.mem_inter, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h1 | h1, h2 | h2⟩
    · exact ⟨h1, h2⟩
    · rcases h2 with rfl | rfl | rfl <;> exact (notin A hA _ h1).elim
    · rcases h1 with rfl | rfl | rfl <;> exact (notin B hB _ h2).elim
    · rcases h1 with rfl | rfl | rfl <;> rcases h2 with h2 | h2 | h2 <;>
        exact (pair _ _ (by simp) (by simp) h2).elim
  · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, Or.inl h2⟩

end TwoTri
