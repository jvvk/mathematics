import LeanProofs.TwoTri.Choose

/-!
# Lemma 4 (Insertion)

Joining a generic point inside a face to the three vertices of the face gives a triangulation
of the enlarged set; the hull edges do not change; and if two triangulations are subdivided in
faces with no common vertex, the shared edges do not change.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `T` with `p` joined to `x, y, z`. -/
def star (T : Finset (Sym2 (K × K))) (p x y z : K × K) : Finset (Sym2 (K × K)) :=
  T ∪ {s(p, x), s(p, y), s(p, z)}

/-- `p` is on no line through two points of `P`. -/
def Generic (P : Finset (K × K)) (p : K × K) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, a ≠ b → orient a b p ≠ 0

lemma genPos_insert {P : Finset (K × K)} (hP : GenPos P) {p : K × K} (hpP : p ∉ P)
    (hg : Generic P p) : GenPos (insert p P) := by
  intro a ha b hb c hc hab hac hbc
  rcases Finset.mem_insert.mp ha with ha' | ha' <;> rcases Finset.mem_insert.mp hb with hb' | hb' <;>
    rcases Finset.mem_insert.mp hc with hc' | hc'
  · exact absurd (ha'.trans hb'.symm) hab
  · exact absurd (ha'.trans hb'.symm) hab
  · exact absurd (ha'.trans hc'.symm) hac
  · rw [ha', orient_cyc]; exact hg b hb' c hc' hbc
  · exact absurd (hb'.trans hc'.symm) hbc
  · rw [hb', orient_swap12, orient_cyc, neg_ne_zero]; exact hg a ha' c hc' hac
  · rw [hc']; exact hg a ha' b hb' hab
  · exact hP a ha' b hb' c hc' hab hac hbc

/-- Moving from a point inside a triangle towards a vertex stays inside. -/
lemma InTri.lerp_vertex {x y z p v : K × K} (hp : InTri x y z p) (hv : v = x ∨ v = y ∨ v = z)
    {τ : K} (h0 : 0 ≤ τ) (h1 : τ < 1) : InTri x y z (lerp p v τ) := by
  have hD := hp.ccw
  have c1 : orient y z x = orient x y z := (orient_cyc x y z).symm
  have c2 : orient z x y = orient x y z := by rw [← orient_cyc, ← orient_cyc]
  obtain ⟨p1, p2, p3⟩ := hp
  refine ⟨?_, ?_, ?_⟩ <;> rw [orient_lerp] <;> rcases hv with rfl | rfl | rfl <;>
    (try simp only [orient_self13, orient_self23, c1, c2]) <;> nlinarith

lemma Face.not_mem {P : Finset (K × K)} {T : Finset (Sym2 (K × K))} {x y z p : K × K}
    (hf : Face P T x y z) (hp : InTri x y z p) : p ∉ P := fun h => hf.2.2.2.2.2.2.2 p h hp

/-- **Lemma 4 (Insertion)**, the triangulation part. -/
theorem insert_isTri {P : Finset (K × K)} (hP : GenPos P) {A : Finset (Sym2 (K × K))}
    (hA : IsTri P A) {x y z p : K × K} (hf : Face P A x y z) (hp : InTri x y z p)
    (hg : Generic P p) : IsTri (insert p P) (star A p x y z) := by
  obtain ⟨hx, hy, hz, hD, -, -, -, he⟩ := id hf
  have hpP := hf.not_mem hp
  have hpx : p ≠ x := fun h => hpP (h ▸ hx)
  have hpy : p ≠ y := fun h => hpP (h ▸ hy)
  have hpz : p ≠ z := fun h => hpP (h ▸ hz)
  have segmono : segs P ⊆ segs (insert p P) := by
    intro s hs
    induction s using Sym2.ind with
    | _ a b =>
      rw [mk_mem_segs] at hs ⊢
      exact ⟨Finset.mem_insert_of_mem hs.1, Finset.mem_insert_of_mem hs.2.1, hs.2.2⟩
  have hvert : ∀ v, v = x ∨ v = y ∨ v = z → v ∈ P := by
    rintro v (rfl | rfl | rfl) <;> assumption
  -- a new edge does not cross an old one
  have new_old : ∀ v, (v = x ∨ v = y ∨ v = z) → ∀ t ∈ A, ¬ Cross s(p, v) t := by
    intro v hv t ht hcr
    induction t using Sym2.ind with
    | _ c d =>
      rw [cross_mk] at hcr
      obtain ⟨τ, σ, hτ0, hτ1, hσ0, hσ1, e⟩ := hcr.meet
      have hw : InTri x y z (lerp c d σ) := e ▸ hp.lerp_vertex hv hτ0.le hτ1
      have hcd := mk_mem_segs.mp (hA.1 ht)
      obtain ⟨u, w, hside, hx'⟩ :=
        through hP hx hy hz hcd.1 hcd.2.1 hcd.2.2 (he c hcd.1) (he d hcd.2.1) hσ0 hσ1 hw
      exact hA.2.1 _ ht _ (hf.side_mem hside) (cross_mk.mpr hx')
  have new_new : ∀ v w, ¬ Cross s(p, v) s(p, w) := by
    intro v w h; rw [cross_mk] at h; have := h.1; simp at this
  have hnew : ∀ s ∈ ({s(p, x), s(p, y), s(p, z)} : Finset (Sym2 (K × K))),
      ∃ v, (v = x ∨ v = y ∨ v = z) ∧ s = s(p, v) := by
    intro s hs; simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    exacts [⟨x, Or.inl rfl, rfl⟩, ⟨y, Or.inr (Or.inl rfl), rfl⟩, ⟨z, Or.inr (Or.inr rfl), rfl⟩]
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact segmono (hA.1 hs)
    · obtain ⟨v, hv, rfl⟩ := hnew s hs
      exact mk_mem_segs.mpr ⟨Finset.mem_insert_self _ _,
        Finset.mem_insert_of_mem (hvert v hv), fun h => hpP (h ▸ hvert v hv)⟩
  · intro s hs t ht
    rcases Finset.mem_union.mp hs with hs | hs <;> rcases Finset.mem_union.mp ht with ht | ht
    · exact hA.2.1 s hs t ht
    · obtain ⟨v, hv, rfl⟩ := hnew t ht
      exact fun h => new_old v hv s hs (cross_comm.mp h)
    · obtain ⟨v, hv, rfl⟩ := hnew s hs
      exact new_old v hv t ht
    · obtain ⟨v, hv, rfl⟩ := hnew s hs
      obtain ⟨w, hw, rfl⟩ := hnew t ht
      exact new_new v w
  · intro s hs hsA
    have hsA' : s ∉ A := fun h => hsA (Finset.mem_union_left _ h)
    have key : ∀ b ∈ P, b ≠ p → s(p, b) ∉ star A p x y z → ∃ t ∈ star A p x y z,
        Cross s(p, b) t := by
      intro b hb hbp hnot
      have hbx : b ≠ x := by rintro rfl; exact hnot (by simp [star])
      have hby : b ≠ y := by rintro rfl; exact hnot (by simp [star])
      have hbz : b ≠ z := by rintro rfl; exact hnot (by simp [star])
      obtain ⟨u, w, hside, hx'⟩ := exit_cross hP hx hy hz hb hbx hby hbz (he b hb) hp hg
      exact ⟨s(u, w), Finset.mem_union_left _ (hf.side_mem hside), cross_mk.mpr hx'⟩
    induction s using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hab⟩ := mk_mem_segs.mp hs
      rcases Finset.mem_insert.mp ha with ha' | ha'
      · rcases Finset.mem_insert.mp hb with hb' | hb'
        · exact absurd (ha'.trans hb'.symm) hab
        · rw [ha'] at hsA ⊢
          exact key b hb' (by rintro rfl; exact hab ha') hsA
      · rcases Finset.mem_insert.mp hb with hb' | hb'
        · rw [hb', Sym2.eq_swap] at hsA ⊢
          exact key a ha' (by rintro rfl; exact hab hb'.symm) hsA
        · obtain ⟨t, ht, hc⟩ := hA.2.2 s(a, b) (mk_mem_segs.mpr ⟨ha', hb', hab⟩) hsA'
          exact ⟨t, Finset.mem_union_left _ ht, hc⟩

end TwoTri
