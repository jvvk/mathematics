import LeanProofs.TwoTri.Step

/-!
# Moving a configuration along an embedding of ordered fields

All notions are sign conditions on `orient`, so an order-embedding ring map `ℚ → K` carries a
configuration over `ℚ` to one over `K` (in particular over `ℝ`).
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]

section
variable (f : K →+* L) (hf : StrictMono f)
include hf

/-- The map on points. -/
def pmap (f : K →+* L) : K × K → L × L := Prod.map f f

lemma pmap_inj : Function.Injective (pmap f) := by
  intro a b h
  simp only [pmap, Prod.map, Prod.mk.injEq] at h
  ext
  · exact hf.injective h.1
  · exact hf.injective h.2

omit hf in
lemma orient_pmap (a b c : K × K) :
    orient (pmap f a) (pmap f b) (pmap f c) = f (orient a b c) := by
  simp [orient, pmap, map_sub, map_mul]

lemma f_pos {x : K} : 0 < f x ↔ 0 < x := by rw [← map_zero f]; exact hf.lt_iff_lt
lemma f_neg {x : K} : f x < 0 ↔ x < 0 := by rw [← map_zero f]; exact hf.lt_iff_lt
lemma f_ne {x : K} : f x ≠ 0 ↔ x ≠ 0 := by
  rw [← map_zero f]; exact hf.injective.ne_iff

lemma scross_pmap {a b c d : K × K} :
    SCross (pmap f a) (pmap f b) (pmap f c) (pmap f d) ↔ SCross a b c d := by
  simp only [SCross, orient_pmap, ← map_mul, f_neg f hf]

lemma cross_map {s t : Sym2 (K × K)} :
    Cross (s.map (pmap f)) (t.map (pmap f)) ↔ Cross s t := by
  induction s using Sym2.ind; induction t using Sym2.ind
  simp only [Sym2.map_mk, cross_mk]; exact scross_pmap f hf

lemma genPos_image {P : Finset (K × K)} (h : GenPos P) : GenPos (P.image (pmap f)) := by
  intro a ha b hb c hc hab hac hbc
  obtain ⟨a, ha', rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b, hb', rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp hc
  rw [orient_pmap, f_ne f hf]
  exact h a ha' b hb' c hc' (fun e => hab (e ▸ rfl)) (fun e => hac (e ▸ rfl)) (fun e => hbc (e ▸ rfl))

lemma mem_segs_image {P : Finset (K × K)} {s : Sym2 (L × L)}
    (hs : s ∈ segs (P.image (pmap f))) : ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧
      s = s(pmap f a, pmap f b) := by
  induction s using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb, hab⟩ := mk_mem_segs.mp hs
    obtain ⟨a, ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b, hb', rfl⟩ := Finset.mem_image.mp hb
    exact ⟨a, ha', b, hb', fun e => hab (e ▸ rfl), rfl⟩

lemma isTri_image {P : Finset (K × K)} {T : Finset (Sym2 (K × K))} (h : IsTri P T) :
    IsTri (P.image (pmap f)) (T.image (Sym2.map (pmap f))) := by
  have inj := pmap_inj f hf
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s, hs', rfl⟩ := Finset.mem_image.mp hs
    induction s using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hab⟩ := mk_mem_segs.mp (h.1 hs')
      exact mk_mem_segs.mpr ⟨Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb,
        inj.ne hab⟩
  · intro s hs t ht
    obtain ⟨s, hs', rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨t, ht', rfl⟩ := Finset.mem_image.mp ht
    rw [cross_map f hf]; exact h.2.1 s hs' t ht'
  · intro s hs hnot
    obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_segs_image f hf hs
    have hn : s(a, b) ∉ T := fun h' =>
      hnot (Finset.mem_image.mpr ⟨_, h', by simp [Sym2.map_mk]⟩)
    obtain ⟨t, ht, hc⟩ := h.2.2 s(a, b) (mk_mem_segs.mpr ⟨ha, hb, hab⟩) hn
    refine ⟨t.map (pmap f), Finset.mem_image_of_mem _ ht, ?_⟩
    have : s(pmap f a, pmap f b) = (s(a, b)).map (pmap f) := by simp [Sym2.map_mk]
    rw [this, cross_map f hf]; exact hc

lemma hullP_image {P : Finset (K × K)} {a b : K × K} :
    HullP (P.image (pmap f)) (pmap f a) (pmap f b) ↔ HullP P a b := by
  have inj := pmap_inj f hf
  simp only [HullP, Finset.forall_mem_image, orient_pmap, f_pos f hf, f_neg f hf, inj.ne_iff]

lemma hullEdges_image {P : Finset (K × K)} :
    hullEdges (P.image (pmap f)) = (hullEdges P).image (Sym2.map (pmap f)) := by
  have inj := pmap_inj f hf
  ext s
  constructor
  · intro hs
    obtain ⟨a, ha, b, hb, hab, rfl⟩ :=
      mem_segs_image f hf (Finset.mem_filter.mp hs).1
    rw [mk_mem_hullEdges, hullP_image f hf] at hs
    exact Finset.mem_image.mpr ⟨s(a, b), mk_mem_hullEdges.mpr ⟨ha, hb, hab, hs.2.2.2⟩,
      by simp [Sym2.map_mk]⟩
  · intro hs
    obtain ⟨s, hs', rfl⟩ := Finset.mem_image.mp hs
    induction s using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hab, hh⟩ := mk_mem_hullEdges.mp hs'
      rw [Sym2.map_mk, mk_mem_hullEdges, hullP_image f hf]
      exact ⟨Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb, inj.ne hab, hh⟩

end

end TwoTri
