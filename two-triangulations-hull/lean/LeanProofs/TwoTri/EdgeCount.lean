import LeanProofs.TwoTri.SideFace
import LeanProofs.TwoTri.Count

/-!
# Every triangulation has `3n - 3 - h` edges

Double counting, with no appeal to Euler's formula:
* each face (counted once per rotation) is the left face of exactly one oriented edge, and the
  oriented edges with no face on their left are the hull edges, oriented clockwise:
  `|faces| + h = 2|T|`;
* for a generic linear functional `φ`, each face has exactly one top vertex, and the faces with
  top vertex `v` correspond to consecutive pairs among the edges going down from `v`; every point
  but the lowest has such an edge (the fan lemma): `|faces| = 3(|T| - n + 1)`.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Faces, as counterclockwise triples (each face appears in its three rotations). -/
def faceTriples (P : Finset (K × K)) (T : Finset (Sym2 (K × K))) :
    Finset ((K × K) × (K × K) × (K × K)) :=
  (P ×ˢ P ×ˢ P).filter (fun t => Face P T t.1 t.2.1 t.2.2)

/-- Oriented edges. -/
def orEdges (P : Finset (K × K)) (T : Finset (Sym2 (K × K))) : Finset ((K × K) × (K × K)) :=
  (P ×ˢ P).filter (fun ab => s(ab.1, ab.2) ∈ T)

lemma card_orEdges {P : Finset (K × K)} {T : Finset (Sym2 (K × K))} (hT : T ⊆ segs P) :
    (orEdges P T).card = 2 * T.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (s := orEdges P T) (f := fun ab => s(ab.1, ab.2))
    (t := T) (fun ab h => (Finset.mem_filter.mp h).2)]
  rw [Finset.sum_const_nat (m := 2), mul_comm]
  intro s hs
  induction s using Sym2.ind with
  | _ a b =>
  obtain ⟨ha, hb, hab⟩ := mk_mem_segs.mp (hT hs)
  have : (orEdges P T).filter (fun ab => s(ab.1, ab.2) = s(a, b)) = {(a, b), (b, a)} := by
    ext ⟨x, y⟩
    simp only [orEdges, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨-, e⟩
      rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨⟨ha, hb⟩, hs⟩, rfl⟩
      · exact ⟨⟨⟨hb, ha⟩, by rw [Sym2.eq_swap]; exact hs⟩, Sym2.eq_swap⟩
  rw [this, Finset.card_pair]
  intro h; exact hab (Prod.mk.inj h).1

/-- `|faces| + h = 2|T|`. -/
theorem faces_add_hull {P : Finset (K × K)} (hP : GenPos P) (h3 : 3 ≤ P.card)
    {T : Finset (Sym2 (K × K))} (hT : IsTri P T) :
    (faceTriples P T).card + (hullEdges P).card = 2 * T.card := by
  classical
  set OE := orEdges P T
  set OL := OE.filter (fun ab => ∃ x ∈ P, 0 < orient ab.1 ab.2 x)
  have h1 : (faceTriples P T).card = OL.card := by
    refine Finset.card_bij (fun t _ => (t.1, t.2.1)) ?_ ?_ ?_
    · intro t ht
      obtain ⟨-, hf⟩ := Finset.mem_filter.mp ht
      obtain ⟨hx, hy, hz, hD, hxy, -, -, -⟩ := hf
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩,
        t.2.2, hz, hD⟩
    · intro t ht t' ht' e
      obtain ⟨-, hf⟩ := Finset.mem_filter.mp ht
      obtain ⟨-, hf'⟩ := Finset.mem_filter.mp ht'
      simp only [Prod.mk.injEq] at e
      obtain ⟨x, y, z⟩ := t
      obtain ⟨x', y', z'⟩ := t'
      simp only at e hf hf'
      obtain ⟨rfl, rfl⟩ := e
      rw [face_unique hP hT.nonCross hf hf']
    · intro ab hab
      obtain ⟨hOE, x, hx, hxpos⟩ := Finset.mem_filter.mp hab
      obtain ⟨hP2, hT'⟩ := Finset.mem_filter.mp hOE
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hP2
      obtain ⟨c, hc, hf⟩ := side_face hP hT ha hb hT' ⟨x, hx, hxpos⟩
      exact ⟨(ab.1, ab.2, c), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_product.mpr ⟨hb, hc⟩⟩, hf⟩, rfl⟩
  have h2 : (OE.filter (fun ab => ¬ ∃ x ∈ P, 0 < orient ab.1 ab.2 x)).card =
      (hullEdges P).card := by
    refine Finset.card_bij (fun ab _ => s(ab.1, ab.2)) ?_ ?_ ?_
    · intro ab hab
      obtain ⟨hOE, hno⟩ := Finset.mem_filter.mp hab
      obtain ⟨hP2, hT'⟩ := Finset.mem_filter.mp hOE
      obtain ⟨ha, hb, hne⟩ := mk_mem_segs.mp (hT.1 hT')
      refine mk_mem_hullEdges.mpr ⟨ha, hb, hne, Or.inr fun c hc hca hcb => ?_⟩
      push Not at hno
      exact lt_of_le_of_ne (hno c hc) (hP _ ha _ hb c hc hne (Ne.symm hca) (Ne.symm hcb))
    · intro ab hab ab' hab' e
      obtain ⟨hOE, hno⟩ := Finset.mem_filter.mp hab
      obtain ⟨hOE', hno'⟩ := Finset.mem_filter.mp hab'
      obtain ⟨ha, hb, hne⟩ := mk_mem_segs.mp (hT.1 (Finset.mem_filter.mp hOE).2)
      rcases Sym2.eq_iff.mp e with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exfalso
        obtain ⟨c, hc, hca, hcb⟩ := third h3 ab.1 ab.2
        have n := hP _ ha _ hb c hc hne (Ne.symm hca) (Ne.symm hcb)
        push Not at hno hno'
        have e1 := hno c hc
        have e2 := hno' c hc
        rw [← h1, ← h2, orient_swap12] at e2
        exact n (by linarith)
    · intro s hs
      induction s using Sym2.ind with
      | _ a b =>
      obtain ⟨ha, hb, hne, hh⟩ := mk_mem_hullEdges.mp hs
      have hsT : s(a, b) ∈ T := (hull_unavoidable hs).mem hT (Finset.mem_filter.mp hs).1
      rcases hullP_iff.mp hh with h | h
      · refine ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by rw [Sym2.eq_swap]; exact hsT⟩, ?_⟩, Sym2.eq_swap⟩
        rintro ⟨x, hx, hxp⟩
        by_cases hxa : x = a
        · subst hxa; simp at hxp
        by_cases hxb : x = b
        · subst hxb; simp at hxp
        have := h x hx hxa hxb; rw [orient_swap12] at hxp; linarith
      · refine ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hsT⟩, ?_⟩, rfl⟩
        rintro ⟨x, hx, hxp⟩
        by_cases hxa : x = a
        · subst hxa; simp at hxp
        by_cases hxb : x = b
        · subst hxb; simp at hxp
        have := h x hx hxb hxa; rw [orient_swap12] at this; linarith
  have h4 := Finset.card_filter_add_card_filter_not (s := OE)
    (p := fun ab => ∃ x ∈ P, 0 < orient ab.1 ab.2 x)
  rw [h1, ← h2, h4, card_orEdges hT.1]

/-- A linear functional taking distinct values on `P`. -/
lemma exists_injective_functional (P : Finset (K × K)) :
    ∃ k : K, ∀ a ∈ P, ∀ b ∈ P, a ≠ b → a.1 + k * a.2 ≠ b.1 + k * b.2 := by
  classical
  obtain ⟨k, -, -, hk⟩ := exists_small (∅ : Finset Unit) ((P ×ˢ P).filter (fun ab => ab.1 ≠ ab.2))
    (fun _ => (1 : K)) (fun _ => 0) (fun ab => ab.1.1 - ab.2.1) (fun ab => ab.1.2 - ab.2.2)
    (by simp) (by
      intro ab hab
      have hne := (Finset.mem_filter.mp hab).2
      by_contra hc; push Not at hc
      exact hne (Prod.ext (by linarith [hc.1]) (by linarith [hc.2])))
  refine ⟨k, fun a ha b hb hab e => hk (a, b) (by simp [ha, hb, hab]) ?_⟩
  simp only; linarith

/-- The angular coordinate seen from `u`, for points in the half-plane `dotd e u · > 0`. -/
def angf (e u r : K × K) : K := (-e.2 * (r.1 - u.1) + e.1 * (r.2 - u.2)) / dotd e u r

lemma ang_lt {e u a b : K × K} (ha : 0 < dotd e u a) (hb : 0 < dotd e u b) :
    0 < orient u a b ↔ angf e u a < angf e u b := by
  have he : 0 < e.1 * e.1 + e.2 * e.2 := by
    by_contra hc; push Not at hc
    have h1 : e.1 = 0 := by nlinarith [mul_self_nonneg e.1, mul_self_nonneg e.2]
    have h2 : e.2 = 0 := by nlinarith [mul_self_nonneg e.1, mul_self_nonneg e.2]
    simp only [dotd, h1, h2, zero_mul, add_zero] at ha; exact lt_irrefl _ ha
  have key : orient u a b * (e.1 * e.1 + e.2 * e.2) =
      dotd e u a * (-e.2 * (b.1 - u.1) + e.1 * (b.2 - u.2)) -
        (-e.2 * (a.1 - u.1) + e.1 * (a.2 - u.2)) * dotd e u b := by
    unfold orient dotd; ring
  unfold angf
  rw [div_lt_div_iff₀ ha hb]
  constructor
  · intro h; have := mul_pos h he; rw [key] at this; linarith
  · intro h
    have : 0 < orient u a b * (e.1 * e.1 + e.2 * e.2) := by rw [key]; linarith
    exact pos_of_mul_pos_left this he.le

/-- No edge leaves a vertex of a face into the face. -/
lemma face_no_inner_edge {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    (hT : NonCross T) {v y z w : K × K} (hf : Face P T v y z) (hw : w ∈ P)
    (hvw : s(v, w) ∈ T) (h1 : 0 < orient v y w) (h2 : 0 < orient v w z) : False := by
  obtain ⟨hv, hy, hz, hD, -, -, -, he⟩ := id hf
  have hwv : w ≠ v := by rintro rfl; simp at h1
  have hc1 : orient y z v = orient v y z := (orient_cyc v y z).symm
  have hc2 : orient z v w = orient v w z := (orient_cyc v w z).symm ▸ (orient_cyc z v w)
  obtain ⟨t, ht, hc, -⟩ := exists_small (Finset.univ : Finset (Fin 2)) (∅ : Finset Unit)
    ![orient v y z, 1] ![orient y z w - orient v y z, -1] (fun _ => (1 : K)) (fun _ => 0)
    (by intro i _; fin_cases i; exacts [hD, one_pos]) (by simp)
  have c0 := hc 0 (by simp); have c1 := hc 1 (by simp)
  simp at c0 c1
  have hin : InTri v y z (lerp v w t) := by
    refine ⟨?_, ?_, ?_⟩ <;> rw [orient_lerp]
    · simp only [orient_self13, mul_zero, zero_add]; exact mul_pos ht h1
    · rw [hc1]; linarith
    · simp only [orient_self23, mul_zero, zero_add]
      have : orient z v w = orient v w z := by rw [orient_cyc z v w]
      rw [this]; exact mul_pos ht h2
  obtain ⟨u, u', hside, hx⟩ := through hP hv hy hz hv hw (Ne.symm hwv)
    (fun h => by have := h.1; simp at this) (he w hw) ht (by linarith) hin
  exact hT _ hvw _ (hf.side_mem hside) (cross_mk.mpr hx)

/-- The direction of `w` inside the wedge `y v z` is a positive combination. -/
lemma dotd_wedge (e v y z w : K × K) :
    orient v y z * dotd e v w = orient v w z * dotd e v y + orient v y w * dotd e v z := by
  unfold orient dotd; ring

/-- The generic functional. -/
def phi (k : K) (r : K × K) : K := r.1 + k * r.2

lemma dotd_down (k : K) (v r : K × K) : dotd (-1, -k) v r = phi k v - phi k r := by
  unfold dotd phi; ring

lemma dotd_up (k : K) (v r : K × K) : dotd (1, k) v r = phi k r - phi k v := by
  unfold dotd phi; ring

/-- Edges going down from `v`. -/
def down (P : Finset (K × K)) (T : Finset (Sym2 (K × K))) (k : K) (v : K × K) :
    Finset (K × K) := P.filter (fun y => s(v, y) ∈ T ∧ phi k y < phi k v)

/-- Faces whose top vertex is `v`. -/
def topFaces (P : Finset (K × K)) (T : Finset (Sym2 (K × K))) (k : K) (v : K × K) :
    Finset ((K × K) × (K × K)) :=
  (P ×ˢ P).filter (fun yz => Face P T v yz.1 yz.2 ∧ phi k yz.1 < phi k v ∧ phi k yz.2 < phi k v)

theorem vertex_count {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    (hT : IsTri P T) {k : K} {v : K × K} (hv : v ∈ P)
    (hne : (down P T k v).Nonempty) : (topFaces P T k v).card + 1 = (down P T k v).card := by
  classical
  set D := down P T k v
  set e : K × K := (-1, -k)
  set g := angf e v
  have hpos : ∀ y ∈ D, 0 < dotd e v y := by
    intro y hy; rw [dotd_down]; linarith [(Finset.mem_filter.mp hy).2.2]
  have hDv : ∀ y ∈ D, y ≠ v := by
    intro y hy h; have := (Finset.mem_filter.mp hy).2.2; rw [h] at this; exact lt_irrefl _ this
  have hDP : ∀ y ∈ D, y ∈ P := fun y hy => (Finset.mem_filter.mp hy).1
  have ginj : Set.InjOn g D := by
    intro y hy z hz e'
    by_contra hyz
    have n := hP v hv y (hDP y hy) z (hDP z hz) (Ne.symm (hDv y hy)) (Ne.symm (hDv z hz)) hyz
    rcases lt_or_gt_of_ne n with h | h
    · have : 0 < orient v z y := by rw [orient_swap23]; linarith
      have := (ang_lt (hpos z hz) (hpos y hy)).mp this
      exact absurd e' (ne_of_gt this)
    · exact absurd e' (ne_of_lt ((ang_lt (hpos y hy) (hpos z hz)).mp h))
  set G := D.image g
  have hG : G.card = D.card := Finset.card_image_of_injOn ginj
  have key : (topFaces P T k v).card = (consecPairs G).card := by
    refine Finset.card_bij (fun yz _ => (g yz.1, g yz.2)) ?_ ?_ ?_
    · intro yz hyz
      obtain ⟨hP2, hf, hy, hz⟩ := Finset.mem_filter.mp hyz
      obtain ⟨hyP, hzP⟩ := Finset.mem_product.mp hP2
      have hyD : yz.1 ∈ D := Finset.mem_filter.mpr ⟨hyP, hf.2.2.2.2.1, hy⟩
      have hzD : yz.2 ∈ D := Finset.mem_filter.mpr ⟨hzP, by
        rw [Sym2.eq_swap]; exact hf.2.2.2.2.2.2.1, hz⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_image_of_mem g hyD,
        Finset.mem_image_of_mem g hzD⟩, (ang_lt (hpos _ hyD) (hpos _ hzD)).mp hf.2.2.2.1, ?_⟩
      intro c hc ⟨h1, h2⟩
      obtain ⟨w, hwD, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨hwP, hwT, -⟩ := Finset.mem_filter.mp hwD
      exact face_no_inner_edge hP hT.nonCross hf hwP hwT
        ((ang_lt (hpos _ hyD) (hpos _ hwD)).mpr h1) ((ang_lt (hpos _ hwD) (hpos _ hzD)).mpr h2)
    · intro yz hyz yz' hyz' e'
      simp only [Prod.mk.injEq] at e'
      have hm : ∀ t ∈ topFaces P T k v, t.1 ∈ D ∧ t.2 ∈ D := by
        intro t ht
        obtain ⟨hP2, hf, hy, hz⟩ := Finset.mem_filter.mp ht
        exact ⟨Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hP2).1, hf.2.2.2.2.1, hy⟩,
          Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hP2).2, by
            rw [Sym2.eq_swap]; exact hf.2.2.2.2.2.2.1, hz⟩⟩
      exact Prod.ext (ginj (hm _ hyz).1 (hm _ hyz').1 e'.1) (ginj (hm _ hyz).2 (hm _ hyz').2 e'.2)
    · rintro ⟨a, b⟩ hab
      obtain ⟨hab2, hlt, hno⟩ := Finset.mem_filter.mp hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab2
      obtain ⟨y, hyD, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨z, hzD, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨hyP, hyT, hyφ⟩ := Finset.mem_filter.mp hyD
      obtain ⟨hzP, hzT, hzφ⟩ := Finset.mem_filter.mp hzD
      have hD : 0 < orient v y z := (ang_lt (hpos _ hyD) (hpos _ hzD)).mpr hlt
      have hf := consec hP hT hv hyP hzP hD hyT hzT fun w hw hwT h1 h2 => by
        have hW := dotd_wedge e v y z w
        have hwpos : 0 < dotd e v w := by
          have : 0 < orient v y z * dotd e v w := by
            rw [hW]; nlinarith [hpos y hyD, hpos z hzD]
          exact pos_of_mul_pos_right this hD.le
        have hwD : w ∈ D := Finset.mem_filter.mpr ⟨hw, hwT, by rw [dotd_down] at hwpos; linarith⟩
        exact hno (g w) (Finset.mem_image_of_mem g hwD)
          ⟨(ang_lt (hpos _ hyD) (hpos _ hwD)).mp h1, (ang_lt (hpos _ hwD) (hpos _ hzD)).mp h2⟩
      exact ⟨(y, z), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hyP, hzP⟩, hf, hyφ, hzφ⟩, rfl⟩
  rw [key, ← hG]
  exact card_consecPairs G (hne.image g)

/-- Each face has exactly one top vertex: `|faces| = 3 · #(faces counted at their top)`. -/
lemma faces_eq_three {P : Finset (K × K)} {T : Finset (Sym2 (K × K))} {k : K}
    (hk : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → phi k a ≠ phi k b) :
    (faceTriples P T).card = 3 * ((faceTriples P T).filter
      (fun t => phi k t.2.1 < phi k t.1 ∧ phi k t.2.2 < phi k t.1)).card := by
  classical
  set FT := faceTriples P T
  set A0 := FT.filter (fun t => phi k t.2.1 < phi k t.1 ∧ phi k t.2.2 < phi k t.1)
  set A1 := FT.filter (fun t => phi k t.1 < phi k t.2.1 ∧ phi k t.2.2 < phi k t.2.1)
  set A2 := FT.filter (fun t => phi k t.1 < phi k t.2.2 ∧ phi k t.2.1 < phi k t.2.2)
  have memFT : ∀ t, t ∈ FT ↔ Face P T t.1 t.2.1 t.2.2 := by
    intro t
    simp only [FT, faceTriples, Finset.mem_filter, Finset.mem_product, and_iff_right_iff_imp]
    intro hf; exact ⟨hf.1, hf.2.1, hf.2.2.1⟩
  have c1 : A1.card = A0.card := by
    refine Finset.card_bij (fun t _ => (t.2.1, t.2.2, t.1)) ?_ ?_ ?_
    · intro t ht
      obtain ⟨hf, h1, h2⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨(memFT _).mpr ((memFT t).mp hf).rot, h2, h1⟩
    · intro t _ t' _ e
      simp only [Prod.mk.injEq] at e
      exact Prod.ext e.2.2 (Prod.ext e.1 e.2.1)
    · intro t ht
      obtain ⟨hf, h1, h2⟩ := Finset.mem_filter.mp ht
      exact ⟨(t.2.2, t.1, t.2.1), Finset.mem_filter.mpr
        ⟨(memFT _).mpr ((memFT t).mp hf).rot.rot, h2, h1⟩, rfl⟩
  have c2 : A2.card = A0.card := by
    refine Finset.card_bij (fun t _ => (t.2.2, t.1, t.2.1)) ?_ ?_ ?_
    · intro t ht
      obtain ⟨hf, h1, h2⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨(memFT _).mpr ((memFT t).mp hf).rot.rot, h1, h2⟩
    · intro t _ t' _ e
      simp only [Prod.mk.injEq] at e
      exact Prod.ext e.2.1 (Prod.ext e.2.2 e.1)
    · intro t ht
      obtain ⟨hf, h1, h2⟩ := Finset.mem_filter.mp ht
      exact ⟨(t.2.1, t.2.2, t.1), Finset.mem_filter.mpr
        ⟨(memFT _).mpr ((memFT t).mp hf).rot, h1, h2⟩, rfl⟩
  have split : FT.filter (fun t => ¬ (phi k t.2.1 < phi k t.1 ∧ phi k t.2.2 < phi k t.1)) =
      A1 ∪ A2 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_union, A1, A2]
    constructor
    · rintro ⟨hf, hn⟩
      obtain ⟨hx, hy, hz, -⟩ := (memFT t).mp hf
      obtain ⟨hxy, hyz, hzx⟩ := ((memFT t).mp hf).ne
      have d1 := hk _ hx _ hy hxy
      have d2 := hk _ hy _ hz hyz
      have d3 := hk _ hz _ hx hzx
      rcases lt_or_gt_of_ne d1 with h1 | h1 <;> rcases lt_or_gt_of_ne d2 with h2 | h2 <;>
        rcases lt_or_gt_of_ne d3 with h3 | h3
      all_goals first
        | exact Or.inl ⟨hf, by linarith, by linarith⟩
        | exact Or.inr ⟨hf, by linarith, by linarith⟩
        | exact absurd ⟨by linarith, by linarith⟩ hn
        | (exfalso; linarith)
    · rintro (⟨hf, h1, h2⟩ | ⟨hf, h1, h2⟩)
      · exact ⟨hf, fun h => by linarith [h.1]⟩
      · exact ⟨hf, fun h => by linarith [h.2]⟩
  have disj : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]
    intro t h1 h2
    have := (Finset.mem_filter.mp h1).2
    have := (Finset.mem_filter.mp h2).2
    linarith
  have := Finset.card_filter_add_card_filter_not (s := FT)
    (p := fun t => phi k t.2.1 < phi k t.1 ∧ phi k t.2.2 < phi k t.1)
  change A0.card + _ = FT.card at this
  rw [split, Finset.card_union_of_disjoint disj, c1, c2] at this
  omega

/-- **Edge count.** Every triangulation of `n ≥ 3` points in general position with `h` hull
edges has `3n - 3 - h` edges. -/
theorem edge_count {P : Finset (K × K)} (hP : GenPos P) (h3 : 3 ≤ P.card)
    {T : Finset (Sym2 (K × K))} (hT : IsTri P T) :
    T.card + 3 + (hullEdges P).card = 3 * P.card := by
  classical
  obtain ⟨k, hk'⟩ := exists_injective_functional P
  have hk : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → phi k a ≠ phi k b := hk'
  have hFH := faces_add_hull hP h3 hT
  have h3F := faces_eq_three (T := T) hk
  set A0 := (faceTriples P T).filter (fun t => phi k t.2.1 < phi k t.1 ∧ phi k t.2.2 < phi k t.1)
  have hne : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨m, hm, hmin⟩ := P.exists_min_image (phi k) hne
  -- faces counted at their top vertex
  have hA0 : A0.card = ∑ v ∈ P, (topFaces P T k v).card := by
    rw [Finset.card_eq_sum_card_fiberwise (s := A0) (f := fun t => t.1) (t := P) (fun t ht =>
      (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1).1)]
    refine Finset.sum_congr rfl fun v _ => ?_
    refine Finset.card_bij (fun t _ => (t.2.1, t.2.2)) ?_ ?_ ?_
    · intro t ht
      obtain ⟨htA, rfl⟩ := Finset.mem_filter.mp ht
      obtain ⟨htF, h1, h2⟩ := Finset.mem_filter.mp htA
      obtain ⟨hP3, hf⟩ := Finset.mem_filter.mp htF
      obtain ⟨-, hP2⟩ := Finset.mem_product.mp hP3
      exact Finset.mem_filter.mpr ⟨hP2, hf, h1, h2⟩
    · intro t ht t' ht' e
      simp only [Prod.mk.injEq] at e
      have h1 := (Finset.mem_filter.mp ht).2
      have h2 := (Finset.mem_filter.mp ht').2
      exact Prod.ext (h1.trans h2.symm) (Prod.ext e.1 e.2)
    · rintro ⟨y, z⟩ hyz
      obtain ⟨hP2, hf, h1, h2⟩ := Finset.mem_filter.mp hyz
      refine ⟨(v, y, z), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hf.1, hP2⟩, hf⟩, h1, h2⟩, rfl⟩, rfl⟩
  -- edges counted at their top endpoint
  have hdown : ∑ v ∈ P, (down P T k v).card = T.card := by
    set DP := (P ×ˢ P).filter (fun vy => s(vy.1, vy.2) ∈ T ∧ phi k vy.2 < phi k vy.1)
    have e1 : DP.card = ∑ v ∈ P, (down P T k v).card := by
      rw [Finset.card_eq_sum_card_fiberwise (s := DP) (f := Prod.fst) (t := P) (fun t ht =>
        (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1)]
      refine Finset.sum_congr rfl fun v _ => ?_
      refine Finset.card_bij (fun t _ => t.2) ?_ ?_ ?_
      · intro t ht
        obtain ⟨htD, rfl⟩ := Finset.mem_filter.mp ht
        obtain ⟨hP2, hT', hφ⟩ := Finset.mem_filter.mp htD
        exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hP2).2, hT', hφ⟩
      · intro t ht t' ht' e
        exact Prod.ext ((Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp ht').2.symm) e
      · intro y hy
        obtain ⟨hyP, hT', hφ⟩ := Finset.mem_filter.mp hy
        have hvP : v ∈ P := (mk_mem_segs.mp (hT.1 hT')).1
        exact ⟨(v, y), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hvP, hyP⟩, hT', hφ⟩, rfl⟩, rfl⟩
    have e2 : DP.card = T.card := by
      refine Finset.card_bij (fun t _ => s(t.1, t.2)) ?_ ?_ ?_
      · intro t ht; exact (Finset.mem_filter.mp ht).2.1
      · intro t ht t' ht' e
        have h1 := (Finset.mem_filter.mp ht).2.2
        have h2 := (Finset.mem_filter.mp ht').2.2
        rcases Sym2.eq_iff.mp e with ⟨a, b⟩ | ⟨a, b⟩
        · exact Prod.ext a b
        · rw [a, b] at h1; linarith
      · intro s hs
        induction s using Sym2.ind with
        | _ a b =>
        obtain ⟨ha, hb, hab⟩ := mk_mem_segs.mp (hT.1 hs)
        rcases lt_or_gt_of_ne (hk a ha b hb hab) with h | h
        · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩,
            by rw [Sym2.eq_swap]; exact hs, h⟩, Sym2.eq_swap⟩
        · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hs, h⟩, rfl⟩
    rw [← e1, e2]
  -- the per-vertex relation
  have hvert : ∀ v ∈ P, (topFaces P T k v).card + (if v = m then 0 else 1) =
      (down P T k v).card := by
    intro v hv
    by_cases hvm : v = m
    · subst hvm
      have hD : down P T k v = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro y hy
        have := (Finset.mem_filter.mp hy).2.2
        linarith [hmin y (Finset.mem_filter.mp hy).1]
      have hF : topFaces P T k v = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro yz hyz
        obtain ⟨hP2, -, h1, -⟩ := Finset.mem_filter.mp hyz
        linarith [hmin yz.1 (Finset.mem_product.mp hP2).1]
      simp [hD, hF]
    · rw [if_neg hvm]
      apply vertex_count hP hT hv
      obtain ⟨w, hw, hwT, hwneg⟩ := fan hP hT hv (1, k) ⟨m, hm, by
        rw [dotd_up]
        have h1 := hmin v hv
        have h2 : phi k m ≠ phi k v := fun e => hk v hv m hm hvm e.symm
        exact sub_neg.mpr (lt_of_le_of_ne h1 h2)⟩
      rw [dotd_up] at hwneg
      exact ⟨w, Finset.mem_filter.mpr ⟨hw, hwT, by linarith⟩⟩
  have hsum := Finset.sum_congr rfl hvert
  rw [Finset.sum_add_distrib, hdown, ← hA0] at hsum
  have hind : ∑ v ∈ P, (if v = m then 0 else 1) = P.card - 1 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.filter_ne' P m, Finset.card_erase_of_mem hm]
  rw [hind] at hsum
  omega

end TwoTri
