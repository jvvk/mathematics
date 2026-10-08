import LeanProofs.TwoTri.Preserve

/-!
# The good pair returns

The induction in the proof of Theorem 1 only ever inserts into the chain of faces along one
side `xy` of a face of `A`. We carry the following invariant (`Inv`): a face `x y z` of `A`, and
two *different* faces `β` and `T` of `B`, both meeting the open segment `xy` in their interiors,
with `β` sharing no vertex with `x y z` and `T` not having `x` or `y` as a vertex. (`(xyz, β)` is
then a good pair, and `T` is the face `T_k` of the case `m ≥ 4` of Lemma 5.)

After inserting `p ∈ int(xyz) ∩ int(β)`, the triple `(x y p, T, the piece of β meeting xy)`
satisfies the invariant again. This is the case `m ≥ 4` of the paper's Lemma 5 iterated; the
remaining case of that lemma is not needed for Theorem 1.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Three points with `p ≠ b`, both `x` and `y` on the line `pb`, are collinear. -/
lemma orient_collinear {p b x y : K × K} (hpb : p ≠ b) (hx : orient p b x = 0)
    (hy : orient p b y = 0) : orient x y p = 0 := by
  have e1 : orient x y p * (b.1 - p.1) = 0 := by
    unfold orient at hx hy ⊢; linear_combination (x.1 - p.1) * hy - (y.1 - p.1) * hx
  have e2 : orient x y p * (b.2 - p.2) = 0 := by
    unfold orient at hx hy ⊢; linear_combination (x.2 - p.2) * hy - (y.2 - p.2) * hx
  by_contra h
  apply hpb
  ext
  · have := (mul_eq_zero.mp e1).resolve_left h; linarith
  · have := (mul_eq_zero.mp e2).resolve_left h; linarith

/-- Shifting a point in direction `(1, k)`. -/
def shift (r : K × K) (k t : K) : K × K := (r.1 + t, r.2 + t * k)

lemma orient_shift (a b r : K × K) (k t : K) :
    orient a b (shift r k t) = orient a b r + t * ((b.1 - a.1) * k - (b.2 - a.2)) := by
  unfold orient shift; ring

/-- A point strictly inside two triangles can be moved, staying inside both, onto no line
through two points of `P`. -/
lemma exists_generic {P : Finset (K × K)} {x y z b₁ b₂ b₃ r : K × K} (h1 : InTri x y z r)
    (h2 : InTri b₁ b₂ b₃ r) :
    ∃ p, InTri x y z p ∧ InTri b₁ b₂ b₃ p ∧ Generic P p := by
  classical
  set G := (P ×ˢ P).filter (fun ab : (K × K) × (K × K) => ab.1 ≠ ab.2)
  have hG : ∀ ab ∈ G, ab.1 ∈ P ∧ ab.2 ∈ P ∧ ab.1 ≠ ab.2 := by
    intro ab h; simp only [G, Finset.mem_filter, Finset.mem_product] at h; exact ⟨h.1.1, h.1.2, h.2⟩
  -- a direction parallel to no line through two points
  obtain ⟨k, -, -, hk⟩ := exists_small (∅ : Finset Unit) G (fun _ => 1) (fun _ => 0)
    (fun ab => -(ab.2.2 - ab.1.2)) (fun ab => ab.2.1 - ab.1.1) (by simp) (by
      intro ab hab
      obtain ⟨-, -, hne⟩ := hG ab hab
      by_contra hc; push Not at hc
      apply hne; ext <;> linarith [hc.1, hc.2])
  set sides : Fin 6 → (K × K) × (K × K) :=
    ![(x, y), (y, z), (z, x), (b₁, b₂), (b₂, b₃), (b₃, b₁)]
  obtain ⟨t, -, ht, hgen⟩ := exists_small Finset.univ G
    (fun i => orient (sides i).1 (sides i).2 r)
    (fun i => ((sides i).2.1 - (sides i).1.1) * k - ((sides i).2.2 - (sides i).1.2))
    (fun ab => orient ab.1 ab.2 r)
    (fun ab => (ab.2.1 - ab.1.1) * k - (ab.2.2 - ab.1.2)) (by
      intro i _
      fin_cases i
      exacts [h1.1, h1.2.1, h1.2.2, h2.1, h2.2.1, h2.2.2]) (by
      intro ab hab
      right
      have := hk ab hab
      intro h; apply this; linarith)
  refine ⟨shift r k t, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩ <;> rw [orient_shift]
    exacts [ht 0 (by simp), ht 1 (by simp), ht 2 (by simp)]
  · refine ⟨?_, ?_, ?_⟩ <;> rw [orient_shift]
    exacts [ht 3 (by simp), ht 4 (by simp), ht 5 (by simp)]
  · intro a ha b hb hab
    rw [orient_shift]
    exact hgen (a, b) (by simp [G, ha, hb, hab])

/-- A triangle cut from `b₁ b₂ b₃` by a point `p` inside it lies inside it. -/
lemma subtri {b₁ b₂ b₃ p q : K × K} (hp : InTri b₁ b₂ b₃ p) (hq : InTri b₁ b₂ p q) :
    InTri b₁ b₂ b₃ q := by
  have hD := hp.ccw
  obtain ⟨p1, p2, p3⟩ := hp
  obtain ⟨q1, q2, q3⟩ := hq
  have c1 : orient b₂ b₃ b₁ = orient b₁ b₂ b₃ := (orient_cyc _ _ _).symm
  have c2 : orient b₃ b₁ b₂ = orient b₁ b₂ b₃ := by rw [← orient_cyc, ← orient_cyc]
  have B2 := orient_bary b₁ b₂ p q b₂ b₃
  have B3 := orient_bary b₁ b₂ p q b₃ b₁
  rw [c1, orient_self13] at B2
  rw [c2, orient_self23] at B3
  refine ⟨q1, ?_, ?_⟩
  · have : 0 < orient b₁ b₂ p * orient b₂ b₃ q := by rw [B2]; nlinarith [mul_pos q2 hD, mul_pos q1 p2]
    exact pos_of_mul_pos_right this p1.le
  · have : 0 < orient b₁ b₂ p * orient b₃ b₁ q := by rw [B3]; nlinarith [mul_pos q3 hD, mul_pos q1 p3]
    exact pos_of_mul_pos_right this p1.le

/-- A face stays a face when segments are added and the new point is not inside it. -/
lemma Face.mono {P : Finset (K × K)} {T T' : Finset (Sym2 (K × K))} {a b c p : K × K}
    (hf : Face P T a b c) (hT : T ⊆ T') (hp : ¬ InTri a b c p) : Face (insert p P) T' a b c := by
  obtain ⟨ha, hb, hc, hD, h1, h2, h3, he⟩ := hf
  refine ⟨Finset.mem_insert_of_mem ha, Finset.mem_insert_of_mem hb, Finset.mem_insert_of_mem hc,
    hD, hT h1, hT h2, hT h3, fun q hq => ?_⟩
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact hp
  · exact he q hq

/-- One of the three pieces into which `p` cuts a face is a face of the subdivided set. -/
lemma Face.piece {P : Finset (K × K)} {T T' : Finset (Sym2 (K × K))} {b₁ b₂ b₃ p : K × K}
    (hf : Face P T b₁ b₂ b₃) (hp : InTri b₁ b₂ b₃ p) (hT : T ⊆ T') (h1 : s(p, b₁) ∈ T')
    (h2 : s(p, b₂) ∈ T') : Face (insert p P) T' b₁ b₂ p := by
  obtain ⟨ha, hb, hc, hD, e1, e2, e3, he⟩ := hf
  refine ⟨Finset.mem_insert_of_mem ha, Finset.mem_insert_of_mem hb, Finset.mem_insert_self _ _,
    hp.1, hT e1, by rw [Sym2.eq_swap]; exact h2, h1, fun q hq hin => ?_⟩
  rcases Finset.mem_insert.mp hq with rfl | hq
  · have := hin.2.1; simp at this
  · exact he q hq (subtri hp hin)

/-- A point `q` inside `b₁ b₂ b₃`, on none of the lines from an interior point `p` to the
vertices, lies inside one of the three pieces. -/
lemma piece_of_signs {b₁ b₂ b₃ p q : K × K} (hp : InTri b₁ b₂ b₃ p) (hq : InTri b₁ b₂ b₃ q)
    (n1 : orient p b₁ q ≠ 0) (n2 : orient p b₂ q ≠ 0) (n3 : orient p b₃ q ≠ 0) :
    InTri b₁ b₂ p q ∨ InTri b₂ b₃ p q ∨ InTri b₃ b₁ p q := by
  obtain ⟨p1, p2, p3⟩ := hp
  have B := orient_bary b₁ b₂ b₃ p q p
  simp only [orient_self23, mul_zero] at B
  have e : ∀ b, orient q p b = orient p b q := fun b => orient_cyc q p b
  rw [e, e, e] at B
  have s2 : ∀ b, orient b p q = -orient p b q := fun b => orient_swap12 p b q
  unfold InTri
  rw [s2, s2, s2]
  obtain ⟨q1, q2, q3⟩ := hq
  rcases lt_or_gt_of_ne n1 with h1 | h1 <;> rcases lt_or_gt_of_ne n2 with h2 | h2 <;>
    rcases lt_or_gt_of_ne n3 with h3 | h3
  · nlinarith [mul_pos p1 (neg_pos.mpr h3), mul_pos p2 (neg_pos.mpr h1),
      mul_pos p3 (neg_pos.mpr h2)]
  · exact Or.inr (Or.inr ⟨q3, by linarith, h3⟩)
  · exact Or.inr (Or.inl ⟨q2, by linarith, h2⟩)
  · exact Or.inr (Or.inr ⟨q3, by linarith, h3⟩)
  · exact Or.inl ⟨q1, by linarith, h1⟩
  · exact Or.inl ⟨q1, by linarith, h1⟩
  · exact Or.inr (Or.inl ⟨q2, by linarith, h2⟩)
  · nlinarith [mul_pos p1 h3, mul_pos p2 h1, mul_pos p3 h2]

end TwoTri
