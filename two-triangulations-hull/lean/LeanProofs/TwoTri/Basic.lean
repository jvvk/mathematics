import LeanProofs.TwoTri.Orient

/-!
# Segments, crossings, triangulations, faces, hull edges

Points are elements of `K × K` for an ordered field `K`; a point set is a `Finset`, a segment is
an unordered pair `Sym2`, and a set of segments is a `Finset (Sym2 _)`.

For points in general position (no three on a line), two segments with four distinct endpoints
meet iff their endpoints separate each other; `SCross` is that sign test. `Cross.lean` proves
that it agrees with "the closed segments meet" (`scross_iff_meet`).

A *triangulation* is, as in the paper, a maximal set of pairwise non-crossing segments with
endpoints in the set.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Segment `ab` and segment `cd` cross: each separates the endpoints of the other. -/
def SCross (a b c d : K × K) : Prop :=
  orient a b c * orient a b d < 0 ∧ orient c d a * orient c d b < 0

instance (a b c d : K × K) : Decidable (SCross a b c d) := by unfold SCross; infer_instance

lemma scross_swap12 {a b c d : K × K} : SCross b a c d ↔ SCross a b c d := by
  unfold SCross
  rw [orient_swap12 a b c, orient_swap12 a b d, mul_comm (orient c d b)]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩

lemma scross_swap34 {a b c d : K × K} : SCross a b d c ↔ SCross a b c d := by
  unfold SCross
  rw [orient_swap12 c d a, orient_swap12 c d b, mul_comm (orient a b d)]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

lemma scross_comm {a b c d : K × K} : SCross c d a b ↔ SCross a b c d := by
  unfold SCross; exact And.comm

/-- Crossing of two segments given as unordered pairs. -/
def crossB : Sym2 (K × K) → Sym2 (K × K) → Bool :=
  Sym2.lift₂ ⟨fun a b c d => decide (SCross a b c d), fun a b c d => by
    constructor
    · simp only [scross_swap12]
    · simp only [scross_swap34]⟩

/-- The segments `s` and `t` cross. -/
def Cross (s t : Sym2 (K × K)) : Prop := crossB s t = true

instance (s t : Sym2 (K × K)) : Decidable (Cross s t) := by unfold Cross; infer_instance

@[simp] lemma cross_mk {a b c d : K × K} : Cross s(a, b) s(c, d) ↔ SCross a b c d := by
  simp [Cross, crossB]

lemma cross_comm {s t : Sym2 (K × K)} : Cross s t ↔ Cross t s := by
  induction s using Sym2.ind; induction t using Sym2.ind
  simp only [cross_mk]; exact scross_comm.symm

/-- The segments between distinct points of `P`. -/
def segs (P : Finset (K × K)) : Finset (Sym2 (K × K)) := P.sym2.filter (fun s => ¬ s.IsDiag)

lemma mk_mem_segs {P : Finset (K × K)} {a b : K × K} :
    s(a, b) ∈ segs P ↔ a ∈ P ∧ b ∈ P ∧ a ≠ b := by
  simp [segs, Finset.mk_mem_sym2_iff, and_assoc]

/-- No three distinct points of `P` are collinear. -/
def GenPos (P : Finset (K × K)) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, a ≠ b → a ≠ c → b ≠ c → orient a b c ≠ 0

instance (P : Finset (K × K)) : Decidable (GenPos P) := by unfold GenPos; infer_instance

/-- `T` is a triangulation of `P`: segments of `P`, pairwise non-crossing, and maximal. -/
def IsTri (P : Finset (K × K)) (T : Finset (Sym2 (K × K))) : Prop :=
  T ⊆ segs P ∧ (∀ s ∈ T, ∀ t ∈ T, ¬ Cross s t) ∧ ∀ s ∈ segs P, s ∉ T → ∃ t ∈ T, Cross s t

instance (P : Finset (K × K)) (T : Finset (Sym2 (K × K))) : Decidable (IsTri P T) := by
  unfold IsTri; infer_instance

/-- All points of `P` other than `a, b` lie strictly on one side of the line `ab`. -/
def HullP (P : Finset (K × K)) (a b : K × K) : Prop :=
  (∀ c ∈ P, c ≠ a → c ≠ b → 0 < orient a b c) ∨ (∀ c ∈ P, c ≠ a → c ≠ b → orient a b c < 0)

instance (P : Finset (K × K)) (a b : K × K) : Decidable (HullP P a b) := by
  unfold HullP; infer_instance

lemma hullP_swap {P : Finset (K × K)} {a b : K × K} : HullP P b a ↔ HullP P a b := by
  unfold HullP
  simp only [orient_swap12 a b, neg_pos, neg_lt_zero]
  constructor
  · rintro (h | h)
    · exact Or.inr fun c hc h1 h2 => h c hc h2 h1
    · exact Or.inl fun c hc h1 h2 => h c hc h2 h1
  · rintro (h | h)
    · exact Or.inr fun c hc h1 h2 => h c hc h2 h1
    · exact Or.inl fun c hc h1 h2 => h c hc h2 h1

def hullB (P : Finset (K × K)) : Sym2 (K × K) → Bool :=
  Sym2.lift ⟨fun a b => decide (HullP P a b), fun a b => by simp only [hullP_swap]⟩

/-- The edges of the convex hull of `P`. -/
def hullEdges (P : Finset (K × K)) : Finset (Sym2 (K × K)) :=
  (segs P).filter (fun s => hullB P s = true)

lemma mk_mem_hullEdges {P : Finset (K × K)} {a b : K × K} :
    s(a, b) ∈ hullEdges P ↔ a ∈ P ∧ b ∈ P ∧ a ≠ b ∧ HullP P a b := by
  rw [hullEdges, Finset.mem_filter, mk_mem_segs]
  simp [hullB, and_assoc]

/-- `r` lies strictly inside the counterclockwise triangle `x y z`. -/
def InTri (x y z r : K × K) : Prop := 0 < orient x y r ∧ 0 < orient y z r ∧ 0 < orient z x r

instance (x y z r : K × K) : Decidable (InTri x y z r) := by unfold InTri; infer_instance

lemma InTri.rot {x y z r : K × K} (h : InTri x y z r) : InTri y z x r :=
  ⟨h.2.1, h.2.2, h.1⟩

lemma InTri.ccw {x y z r : K × K} (h : InTri x y z r) : 0 < orient x y z := by
  have := orient_sum x y z r; linarith [h.1, h.2.1, h.2.2]

/-- `x y z` (counterclockwise) is a face of `T`: its sides are in `T` and no point of `P`
lies strictly inside it. -/
def Face (P : Finset (K × K)) (T : Finset (Sym2 (K × K))) (x y z : K × K) : Prop :=
  x ∈ P ∧ y ∈ P ∧ z ∈ P ∧ 0 < orient x y z ∧ s(x, y) ∈ T ∧ s(y, z) ∈ T ∧ s(z, x) ∈ T ∧
    ∀ q ∈ P, ¬ InTri x y z q

instance (P : Finset (K × K)) (T : Finset (Sym2 (K × K))) (x y z : K × K) :
    Decidable (Face P T x y z) := by unfold Face; infer_instance

lemma Face.rot {P : Finset (K × K)} {T : Finset (Sym2 (K × K))} {x y z : K × K}
    (h : Face P T x y z) : Face P T y z x := by
  obtain ⟨hx, hy, hz, ho, h1, h2, h3, he⟩ := h
  exact ⟨hy, hz, hx, by rw [← orient_cyc]; exact ho, h2, h3, h1,
    fun q hq hin => he q hq ⟨hin.2.2, hin.1, hin.2.1⟩⟩

lemma Face.ne {P : Finset (K × K)} {T : Finset (Sym2 (K × K))} {x y z : K × K}
    (h : Face P T x y z) : x ≠ y ∧ y ≠ z ∧ z ≠ x := by
  have ho := h.2.2.2.1
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp at ho

end TwoTri
