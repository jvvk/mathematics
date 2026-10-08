import EnclosingCopy.Enclosing.SegmentBounds
import EnclosingCopy.Enclosing.SegmentCoordinates
import EnclosingCopy.Enclosing.VertexEvent

/-!
# Segment candidates in the Poisson strip model

Theorem 8, segment case, inside the model. Fix an ordered pair of parallel sides `k, k̄`
(`ParPair`: `u k̄ = -u k`, `u k` a unit vector, positive width `h k + h k̄`, and some side
not parallel to them). A *segment candidate* is a triple of sampled points, two on side `k`
and one on side `k̄`, with positions `s₀ < -s₂ < s₁` (the KKT condition, `kkt_segment_iff`),
together with a chord position `c` at which the copy they make tight fits, stays below the
depth cutoff, and is feasible for the whole sample.

* `exists_affine_iff`: one-variable Fourier–Motzkin. It makes "some chord position works"
  a finite conjunction, hence measurable.
* `segCopy_tight`, `seg_certificate`: the three points are tight along the whole chord, and
  positive multipliers make every feasible copy at least as large.
* `segCand_unique`: outside the null event of an extra tight point, a sample has at most one
  segment candidate (as an ordered triple), so the candidate count is an indicator.
-/

namespace Enclosing
open MeasureTheory Set Matrix ENNReal

/-! ### One-variable Fourier–Motzkin -/

/-- Finitely many constraints `a j * c ≤ b j` have a common solution iff every lower bound is
below every upper bound and the constraints with `a j = 0` hold. -/
lemma exists_affine_iff {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∃ c : ℝ, ∀ j, a j * c ≤ b j) ↔
      (∀ j, a j = 0 → 0 ≤ b j) ∧ ∀ j j', 0 < a j → a j' < 0 → b j' / a j' ≤ b j / a j := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun j hj => by simpa [hj] using hc j, fun j j' hj hj' => ?_⟩
    have h1 : c ≤ b j / a j := (le_div_iff₀ hj).mpr (by linarith [hc j])
    have h2 : b j' / a j' ≤ c := (div_le_iff_of_neg hj').mpr (by linarith [hc j'])
    linarith
  · rintro ⟨h0, hlu⟩
    let L := Finset.univ.filter fun j => a j < 0
    let U := Finset.univ.filter fun j => 0 < a j
    by_cases hL : L.Nonempty
    · refine ⟨L.sup' hL fun j => b j / a j, fun j => ?_⟩
      rcases lt_trichotomy (a j) 0 with hn | hz | hp
      · have h := Finset.le_sup' (fun j => b j / a j) (show j ∈ L by simp [L, hn])
        rw [div_le_iff_of_neg hn] at h
        linarith
      · simp [hz, h0 j hz]
      · have h : L.sup' hL (fun j => b j / a j) ≤ b j / a j :=
          Finset.sup'_le hL _ fun j' hj' => hlu j j' hp (by simpa [L] using hj')
        rw [le_div_iff₀ hp] at h
        linarith
    · by_cases hU : U.Nonempty
      · refine ⟨U.inf' hU fun j => b j / a j, fun j => ?_⟩
        rcases lt_trichotomy (a j) 0 with hn | hz | hp
        · exact absurd ⟨j, by simp [L, hn]⟩ hL
        · simp [hz, h0 j hz]
        · have h := Finset.inf'_le (fun j => b j / a j) (show j ∈ U by simp [U, hp])
          rw [le_div_iff₀ hp] at h
          linarith
      · refine ⟨0, fun j => ?_⟩
        rcases lt_trichotomy (a j) 0 with hn | hz | hp
        · exact absurd ⟨j, by simp [L, hn]⟩ hL
        · simp [hz, h0 j hz]
        · exact absurd ⟨j, by simp [U, hp]⟩ hU

/-- Solvability of finitely many measurable one-variable constraints is a measurable event. -/
lemma measurableSet_exists_affine {β ι : Type*} [MeasurableSpace β] [Fintype ι]
    (a b : ι → β → ℝ) (ha : ∀ j, Measurable (a j)) (hb : ∀ j, Measurable (b j)) :
    MeasurableSet {q | ∃ c : ℝ, ∀ j, a j q * c ≤ b j q} := by
  have he : {q | ∃ c : ℝ, ∀ j, a j q * c ≤ b j q} =
      (⋂ j, ({q | a j q = 0}ᶜ ∪ {q | 0 ≤ b j q})) ∩
        ⋂ j, ⋂ j', ({q | 0 < a j q}ᶜ ∪ ({q | a j' q < 0}ᶜ ∪
          {q | b j' q / a j' q ≤ b j q / a j q})) := by
    ext q
    simp only [mem_ofPred_eq, exists_affine_iff, mem_inter_iff, mem_iInter, mem_union,
      mem_compl_iff, imp_iff_not_or]
  rw [he]
  refine (MeasurableSet.iInter fun j => ?_).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun j' => ?_)
  · exact (measurableSet_eq_fun (ha j) measurable_const).compl.union
      (measurableSet_le measurable_const (hb j))
  · exact (measurableSet_lt measurable_const (ha j)).compl.union
      ((measurableSet_lt (ha j') measurable_const).compl.union
        (measurableSet_le ((hb j').div (ha j')) ((hb j).div (ha j))))

/-! ### The segment copy of three points -/

variable {m : ℕ} (K : Sides m)

/-- The tangent of side `k`: its normal turned through `90°`. -/
def tang (k : Fin m) : ℝ × ℝ := (-(K.u k).2, (K.u k).1)

/-- The hypotheses on an ordered pair of parallel sides `k, k̄`. -/
structure ParPair (k kb : Fin m) : Prop where
  unit : (K.u k).1 ^ 2 + (K.u k).2 ^ 2 = 1
  par : K.u kb = -K.u k
  width : 0 < K.h k + K.h kb
  trans : ∃ j, 0 < dot (K.u j) (tang K k)

variable (k kb : Fin m)

/-- The tight matrix of two points on side `k` and one on side `k̄`, in the unknowns
`(ε, w, Θ)` with `w = C · u k`. -/
def segMat (x : Fin 3 → Pt m) : Matrix (Fin 3) (Fin 3) ℝ :=
  segmentMatrix (K.h k) (K.h kb) (x 0).2.1 (x 1).2.1 (x 2).2.1

/-- The solution `(ε, w, Θ)` of the three tight equations. -/
noncomputable def segVec (x : Fin 3 → Pt m) : Fin 3 → ℝ :=
  (segMat K k kb x)⁻¹ *ᵥ (fun r => -(x r).2.2)

/-- The copy with scale `v 0`, normal translation `v 1` along `u k`, tilt `v 2`, and chord
position `c` along the tangent of side `k`. -/
def segCopy (v : Fin 3 → ℝ) (c : ℝ) : Copy :=
  chordCopy (v 0, (v 1 * (K.u k).1, v 1 * (K.u k).2), v 2) (tang K k) c

/-- Two points on side `k`, one on side `k̄`, positions `s₀ < -s₂ < s₁` (KKT). -/
def SegGood (x : Fin 3 → Pt m) : Prop :=
  (x 0).1 = k ∧ (x 1).1 = k ∧ (x 2).1 = kb ∧ (x 0).2.1 < -(x 2).2.1 ∧ -(x 2).2.1 < (x 1).2.1

/-- Chord positions at which the copy fits and its lines stay below the depth cutoff. -/
def chordSet (T : ℝ) (v : Fin 3 → ℝ) : Set ℝ :=
  {c | Fits K (segCopy K k v c) ∧ Below K T (segCopy K k v c)}

/-- Chord positions at which the copy fits (no cutoff). -/
def fitChord (v : Fin 3 → ℝ) : Set ℝ := {c | Fits K (segCopy K k v c)}

/-- The segment event for three points `x` and a configuration `μ`. -/
def SegEvent (T : ℝ) (x : Fin 3 → Pt m) (μ : Multiset (Pt m)) : Prop :=
  SegGood k kb x ∧
    ∃ c ∈ chordSet K k T (segVec K k kb x), Feasible K μ (segCopy K k (segVec K k kb x) c)

variable {K k kb}

lemma segCopy_fst (v : Fin 3 → ℝ) (c : ℝ) : (segCopy K k v c).1 = v 0 := rfl

lemma dot_u_tang : dot (K.u k) (tang K k) = 0 := by
  simp only [dot, tang]; ring

lemma ParPair.dot_kb (hP : ParPair K k kb) : dot (K.u kb) (tang K k) = 0 := by
  rw [hP.par]; simp only [dot, tang, Prod.fst_neg, Prod.snd_neg]; ring

lemma ParPair.ne (hP : ParPair K k kb) : k ≠ kb := by
  intro h
  have hu := hP.par
  rw [← h] at hu
  have h1 : (K.u k).1 = 0 := by
    have := congrArg Prod.fst hu; simp only [Prod.fst_neg] at this; linarith
  have h2 : (K.u k).2 = 0 := by
    have := congrArg Prod.snd hu; simp only [Prod.snd_neg] at this; linarith
  have := hP.unit
  rw [h1, h2] at this
  norm_num at this

lemma gx_segCopy_k (hP : ParPair K k kb) (v : Fin 3 → ℝ) (c : ℝ) (p : Pt m) (hp : p.1 = k) :
    gx K (segCopy K k v c) p = K.h k * v 0 + v 1 - p.2.1 * v 2 + p.2.2 := by
  have hu := hP.unit
  obtain ⟨i, s, D⟩ := p
  simp only at hp
  subst hp
  simp only [gx, segCopy, chordCopy, Hs, dot, tang]
  linear_combination v 1 * hu

lemma gx_segCopy_kb (hP : ParPair K k kb) (v : Fin 3 → ℝ) (c : ℝ) (p : Pt m) (hp : p.1 = kb) :
    gx K (segCopy K k v c) p = K.h kb * v 0 - v 1 - p.2.1 * v 2 + p.2.2 := by
  have hu := hP.unit
  obtain ⟨i, s, D⟩ := p
  simp only at hp
  subst hp
  simp only [gx, segCopy, chordCopy, Hs, dot, tang, hP.par, Prod.fst_neg, Prod.snd_neg]
  linear_combination -(v 1 * hu)

lemma SegGood.lt {x : Fin 3 → Pt m} (hx : SegGood k kb x) : (x 0).2.1 < (x 1).2.1 := hx.2.2.2.1.trans hx.2.2.2.2

lemma gx_segCopy (hP : ParPair K k kb) {x : Fin 3 → Pt m} (hx : SegGood k kb x)
    (v : Fin 3 → ℝ) (c : ℝ) (r : Fin 3) :
    gx K (segCopy K k v c) (x r) = (segMat K k kb x *ᵥ v) r + (x r).2.2 := by
  match r with
  | 0 =>
    rw [gx_segCopy_k hP v c _ hx.1]
    simp [segMat, segmentMatrix, mulVec, dotProduct, Fin.sum_univ_three]; ring
  | 1 =>
    rw [gx_segCopy_k hP v c _ hx.2.1]
    simp [segMat, segmentMatrix, mulVec, dotProduct, Fin.sum_univ_three]; ring
  | 2 =>
    rw [gx_segCopy_kb hP v c _ hx.2.2.1]
    simp [segMat, segmentMatrix, mulVec, dotProduct, Fin.sum_univ_three]; ring

lemma segMat_det_ne (hP : ParPair K k kb) {x : Fin 3 → Pt m} (hx : SegGood k kb x) :
    (segMat K k kb x).det ≠ 0 :=
  segmentMatrix_nonsingular _ _ _ _ _ hx.lt hP.width

/-- The three points are tight at every copy of their chord. -/
lemma segCopy_tight (hP : ParPair K k kb) {x : Fin 3 → Pt m} (hx : SegGood k kb x)
    (c : ℝ) (r : Fin 3) : gx K (segCopy K k (segVec K k kb x) c) (x r) = 0 := by
  rw [gx_segCopy hP hx, segVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (segMat_det_ne hP hx)), Matrix.one_mulVec]
  ring

/-- **The segment certificate.** Positive multipliers with `∑ μᵣ gₓᵣ(z) = ε(z) + ∑ μᵣ Dᵣ` for
every copy `z` (`kkt_segment_iff`). -/
lemma seg_certificate (hP : ParPair K k kb) {x : Fin 3 → Pt m} (hx : SegGood k kb x) :
    ∃ μ : Fin 3 → ℝ, (∀ r, 0 < μ r) ∧
      ∀ z : Copy, ∑ r, μ r * gx K z (x r) = z.1 + ∑ r, μ r * (x r).2.2 := by
  obtain ⟨μ₁, μ₂, _, h1, h2, h3, rfl, hw, hs⟩ :=
    (kkt_segment_iff (s₃ := (x 2).2.1) hx.lt hP.width).mpr ⟨hx.2.2.2.1, hx.2.2.2.2⟩
  refine ⟨![μ₁, μ₂, μ₁ + μ₂], fun r => by fin_cases r <;> simpa, fun z => ?_⟩
  have e0 : gx K z (x 0) = z.1 * K.h k + dot z.2.1 (K.u k) - z.2.2 * (x 0).2.1 + (x 0).2.2 := by
    simp only [gx, Hs, hx.1]
  have e1 : gx K z (x 1) = z.1 * K.h k + dot z.2.1 (K.u k) - z.2.2 * (x 1).2.1 + (x 1).2.2 := by
    simp only [gx, Hs, hx.2.1]
  have e2 : gx K z (x 2) = z.1 * K.h kb - dot z.2.1 (K.u k) - z.2.2 * (x 2).2.1 + (x 2).2.2 := by
    simp only [gx, Hs, hx.2.2.1, hP.par, dot, Prod.fst_neg, Prod.snd_neg]; ring
  simp only [Fin.sum_univ_three, e0, e1, e2, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination z.1 * hw - z.2.2 * hs

/-- Every copy feasible at the three points has scale at least that of the chord. Equality
forces all three points to be tight. -/
lemma seg_optimal (hP : ParPair K k kb) {x : Fin 3 → Pt m} (hx : SegGood k kb x)
    (z : Copy) (hz : ∀ r, 0 ≤ gx K z (x r)) :
    segVec K k kb x 0 ≤ z.1 ∧ (z.1 = segVec K k kb x 0 → ∀ r, gx K z (x r) = 0) := by
  obtain ⟨μ, hμ, hcert⟩ := seg_certificate hP hx
  have h0 := hcert (segCopy K k (segVec K k kb x) 0)
  simp only [segCopy_tight hP hx, mul_zero, Finset.sum_const_zero, segCopy_fst] at h0
  have hz' := hcert z
  have hnn : ∀ r ∈ Finset.univ, 0 ≤ μ r * gx K z (x r) :=
    fun r _ => mul_nonneg (hμ r).le (hz r)
  have hs := Finset.sum_nonneg hnn
  refine ⟨by linarith, fun he r => ?_⟩
  have hsum : ∑ r, μ r * gx K z (x r) = 0 := by linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum r (Finset.mem_univ r)
  exact (mul_eq_zero.mp this).resolve_left (hμ r).ne'

lemma gx_segCopy_c (v : Fin 3 → ℝ) (c : ℝ) (p : Pt m) :
    gx K (segCopy K k v c) p = gx K (segCopy K k v 0) p + c * dot (K.u p.1) (tang K k) := by
  simp only [gx, segCopy, chordCopy, Hs, dot]; ring

lemma Hs_segCopy_c (v : Fin 3 → ℝ) (c : ℝ) (i : Fin m) :
    Hs K (segCopy K k v c) i = Hs K (segCopy K k v 0) i + c * dot (K.u i) (tang K k) := by
  simp only [segCopy, chordCopy, Hs, dot]; ring

/-- On sides `k` and `k̄` the chord position does not matter. -/
lemma gx_segCopy_side (hP : ParPair K k kb) (v : Fin 3 → ℝ) (c : ℝ) (p : Pt m)
    (hp : p.1 = k ∨ p.1 = kb) : gx K (segCopy K k v c) p = gx K (segCopy K k v 0) p := by
  rw [gx_segCopy_c]
  rcases hp with hp | hp
  · rw [hp, dot_u_tang, mul_zero, add_zero]
  · rw [hp, hP.dot_kb, mul_zero, add_zero]

variable (K k kb)

/-- The copy at chord position `0`, used for the null event of an extra tight point. -/
noncomputable def segBase (x : Fin 3 → Pt m) : Copy := segCopy K k (segVec K k kb x) 0

/-- A segment candidate among the sampled points, as an ordered triple. -/
def SegCand {n : ℕ} (T : ℝ) (y : Fin n → Pt m) (i : Fin 3 ↪ Fin n) : Prop :=
  SegEvent K k kb T (y ∘ i) (PoissonPP.config y)

def HasSegCand (T : ℝ) (ω : PoissonPP.Sample (Pt m)) : Prop :=
  ∃ i : Fin 3 ↪ Fin ω.1, SegCand K k kb T ω.2 i

variable {K k kb}

def appendEmb3 {n : ℕ} (i : Fin 3 ↪ Fin n) (t : Fin n) (ht : t ∉ Set.range i) :
    Fin 4 ↪ Fin n where
  toFun := Fin.lastCases t i
  inj' := by
    intro a b h
    cases a using Fin.lastCases <;> cases b using Fin.lastCases
    · rfl
    · simp at h
      exact False.elim (ht ⟨_, h.symm⟩)
    · simp at h
      exact False.elim (ht ⟨_, h⟩)
    · simp at h
      exact congrArg Fin.castSucc h

lemma seg_tight_in_range {n : ℕ} (y : Fin n → Pt m)
    (hbad : ¬ BadExtra K (segBase K k kb) ⟨n, y⟩) (i : Fin 3 ↪ Fin n) (t : Fin n)
    (ht : gx K (segBase K k kb (y ∘ i)) (y t) = 0) : t ∈ Set.range i := by
  by_contra h
  apply hbad
  refine ⟨appendEmb3 i t h, ?_⟩
  have hl : appendEmb3 i t h (Fin.last 3) = t := by
    change Fin.lastCases t (fun r => i r) (Fin.last 3) = t
    simp only [Fin.lastCases_last]
  have hf : (fun r : Fin 3 => (y ∘ appendEmb3 i t h) ((Fin.last 3).succAbove r)) = y ∘ i := by
    funext r
    change y (Fin.lastCases t i ((Fin.last 3).succAbove r)) = y (i r)
    rw [Fin.succAbove_last, Fin.lastCases_castSucc]
  change gx K (segBase K k kb _) ((y ∘ appendEmb3 i t h) (Fin.last 3)) = 0
  rw [hf]
  change gx K (segBase K k kb (y ∘ i)) (y (appendEmb3 i t h (Fin.last 3))) = 0
  rw [hl]
  exact ht

/-- Two good triples with the same points are the same ordered triple: the point on `k̄` is
last, and the two points on `k` are ordered by position. -/
lemma seg_embedding_eq (hk : k ≠ kb) {n : ℕ} (y : Fin n → Pt m) (i j : Fin 3 ↪ Fin n)
    (hi : SegGood k kb (y ∘ i)) (hj : SegGood k kb (y ∘ j)) (h : ∀ r, ∃ r', i r = j r') :
    i = j := by
  have a0 : (y (i 0)).1 = k := hi.1
  have a1 : (y (i 1)).1 = k := hi.2.1
  have a2 : (y (i 2)).1 = kb := hi.2.2.1
  have b0 : (y (j 0)).1 = k := hj.1
  have b1 : (y (j 1)).1 = k := hj.2.1
  have b2 : (y (j 2)).1 = kb := hj.2.2.1
  have ai : (y (i 0)).2.1 < (y (i 1)).2.1 := hi.lt
  have bj : (y (j 0)).2.1 < (y (j 1)).2.1 := hj.lt
  have side : ∀ {r r'}, i r = j r' → (y (i r)).1 = (y (j r')).1 := fun h => by rw [h]
  have pos : ∀ {r r'}, i r = j r' → (y (i r)).2.1 = (y (j r')).2.1 := fun h => by rw [h]
  have e2 : i 2 = j 2 := by
    obtain ⟨r', hr⟩ := h 2
    match r', hr with
    | 0, hr => have := side hr; rw [a2, b0] at this; exact absurd this.symm hk
    | 1, hr => have := side hr; rw [a2, b1] at this; exact absurd this.symm hk
    | 2, hr => exact hr
  have e0 : i 0 = j 0 := by
    obtain ⟨r', hr⟩ := h 0
    match r', hr with
    | 0, hr => exact hr
    | 1, hr =>
      obtain ⟨r'', hr'⟩ := h 1
      match r'', hr' with
      | 0, hr' => have := pos hr; have := pos hr'; linarith
      | 1, hr' => exact absurd (i.injective (hr.trans hr'.symm)) (by decide)
      | 2, hr' => exact absurd (i.injective (hr'.trans e2.symm)) (by decide)
    | 2, hr => exact absurd (i.injective (hr.trans e2.symm)) (by decide)
  have e1 : i 1 = j 1 := by
    obtain ⟨r', hr⟩ := h 1
    match r', hr with
    | 0, hr => exact absurd (i.injective (hr.trans e0.symm)) (by decide)
    | 1, hr => exact hr
    | 2, hr => exact absurd (i.injective (hr.trans e2.symm)) (by decide)
  apply Function.Embedding.ext
  intro r
  match r with
  | 0 => exact e0
  | 1 => exact e1
  | 2 => exact e2

/-- **At most one segment candidate**, outside the null event of an extra tight point. -/
lemma segCand_unique (hP : ParPair K k kb) {n : ℕ} (T : ℝ) (y : Fin n → Pt m)
    (hbad : ¬ BadExtra K (segBase K k kb) ⟨n, y⟩) (i j : Fin 3 ↪ Fin n)
    (hi : SegCand K k kb T y i) (hj : SegCand K k kb T y j) : i = j := by
  obtain ⟨hgi, ci, -, hfi⟩ := hi
  obtain ⟨hgj, cj, -, hfj⟩ := hj
  have hfi' := (feasible_config_iff K y _).mp hfi
  have hfj' := (feasible_config_iff K y _).mp hfj
  have h1 := seg_optimal hP hgi _ (fun r => hfj' (i r))
  have h2 := seg_optimal hP hgj _ (fun r => hfi' (j r))
  rw [segCopy_fst] at h1 h2
  have he : segVec K k kb (y ∘ j) 0 = segVec K k kb (y ∘ i) 0 := le_antisymm h2.1 h1.1
  have hside : ∀ r, (y (i r)).1 = k ∨ (y (i r)).1 = kb := fun r => by
    match r with
    | 0 => exact Or.inl hgi.1
    | 1 => exact Or.inl hgi.2.1
    | 2 => exact Or.inr hgi.2.2.1
  apply seg_embedding_eq hP.ne y i j hgi hgj
  intro r
  have ht := h1.2 he r
  change gx K (segCopy K k (segVec K k kb (y ∘ j)) cj) (y (i r)) = 0 at ht
  rw [gx_segCopy_side hP _ _ _ (hside r)] at ht
  obtain ⟨r', hr'⟩ := seg_tight_in_range y hbad j (i r) ht
  exact ⟨r', hr'.symm⟩

/-! ### The constraint form and measurability -/

variable (K k)

/-- The four fitting/cutoff constraints of side `i` along the chord: coefficients of `c`. -/
noncomputable def fitCoef (p : Fin m × Fin 4) : ℝ :=
  ![dot (K.u p.1) (tang K k), dot (K.u p.1) (tang K k),
    -dot (K.u p.1) (tang K k), -dot (K.u p.1) (tang K k)] p.2

/-- The four fitting/cutoff constraints of side `i` along the chord: bounds. -/
noncomputable def fitBound (T : ℝ) (v : Fin 3 → ℝ) (p : Fin m × Fin 4) : ℝ :=
  ![v 2 * K.a p.1 - Hs K (segCopy K k v 0) p.1, v 2 * K.b p.1 - Hs K (segCopy K k v 0) p.1,
    T - v 2 * K.a p.1 + Hs K (segCopy K k v 0) p.1,
    T - v 2 * K.b p.1 + Hs K (segCopy K k v 0) p.1] p.2

/-- All constraints on the chord position: fitting, cutoff, and the sampled points. -/
noncomputable def segA {n : ℕ} (y : Fin n → Pt m) : (Fin m × Fin 4) ⊕ Fin n → ℝ
  | .inl p => fitCoef K k p
  | .inr r => -dot (K.u (y r).1) (tang K k)

noncomputable def segB {n : ℕ} (T : ℝ) (v : Fin 3 → ℝ) (y : Fin n → Pt m) :
    (Fin m × Fin 4) ⊕ Fin n → ℝ
  | .inl p => fitBound K k T v p
  | .inr r => gx K (segCopy K k v 0) (y r)

variable {K k}

lemma segCopy_tilt (v : Fin 3 → ℝ) (c : ℝ) : (segCopy K k v c).2.2 = v 2 := rfl

lemma mem_chordSet_iff (T : ℝ) (v : Fin 3 → ℝ) (c : ℝ) :
    c ∈ chordSet K k T v ↔ ∀ p, fitCoef K k p * c ≤ fitBound K k T v p := by
  simp only [chordSet, mem_ofPred_eq, Fits, Below, Prod.forall, Hs_segCopy_c v c, segCopy_tilt]
  constructor
  · rintro ⟨hf, hb⟩ i l
    have h1 := le_min_iff.mp (hf i)
    have h2 := max_le_iff.mp (sub_le_iff_le_add.mp (hb i))
    fin_cases l <;> simp [fitCoef, fitBound] <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · intro h
    refine ⟨fun i => le_min_iff.mpr ⟨?_, ?_⟩,
      fun i => sub_le_iff_le_add.mpr (max_le_iff.mpr ⟨?_, ?_⟩)⟩
    · have := h i 0; simp [fitCoef, fitBound] at this; linarith
    · have := h i 1; simp [fitCoef, fitBound] at this; linarith
    · have := h i 2; simp [fitCoef, fitBound] at this; linarith
    · have := h i 3; simp [fitCoef, fitBound] at this; linarith

lemma feasible_segCopy_iff {n : ℕ} (y : Fin n → Pt m) (v : Fin 3 → ℝ) (c : ℝ) :
    Feasible K (PoissonPP.config y) (segCopy K k v c) ↔
      ∀ r, -dot (K.u (y r).1) (tang K k) * c ≤ gx K (segCopy K k v 0) (y r) := by
  rw [feasible_config_iff]
  refine forall_congr' fun r => ?_
  rw [gx_segCopy_c]
  constructor <;> intro h <;> linarith

/-- Some chord position fits, stays below the cutoff, and is feasible: a finite system. -/
lemma chord_feasible_affine {n : ℕ} (T : ℝ) (v : Fin 3 → ℝ) (y : Fin n → Pt m) :
    (∃ c ∈ chordSet K k T v, Feasible K (PoissonPP.config y) (segCopy K k v c)) ↔
      ∃ c, ∀ j, segA K k y j * c ≤ segB K k T v y j := by
  refine exists_congr fun c => ?_
  rw [Sum.forall, mem_chordSet_iff, feasible_segCopy_iff]
  rfl

lemma measurable_tang_dot : Measurable (fun p : Pt m => dot (K.u p.1) (tang K k)) :=
  (measurable_of_countable fun i => dot (K.u i) (tang K k)).comp measurable_fst

lemma measurable_segCopy : Measurable (fun q : (Fin 3 → ℝ) × ℝ => segCopy K k q.1 q.2) := by
  unfold segCopy chordCopy tang
  fun_prop

lemma measurable_segCopy_zero : Measurable (fun v : Fin 3 → ℝ => segCopy K k v 0) :=
  measurable_segCopy.comp (measurable_id.prodMk measurable_const)

lemma measurable_fitBound (T : ℝ) (p : Fin m × Fin 4) :
    Measurable (fun v : Fin 3 → ℝ => fitBound K k T v p) := by
  obtain ⟨i, l⟩ := p
  have hH : Measurable fun v : Fin 3 → ℝ => Hs K (segCopy K k v 0) i :=
    (measurable_Hs K i).comp measurable_segCopy_zero
  have h2 : Measurable (fun v : Fin 3 → ℝ => v 2) := measurable_pi_apply 2
  fin_cases l <;> simp [fitBound]
  · exact (h2.mul_const _).sub hH
  · exact (h2.mul_const _).sub hH
  · exact (measurable_const.sub (h2.mul_const _)).add hH
  · exact (measurable_const.sub (h2.mul_const _)).add hH

variable (K k kb) in
lemma measurable_segMat : Measurable (segMat K k kb) := by
  apply Measurable.of_eval_matrix
  intro r c
  fin_cases r <;> fin_cases c <;> simp [segMat, segmentMatrix] <;> fun_prop

lemma measurable_matrixInv3 : Measurable (fun A : Matrix (Fin 3) (Fin 3) ℝ => A⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

variable (K k kb) in
lemma measurable_segVec : Measurable (segVec K k kb) := by
  have hI := measurable_matrixInv3.comp (measurable_segMat K k kb)
  apply Measurable.of_eval
  intro c
  unfold segVec Matrix.mulVec dotProduct
  exact Finset.measurable_sum _ fun r _ =>
    (hI.eval_matrix).mul (((measurable_snd.comp measurable_snd).comp
      (measurable_pi_apply r)).neg)

variable (K k kb) in
lemma measurable_segBase : Measurable (segBase K k kb) :=
  measurable_segCopy_zero.comp (measurable_segVec K k kb)

variable (k kb) in
lemma measurableSet_SegGood : MeasurableSet {x : Fin 3 → Pt m | SegGood k kb x} := by
  have hi : ∀ q : Fin 3, Measurable fun x : Fin 3 → Pt m => (x q).1 :=
    fun q => measurable_fst.comp (measurable_pi_apply q)
  have hs : ∀ q : Fin 3, Measurable fun x : Fin 3 → Pt m => (x q).2.1 :=
    fun q => (measurable_fst.comp measurable_snd).comp (measurable_pi_apply q)
  exact (hi 0 (measurableSet_singleton k)).inter ((hi 1 (measurableSet_singleton k)).inter
    ((hi 2 (measurableSet_singleton kb)).inter ((measurableSet_lt (hs 0) (hs 2).neg).inter
      (measurableSet_lt (hs 2).neg (hs 1)))))

lemma measurableSet_chordFeasible (T : ℝ) {β : Type*} [MeasurableSpace β] (n : ℕ)
    (V : β → Fin 3 → ℝ) (Y : β → Fin n → Pt m) (hV : Measurable V) (hY : Measurable Y) :
    MeasurableSet {q | ∃ c ∈ chordSet K k T (V q),
      Feasible K (PoissonPP.config (Y q)) (segCopy K k (V q) c)} := by
  simp_rw [chord_feasible_affine]
  apply measurableSet_exists_affine (fun j q => segA K k (Y q) j) (fun j q => segB K k T (V q) (Y q) j)
  · intro j
    rcases j with p | r
    · exact measurable_const
    · exact (measurable_tang_dot.comp ((measurable_pi_apply r).comp hY)).neg
  · intro j
    rcases j with p | r
    · exact (measurable_fitBound T p).comp hV
    · exact (measurable_gx_joint K).comp ((measurable_segCopy_zero.comp hV).prodMk
        ((measurable_pi_apply r).comp hY))

/-! ### The candidate count is the candidate probability -/

variable (K k kb) in
lemma measurableSet_SegCand {n : ℕ} (T : ℝ) (i : Fin 3 ↪ Fin n) :
    MeasurableSet {y : Fin n → Pt m | SegCand K k kb T y i} := by
  have hs : Measurable (fun y : Fin n → Pt m => y ∘ i) :=
    Measurable.of_eval fun r => measurable_pi_apply (i r)
  exact ((measurableSet_SegGood k kb).preimage hs).inter
    (measurableSet_chordFeasible T n (fun y => segVec K k kb (y ∘ i)) id
      ((measurable_segVec K k kb).comp hs) measurable_id)

variable (K k kb) in
lemma measurableSet_HasSegCand (T : ℝ) : MeasurableSet {ω | HasSegCand K k kb T ω} := by
  apply PoissonPP.measurableSet_sample
  intro n
  change MeasurableSet {y : Fin n → Pt m | ∃ i : Fin 3 ↪ Fin n, SegCand K k kb T y i}
  simp only [ofPred_exists]
  exact MeasurableSet.iUnion fun i => measurableSet_SegCand K k kb T i

variable (K k kb) in
noncomputable def sampleSegCount (T : ℝ) (ω : PoissonPP.Sample (Pt m)) : ℝ≥0∞ :=
  ∑ i : Fin 3 ↪ Fin ω.1, {y | SegCand K k kb T y i}.indicator (1 : (Fin ω.1 → Pt m) → ℝ≥0∞) ω.2

variable (K k kb) in
lemma measurable_sampleSegCount (T : ℝ) : Measurable (sampleSegCount K k kb T) := by
  intro S hS
  apply PoissonPP.measurableSet_sample
  intro n
  exact (Finset.measurable_sum (s := Finset.univ) fun i _ =>
    measurable_one.indicator (measurableSet_SegCand K k kb T i)) hS

lemma sampleSegCount_eq (hP : ParPair K k kb) (T : ℝ) (ω : PoissonPP.Sample (Pt m))
    (hbad : ¬ BadExtra K (segBase K k kb) ω) :
    sampleSegCount K k kb T ω = {ω | HasSegCand K k kb T ω}.indicator 1 ω := by
  rcases ω with ⟨n, y⟩
  by_cases hy : HasSegCand K k kb T ⟨n, y⟩
  · obtain ⟨i, hi⟩ := hy
    rw [indicator_of_mem (show (⟨n, y⟩ : PoissonPP.Sample (Pt m)) ∈
      {ω | HasSegCand K k kb T ω} from ⟨i, hi⟩)]
    unfold sampleSegCount
    rw [Finset.sum_eq_single i]
    · rw [indicator_of_mem (show y ∈ {y | SegCand K k kb T y i} from hi)]; rfl
    · intro j _ hji
      apply indicator_of_notMem
      intro hj
      exact hji (segCand_unique hP T y hbad j i hj hi)
    · simp
  · rw [indicator_of_notMem (show (⟨n, y⟩ : PoissonPP.Sample (Pt m)) ∉
      {ω | HasSegCand K k kb T ω} from hy)]
    apply Finset.sum_eq_zero
    intro i _
    apply indicator_of_notMem
    intro hi
    exact hy ⟨i, hi⟩

variable (K k kb) in
/-- The Mecke integrand: three points making a segment candidate with configuration `μ`. -/
noncomputable def segG (T : ℝ) (x : Fin 3 → Pt m) (μ : Multiset (Pt m)) : ℝ≥0∞ :=
  {p : (Fin 3 → Pt m) × Multiset (Pt m) | SegEvent K k kb T p.1 p.2}.indicator 1 (x, μ)

variable (K k kb) in
/-- The ordered three-point candidate count. -/
noncomputable def segOrderedCount (T : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, PoissonPP.w0 (Λ K T) / n.factorial *
    ∫⁻ y : Fin n → Pt m, ∑ i : Fin 3 ↪ Fin n, segG K k kb T (y ∘ i) (PoissonPP.rest y i)
      ∂(Measure.pi fun _ => Λ K T)

variable (K k kb) in
lemma measurable_segG_config (T : ℝ) (n : ℕ) :
    Measurable fun q : (Fin 3 → Pt m) × (Fin n → Pt m) =>
      segG K k kb T q.1 (PoissonPP.config q.2) := by
  have h1 : MeasurableSet {q : (Fin 3 → Pt m) × (Fin n → Pt m) | SegGood k kb q.1} :=
    (measurableSet_SegGood k kb).preimage measurable_fst
  have h2 : MeasurableSet {q : (Fin 3 → Pt m) × (Fin n → Pt m) |
      ∃ c ∈ chordSet K k T (segVec K k kb q.1),
        Feasible K (PoissonPP.config q.2) (segCopy K k (segVec K k kb q.1) c)} :=
    measurableSet_chordFeasible T n (fun q : (Fin 3 → Pt m) × (Fin n → Pt m) => segVec K k kb q.1)
      (fun q => q.2) ((measurable_segVec K k kb).comp measurable_fst) measurable_snd
  have hset : MeasurableSet {q : (Fin 3 → Pt m) × (Fin n → Pt m) |
      SegEvent K k kb T q.1 (PoissonPP.config q.2)} := h1.inter h2
  have he : (fun q : (Fin 3 → Pt m) × (Fin n → Pt m) =>
      segG K k kb T q.1 (PoissonPP.config q.2)) = {q : (Fin 3 → Pt m) × (Fin n → Pt m) |
      SegEvent K k kb T q.1 (PoissonPP.config q.2)}.indicator 1 := by
    funext q
    unfold segG
    by_cases h : SegEvent K k kb T q.1 (PoissonPP.config q.2)
    · rw [indicator_of_mem (show q ∈ {q : (Fin 3 → Pt m) × (Fin n → Pt m) |
          SegEvent K k kb T q.1 (PoissonPP.config q.2)} from h),
        indicator_of_mem (show (q.1, PoissonPP.config q.2) ∈
          {p : (Fin 3 → Pt m) × Multiset (Pt m) | SegEvent K k kb T p.1 p.2} from h)]; rfl
    · rw [indicator_of_notMem (show q ∉ {q : (Fin 3 → Pt m) × (Fin n → Pt m) |
          SegEvent K k kb T q.1 (PoissonPP.config q.2)} from h),
        indicator_of_notMem (show (q.1, PoissonPP.config q.2) ∉
          {p : (Fin 3 → Pt m) × Multiset (Pt m) | SegEvent K k kb T p.1 p.2} from h)]
  rw [he]
  exact measurable_one.indicator hset

lemma mem_rest_iff3 {n : ℕ} (y : Fin n → Pt m) (i : Fin 3 ↪ Fin n) (p : Pt m) :
    p ∈ PoissonPP.rest y i ↔ ∃ t, t ∉ Set.range i ∧ y t = p := by
  simp [PoissonPP.rest]

lemma seg_feasible_rest_iff (hP : ParPair K k kb) {n : ℕ} (y : Fin n → Pt m)
    (i : Fin 3 ↪ Fin n) (hx : SegGood k kb (y ∘ i)) (c : ℝ) :
    Feasible K (PoissonPP.rest y i) (segCopy K k (segVec K k kb (y ∘ i)) c) ↔
      Feasible K (PoissonPP.config y) (segCopy K k (segVec K k kb (y ∘ i)) c) := by
  rw [feasible_config_iff]
  constructor
  · intro h t
    by_cases ht : t ∈ Set.range i
    · obtain ⟨r, rfl⟩ := ht
      exact (segCopy_tight hP hx c r).ge
    · exact (gx_nonneg_iff K _ _).mpr (h _ ((mem_rest_iff3 y i _).mpr ⟨t, ht, rfl⟩))
  · intro h p hp
    obtain ⟨t, _, rfl⟩ := (mem_rest_iff3 y i p).mp hp
    exact (gx_nonneg_iff K _ _).mp (h t)

lemma segG_rest (hP : ParPair K k kb) {n : ℕ} (T : ℝ) (y : Fin n → Pt m)
    (i : Fin 3 ↪ Fin n) :
    segG K k kb T (y ∘ i) (PoissonPP.rest y i) = {y | SegCand K k kb T y i}.indicator 1 y := by
  have hiff : SegEvent K k kb T (y ∘ i) (PoissonPP.rest y i) ↔ SegCand K k kb T y i := by
    unfold SegCand SegEvent
    constructor
    · rintro ⟨hg, c, hc, hf⟩; exact ⟨hg, c, hc, (seg_feasible_rest_iff hP y i hg c).mp hf⟩
    · rintro ⟨hg, c, hc, hf⟩; exact ⟨hg, c, hc, (seg_feasible_rest_iff hP y i hg c).mpr hf⟩
  unfold segG
  by_cases h : SegCand K k kb T y i
  · rw [indicator_of_mem (show (y ∘ i, PoissonPP.rest y i) ∈
        {p : (Fin 3 → Pt m) × Multiset (Pt m) | SegEvent K k kb T p.1 p.2} from hiff.mpr h),
      indicator_of_mem (show y ∈ {y | SegCand K k kb T y i} from h)]; rfl
  · rw [indicator_of_notMem (show (y ∘ i, PoissonPP.rest y i) ∉
        {p : (Fin 3 → Pt m) × Multiset (Pt m) | SegEvent K k kb T p.1 p.2} from mt hiff.mp h),
      indicator_of_notMem (show y ∉ {y | SegCand K k kb T y i} from h)]

/-- Segment candidates occur at most once, outside a proved null event, so the ordered count
is the probability of the candidate event. -/
theorem segOrderedCount_eq_law (hP : ParPair K k kb) (T : ℝ) :
    segOrderedCount K k kb T = PoissonPP.law (Λ K T) {ω | HasSegCand K k kb T ω} := by
  have hae : ∀ᵐ ω ∂PoissonPP.law (Λ K T), ¬ BadExtra K (segBase K k kb) ω := by
    rw [ae_iff]
    simpa only [not_not] using badExtra_prob_zero K (segBase K k kb) (measurable_segBase K k kb) T
  rw [← lintegral_indicator_one (measurableSet_HasSegCand K k kb T)]
  calc segOrderedCount K k kb T
      = ∫⁻ ω, sampleSegCount K k kb T ω ∂PoissonPP.law (Λ K T) := by
        rw [PoissonPP.lintegral_law _ _ (measurable_sampleSegCount K k kb T)]
        unfold segOrderedCount sampleSegCount
        congr 1
        funext n
        congr 1
        apply lintegral_congr
        intro y
        exact Finset.sum_congr rfl fun i _ => segG_rest hP T y i
    _ = _ := lintegral_congr_ae (by
        filter_upwards [hae] with ω hω using sampleSegCount_eq hP T ω hω)

variable (K k kb) in
/-- **Three-point Mecke** for segment candidates. -/
theorem seg_mecke (T : ℝ) :
    segOrderedCount K k kb T =
      ∫⁻ x, PoissonPP.expect (Λ K T) (segG K k kb T x) ∂(Measure.pi fun _ : Fin 3 => Λ K T) :=
  PoissonPP.mecke (Λ K T) 3 (segG K k kb T) (measurable_segG_config K k kb T)

/-! ### The chord probability -/

variable (K k) in
/-- `S = ∑_{u_j · t > 0} L_j u_j · t`. -/
noncomputable def slopeSum : ℝ :=
  ∑ i ∈ positiveSides K (tang K k), (K.b i - K.a i) * dot (K.u i) (tang K k)

variable (K k) in
/-- The chord weight `e^{2ε} (1{chord ≠ ∅} + S · |chord|)`. -/
noncomputable def chordWeight (T : ℝ) (v : Fin 3 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (2 * v 0)) *
    ({v | (chordSet K k T v).Nonempty}.indicator 1 v +
      ENNReal.ofReal (slopeSum K k) * volume (chordSet K k T v))

/-- A nonempty solution set of finitely many constraints, with an upper and a lower bound
among them, is a closed interval. -/
lemma affine_eq_Icc {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (hne : {c | ∀ j, a j * c ≤ b j}.Nonempty) (hp : ∃ j, 0 < a j) (hn : ∃ j, a j < 0) :
    {c | ∀ j, a j * c ≤ b j} =
      Icc (sInf {c | ∀ j, a j * c ≤ b j}) (sSup {c | ∀ j, a j * c ≤ b j}) := by
  set S := {c : ℝ | ∀ j, a j * c ≤ b j} with hS
  have hcl : IsClosed S := by
    rw [hS, ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le (continuous_const.mul continuous_id) continuous_const
  obtain ⟨jp, hjp⟩ := hp
  obtain ⟨jn, hjn⟩ := hn
  have hA : BddAbove S := ⟨b jp / a jp, fun c hc => (le_div_iff₀ hjp).mpr (by linarith [hc jp])⟩
  have hB : BddBelow S :=
    ⟨b jn / a jn, fun c hc => (div_le_iff_of_neg hjn).mpr (by linarith [hc jn])⟩
  have hinf := hcl.csInf_mem hne hB
  have hsup := hcl.csSup_mem hne hA
  ext c
  constructor
  · intro hc; exact ⟨csInf_le hB hc, le_csSup hA hc⟩
  · rintro ⟨h1, h2⟩ j
    rcases le_total 0 (a j) with h | h
    · exact (mul_le_mul_of_nonneg_left h2 h).trans (hsup j)
    · exact (mul_le_mul_of_nonpos_left h1 h).trans (hinf j)

lemma ParPair.exists_neg (hP : ParPair K k kb) : ∃ j, dot (K.u j) (tang K k) < 0 := by
  by_contra h
  simp only [not_exists, not_lt] at h
  obtain ⟨j, hj⟩ := hP.trans
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ (K.b i - K.a i) * dot (K.u i) (tang K k) :=
    fun i _ => mul_nonneg (sub_nonneg.mpr (K.hab i).le) (h i)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (tangent_balance K (tang K k)) j
    (Finset.mem_univ j)
  have : 0 < (K.b j - K.a j) * dot (K.u j) (tang K k) := mul_pos (sub_pos.mpr (K.hab j)) hj
  linarith

lemma chordSet_eq_affine (T : ℝ) (v : Fin 3 → ℝ) :
    chordSet K k T v = {c | ∀ p, fitCoef K k p * c ≤ fitBound K k T v p} := by
  ext c; exact mem_chordSet_iff T v c

lemma chordSet_eq_Icc (hP : ParPair K k kb) (T : ℝ) (v : Fin 3 → ℝ)
    (hne : (chordSet K k T v).Nonempty) :
    chordSet K k T v = Icc (sInf (chordSet K k T v)) (sSup (chordSet K k T v)) := by
  rw [chordSet_eq_affine] at hne ⊢
  obtain ⟨jp, hjp⟩ := hP.trans
  obtain ⟨jn, hjn⟩ := hP.exists_neg
  exact affine_eq_Icc _ _ hne ⟨(jp, 0), by simpa [fitCoef] using hjp⟩
    ⟨(jn, 0), by simpa [fitCoef] using hjn⟩

/-- **The chord probability** in the model: with the three points fixed, some chord position
is feasible for the Poisson sample with probability `e^{2ε}(1{chord ≠ ∅} + S · |chord|)`. -/
theorem chord_prob (hP : ParPair K k kb) (T : ℝ) (v : Fin 3 → ℝ) :
    PoissonPP.law (Λ K T) {ω | ∃ c ∈ chordSet K k T v,
      Feasible K (PoissonPP.config ω.2) (segCopy K k v c)} = chordWeight K k T v := by
  by_cases hne : (chordSet K k T v).Nonempty
  · have hI := chordSet_eq_Icc hP T v hne
    set α := sInf (chordSet K k T v)
    set β := sSup (chordSet K k T v)
    have hαβ : α ≤ β := by
      obtain ⟨c, hc⟩ := hne; rw [hI] at hc; exact hc.1.trans hc.2
    have hE : ∀ y ∈ Icc α β, Fits K (segCopy K k v y) := fun y hy => (hI ▸ hy).1
    have hT : ∀ y ∈ Icc α β, Below K T (segCopy K k v y) := fun y hy => (hI ▸ hy).2
    have hp : (PoissonPP.law (Λ K T)).real
        {ω | ∃ c ∈ Icc α β, Feasible K (PoissonPP.config ω.2) (segCopy K k v c)} =
        Real.exp (2 * v 0) * (1 + slopeSum K k * (β - α)) :=
      chord_feasible_prob K T _ (tang K k) α β hαβ hE hT
    have hS : 0 ≤ slopeSum K k := tangent_positiveSlope_nonneg K _
    unfold chordWeight
    rw [indicator_of_mem (show v ∈ {v | (chordSet K k T v).Nonempty} from hne), hI,
      ← ofReal_measureReal, hp, Real.volume_Icc, Pi.one_apply,
      ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_add zero_le_one (mul_nonneg hS (sub_nonneg.mpr hαβ)),
      ENNReal.ofReal_one, ENNReal.ofReal_mul hS]
  · have he : {ω : PoissonPP.Sample (Pt m) | ∃ c ∈ chordSet K k T v,
        Feasible K (PoissonPP.config ω.2) (segCopy K k v c)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨c, hc, -⟩
      exact hne ⟨c, hc⟩
    rw [not_nonempty_iff_eq_empty] at hne
    unfold chordWeight
    rw [he, measure_empty, indicator_of_notMem (show v ∉ {v | (chordSet K k T v).Nonempty} by
      simp [hne]), hne, measure_empty, mul_zero, add_zero, mul_zero]

variable (K k kb) in
/-- The weight of three points: the KKT condition times the chord weight of their copy. -/
noncomputable def segWeight (T : ℝ) (x : Fin 3 → Pt m) : ℝ≥0∞ :=
  {x | SegGood k kb x}.indicator (fun x => chordWeight K k T (segVec K k kb x)) x

lemma expect_segG (hP : ParPair K k kb) (T : ℝ) (x : Fin 3 → Pt m) :
    PoissonPP.expect (Λ K T) (segG K k kb T x) = segWeight K k kb T x := by
  by_cases hx : SegGood k kb x
  · have hG : segG K k kb T x = fun μ => {μ | ∃ c ∈ chordSet K k T (segVec K k kb x),
        Feasible K μ (segCopy K k (segVec K k kb x) c)}.indicator 1 μ := by
      funext μ
      unfold segG
      by_cases h : ∃ c ∈ chordSet K k T (segVec K k kb x),
          Feasible K μ (segCopy K k (segVec K k kb x) c)
      · rw [indicator_of_mem (show (x, μ) ∈ {p : (Fin 3 → Pt m) × Multiset (Pt m) |
          SegEvent K k kb T p.1 p.2} from ⟨hx, h⟩), indicator_of_mem (show μ ∈ {μ |
          ∃ c ∈ chordSet K k T (segVec K k kb x),
            Feasible K μ (segCopy K k (segVec K k kb x) c)} from h)]; rfl
      · rw [indicator_of_notMem (show (x, μ) ∉ {p : (Fin 3 → Pt m) × Multiset (Pt m) |
          SegEvent K k kb T p.1 p.2} from fun h' => h h'.2), indicator_of_notMem (show μ ∉ {μ |
          ∃ c ∈ chordSet K k T (segVec K k kb x),
            Feasible K μ (segCopy K k (segVec K k kb x) c)} from h)]
    rw [hG, segWeight, indicator_of_mem (show x ∈ {x | SegGood k kb x} from hx),
      ← chord_prob hP T]
    exact (PoissonPP.law_prob (Λ K T) (fun μ => ∃ c ∈ chordSet K k T (segVec K k kb x),
      Feasible K μ (segCopy K k (segVec K k kb x) c)) (fun n =>
        measurableSet_chordFeasible T n (fun _ => segVec K k kb x) id measurable_const
          measurable_id)).symm
  · have hG : segG K k kb T x = fun _ => 0 := by
      funext μ
      exact indicator_of_notMem (show (x, μ) ∉ {p : (Fin 3 → Pt m) × Multiset (Pt m) |
        SegEvent K k kb T p.1 p.2} from fun h => hx h.1) _
    rw [hG, PoissonPP.expect_const, segWeight,
      indicator_of_notMem (show x ∉ {x | SegGood k kb x} from hx)]

/-- The segment-candidate probability as a three-point intensity integral. -/
theorem seg_prob_weight (hP : ParPair K k kb) (T : ℝ) :
    PoissonPP.law (Λ K T) {ω | HasSegCand K k kb T ω} =
      ∫⁻ x, segWeight K k kb T x ∂(Measure.pi fun _ : Fin 3 => Λ K T) := by
  rw [← segOrderedCount_eq_law hP, seg_mecke]
  exact lintegral_congr fun x => expect_segG hP T x

/-! ### Positions, depths and the Jacobian -/

lemma pi_dirac_tuple_d {d : ℕ} (κ : Fin d → Fin m) :
    (Measure.pi fun r => Measure.dirac (κ r)) = Measure.dirac κ := by
  apply Measure.pi_eq
  intro S hS
  classical
  simp only [Measure.dirac_apply' _ (MeasurableSet.univ_pi hS),
    Measure.dirac_apply' _ (hS _), indicator_apply, Pi.one_apply, mem_univ_pi]
  by_cases h : ∀ r, κ r ∈ S r
  · simp [h]
  · push Not at h
    obtain ⟨r, hr⟩ := h
    rw [ite_eq_right (by simpa using not_forall.mpr ⟨r, hr⟩)]
    exact (Finset.prod_eq_zero (Finset.mem_univ r) (ite_eq_right hr)).symm

variable (K) in
lemma intensity_pi_eq_d {d : ℕ} (T : ℝ) :
    (Measure.pi fun _ : Fin d => Λ K T) =
      ∑ κ : Fin d → Fin m, Measure.pi fun r =>
        (Measure.dirac (κ r)).prod
          (volume.restrict (Icc (K.a (κ r)) (K.b (κ r)) ×ˢ Icc (0 : ℝ) T)) := by
  apply Measure.pi_eq
  intro S hS
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp_rw [Measure.pi_pi, Λ, Measure.coe_finsetSum, Finset.sum_apply]
  exact (Fintype.prod_sum (fun (r : Fin d) (i : Fin m) =>
    ((Measure.dirac i).prod
      (volume.restrict (Icc (K.a i) (K.b i) ×ˢ Icc (0 : ℝ) T))) (S r))).symm

/-- Points from sides, positions and depths. -/
def ptsOf {d : ℕ} (κ : Fin d → Fin m) (s D : Fin d → ℝ) : Fin d → Pt m :=
  fun r => (κ r, s r, D r)

variable (K) in
/-- Separate side indices, positions and depths in the `d`-fold intensity. -/
lemma lintegral_intensity_positions_d {d : ℕ} (T : ℝ) (F : (Fin d → Pt m) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ x, F x ∂(Measure.pi fun _ : Fin d => Λ K T)) =
      ∑ κ : Fin d → Fin m, ∫⁻ s : Fin d → ℝ,
        ∫⁻ D : Fin d → ℝ, F (ptsOf κ s D)
          ∂(Measure.pi fun _ : Fin d => volume.restrict (Icc (0 : ℝ) T))
        ∂(Measure.pi fun r => volume.restrict (Icc (K.a (κ r)) (K.b (κ r)))) := by
  rw [intensity_pi_eq_d K T, lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro κ _
  have hρ : ∀ r : Fin d,
      volume.restrict (Icc (K.a (κ r)) (K.b (κ r)) ×ˢ Icc (0 : ℝ) T) =
        (volume.restrict (Icc (K.a (κ r)) (K.b (κ r)))).prod
          (volume.restrict (Icc (0 : ℝ) T)) := by
    intro r; rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  simp_rw [hρ]
  -- side indices
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin m) (ℝ × ℝ) (Fin d)
  have he := measurePreserving_arrowProdEquivProdArrow (Fin m) (ℝ × ℝ) (Fin d)
    (fun r => Measure.dirac (κ r))
    (fun r => (volume.restrict (Icc (K.a (κ r)) (K.b (κ r)))).prod
      (volume.restrict (Icc (0 : ℝ) T)))
  change MeasurePreserving e _ _ at he
  have h := he.lintegral_comp_emb e.measurableEmbedding (fun q => F (e.symm q))
  simp only [e.symm_apply_apply] at h
  have hm : Measurable (fun q => F (e.symm q)) := hF.comp e.symm.measurable
  rw [h, pi_dirac_tuple_d, lintegral_prod _ hm.aemeasurable, lintegral_dirac']
  swap
  · exact hm.lintegral_prod_right'
  -- positions and depths
  let e' := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin d)
  have he' := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin d)
    (fun r => volume.restrict (Icc (K.a (κ r)) (K.b (κ r))))
    (fun _ => volume.restrict (Icc (0 : ℝ) T))
  change MeasurePreserving e' _ _ at he'
  have hG : Measurable (fun p : Fin d → ℝ × ℝ => F (fun r => (κ r, p r))) := by
    apply hF.comp
    exact Measurable.of_eval fun r => measurable_const.prodMk (measurable_pi_apply r)
  have h' := he'.lintegral_comp_emb e'.measurableEmbedding
    (fun q => F (fun r => (κ r, (e'.symm q) r)))
  simp only [e'.symm_apply_apply] at h'
  have hm' : Measurable (fun q => F (fun r => (κ r, (e'.symm q) r))) :=
    hG.comp e'.symm.measurable
  change (∫⁻ p : Fin d → ℝ × ℝ, F (fun r => (κ r, p r)) ∂_) = _
  rw [h', lintegral_prod _ hm'.aemeasurable]
  rfl

lemma positions_ae_d {d : ℕ} (κ : Fin d → Fin m) :
    ∀ᵐ s : Fin d → ℝ ∂(Measure.pi fun r => volume.restrict (Icc (K.a (κ r)) (K.b (κ r)))),
      ∀ r, s r ∈ Icc (K.a (κ r)) (K.b (κ r)) := by
  rw [← Measure.restrict_pi_pi (fun _ : Fin d => (volume : Measure ℝ))]
  exact (ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Icc)).mono
    fun _ hs => mem_univ_pi.mp hs

variable (K k) in
lemma measurable_chordWeight (T : ℝ) : Measurable (chordWeight K k T) := by
  have hne : MeasurableSet {v : Fin 3 → ℝ | (chordSet K k T v).Nonempty} := by
    have he : {v : Fin 3 → ℝ | (chordSet K k T v).Nonempty} =
        {v | ∃ c : ℝ, ∀ p, fitCoef K k p * c ≤ fitBound K k T v p} := by
      ext v; simp only [mem_ofPred_eq, chordSet_eq_affine]; rfl
    rw [he]
    exact measurableSet_exists_affine (fun p _ => fitCoef K k p) (fun p v => fitBound K k T v p)
      (fun _ => measurable_const) (fun p => measurable_fitBound T p)
  have hS : MeasurableSet {q : (Fin 3 → ℝ) × ℝ | q.2 ∈ chordSet K k T q.1} :=
    ((measurableSet_Fits K).preimage measurable_segCopy).inter
      ((measurableSet_Below K T).preimage measurable_segCopy)
  have hvol : Measurable fun v : Fin 3 → ℝ => volume (chordSet K k T v) :=
    measurable_measure_prodMk_left hS
  unfold chordWeight
  exact (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
    (measurable_const.mul (measurable_pi_apply 0)))).mul
      ((measurable_one.indicator hne).add (measurable_const.mul hvol))

variable (K k kb) in
lemma measurable_segWeight (T : ℝ) : Measurable (segWeight K k kb T) :=
  ((measurable_chordWeight K k T).comp (measurable_segVec K k kb)).indicator
    (measurableSet_SegGood k kb)

variable (K k kb) in
/-- The position density of a segment candidate: KKT times the Jacobian
`(s₁ - s₀)(h_k + h_k̄)`. -/
noncomputable def segRow (s : Fin 3 → ℝ) : ℝ≥0∞ :=
  {s : Fin 3 → ℝ | s 0 < -s 2 ∧ -s 2 < s 1}.indicator
    (fun s => ENNReal.ofReal ((s 1 - s 0) * (K.h k + K.h kb))) s

variable (K k kb) in
lemma measurable_segRow : Measurable (segRow K k kb) := by
  have hs : MeasurableSet {s : Fin 3 → ℝ | s 0 < -s 2 ∧ -s 2 < s 1} :=
    (measurableSet_lt (measurable_pi_apply 0) (measurable_pi_apply 2).neg).inter
      (measurableSet_lt (measurable_pi_apply 2).neg (measurable_pi_apply 1))
  exact (ENNReal.measurable_ofReal.comp
    (((measurable_pi_apply 1).sub (measurable_pi_apply 0)).mul_const _)).indicator hs

variable (K k kb) in
/-- The segment position density `σ`-integral of Theorem 8. -/
noncomputable def segDensity : ℝ≥0∞ :=
  ∫⁻ s, segRow K k kb s
    ∂(Measure.pi fun r => volume.restrict (Icc (K.a (![k, k, kb] r)) (K.b (![k, k, kb] r))))

lemma chordWeight_nonempty {T : ℝ} {v : Fin 3 → ℝ} (h : chordWeight K k T v ≠ 0) :
    (chordSet K k T v).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  apply h
  unfold chordWeight
  rw [indicator_of_notMem (show v ∉ {v | (chordSet K k T v).Nonempty} by simp [hne]), hne,
    measure_empty, mul_zero, add_zero, mul_zero]

lemma segWeight_zero_of_ne (T : ℝ) (κ : Fin 3 → Fin m) (hκ : κ ≠ ![k, k, kb])
    (s D : Fin 3 → ℝ) : segWeight K k kb T (ptsOf κ s D) = 0 := by
  apply indicator_of_notMem
  rintro ⟨h0, h1, h2, -, -⟩
  apply hκ
  funext r
  match r with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2

/-- With a nonzero weight, the three tight points lie inside the truncated strips. -/
lemma seg_depths (hP : ParPair K k kb) (T : ℝ) (κ : Fin 3 → Fin m) (s D : Fin 3 → ℝ)
    (hs : ∀ r, s r ∈ Icc (K.a (κ r)) (K.b (κ r)))
    (h : segWeight K k kb T (ptsOf κ s D) ≠ 0) : ∀ r, D r ∈ Icc (0 : ℝ) T := by
  have hg : SegGood k kb (ptsOf κ s D) := by
    by_contra hg
    exact h (indicator_of_notMem (show ptsOf κ s D ∉ {x | SegGood k kb x} from hg) _)
  have hw : chordWeight K k T (segVec K k kb (ptsOf κ s D)) ≠ 0 := by
    rwa [segWeight, indicator_of_mem (show ptsOf κ s D ∈ {x | SegGood k kb x} from hg)] at h
  obtain ⟨c, hcF, hcB⟩ := chordWeight_nonempty hw
  intro r
  have ht := segCopy_tight hP hg c r
  set z := segCopy K k (segVec K k kb (ptsOf κ s D)) c
  have he : D r = z.2.2 * s r - Hs K z (κ r) := by
    unfold gx at ht
    change Hs K z (κ r) - z.2.2 * s r + D r = 0 at ht
    linarith
  rw [he]
  exact ⟨line_nonneg (hcF (κ r)) (hs r), below_line K T z hcB (κ r) (hs r)⟩

/-- The depth integral: the cutoff is redundant, and the depth-to-copy Jacobian is
`(s₁ - s₀)(h_k + h_k̄)`. -/
lemma seg_depth_integral (hP : ParPair K k kb) (T : ℝ) (s : Fin 3 → ℝ)
    (hs : ∀ r, s r ∈ Icc (K.a (![k, k, kb] r)) (K.b (![k, k, kb] r))) :
    (∫⁻ D, segWeight K k kb T (ptsOf ![k, k, kb] s D)
      ∂(Measure.pi fun _ : Fin 3 => volume.restrict (Icc (0 : ℝ) T))) =
        segRow K k kb s * ∫⁻ v, chordWeight K k T v := by
  have hrestrict : (∫⁻ D, segWeight K k kb T (ptsOf ![k, k, kb] s D)
      ∂(Measure.pi fun _ : Fin 3 => volume.restrict (Icc (0 : ℝ) T))) =
        ∫⁻ D, segWeight K k kb T (ptsOf ![k, k, kb] s D) := by
    rw [← Measure.restrict_pi_pi (fun _ : Fin 3 => (volume : Measure ℝ))
      (fun _ => Icc (0 : ℝ) T)]
    change (∫⁻ D in univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) T),
      segWeight K k kb T (ptsOf ![k, k, kb] s D)) = _
    rw [← lintegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc)]
    apply lintegral_congr
    intro D
    by_cases hD : D ∈ univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) T)
    · exact indicator_of_mem (f := fun D => segWeight K k kb T (ptsOf ![k, k, kb] s D)) hD
    · rw [indicator_of_notMem hD]
      by_contra hne
      exact hD (mem_univ_pi.mpr (seg_depths hP T _ s D hs (Ne.symm hne)))
  rw [hrestrict]
  by_cases h : s 0 < -s 2 ∧ -s 2 < s 1
  · have he : ∀ D : Fin 3 → ℝ, segWeight K k kb T (ptsOf ![k, k, kb] s D) =
        chordWeight K k T ((segmentMatrix (K.h k) (K.h kb) (s 0) (s 1) (s 2))⁻¹ *ᵥ (-D)) := by
      intro D
      rw [segWeight, indicator_of_mem (show ptsOf ![k, k, kb] s D ∈ {x | SegGood k kb x} from
        ⟨rfl, rfl, rfl, h.1, h.2⟩)]
      rfl
    simp_rw [he]
    rw [segment_lintegral_depths _ _ _ _ _ (h.1.trans h.2) hP.width _
      (measurable_chordWeight K k T), segRow,
      indicator_of_mem (show s ∈ {s : Fin 3 → ℝ | s 0 < -s 2 ∧ -s 2 < s 1} from h)]
  · have hz : ∀ D : Fin 3 → ℝ, segWeight K k kb T (ptsOf ![k, k, kb] s D) = 0 := by
      intro D
      apply indicator_of_notMem
      rintro ⟨-, -, -, h1, h2⟩
      exact h ⟨h1, h2⟩
    simp_rw [hz]
    rw [lintegral_zero, segRow,
      indicator_of_notMem (show s ∉ {s : Fin 3 → ℝ | s 0 < -s 2 ∧ -s 2 < s 1} from h), zero_mul]

/-- **The segment-candidate probability at cutoff `T`**: position density times the
chord-weight integral over `(ε, w, Θ)`. -/
theorem seg_count_factor (hP : ParPair K k kb) (T : ℝ) :
    PoissonPP.law (Λ K T) {ω | HasSegCand K k kb T ω} =
      segDensity K k kb * ∫⁻ v, chordWeight K k T v := by
  rw [seg_prob_weight hP, lintegral_intensity_positions_d K T _ (measurable_segWeight K k kb T),
    Finset.sum_eq_single ![k, k, kb]]
  · calc (∫⁻ s, ∫⁻ D, segWeight K k kb T (ptsOf ![k, k, kb] s D)
          ∂(Measure.pi fun _ : Fin 3 => volume.restrict (Icc (0 : ℝ) T))
          ∂(Measure.pi fun r => volume.restrict
            (Icc (K.a (![k, k, kb] r)) (K.b (![k, k, kb] r)))))
        = ∫⁻ s, segRow K k kb s * (∫⁻ v, chordWeight K k T v)
          ∂(Measure.pi fun r => volume.restrict
            (Icc (K.a (![k, k, kb] r)) (K.b (![k, k, kb] r)))) := by
          apply lintegral_congr_ae
          filter_upwards [positions_ae_d ![k, k, kb]] with s hs
          exact seg_depth_integral hP T s hs
      _ = _ := lintegral_mul_const _ (measurable_segRow K k kb)
  · intro κ _ hκ
    simp_rw [segWeight_zero_of_ne T κ hκ]
    simp
  · simp

/-! ### Removing the cutoff -/

variable (K k) in
/-- The chord weight without cutoff. -/
noncomputable def chordWeightInf (v : Fin 3 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (2 * v 0)) *
    ({v | (fitChord K k v).Nonempty}.indicator 1 v +
      ENNReal.ofReal (slopeSum K k) * volume (fitChord K k v))

lemma chordSet_mono (v : Fin 3 → ℝ) : Monotone fun n : ℕ => chordSet K k n v := by
  intro n q hnq c hc
  exact ⟨hc.1, below_mono K (T := (n : ℝ)) (U := (q : ℝ)) (by exact_mod_cast hnq) _ hc.2⟩

lemma iUnion_chordSet (v : Fin 3 → ℝ) : ⋃ n : ℕ, chordSet K k n v = fitChord K k v := by
  ext c
  simp only [mem_iUnion]
  constructor
  · rintro ⟨n, hn⟩; exact hn.1
  · intro hc
    obtain ⟨n, hn⟩ := exists_below K (segCopy K k v c)
    exact ⟨n, hc, hn⟩

lemma chordWeight_mono (v : Fin 3 → ℝ) : Monotone fun n : ℕ => chordWeight K k n v := by
  intro n q hnq
  change chordWeight K k n v ≤ chordWeight K k q v
  have hs : chordSet K k n v ⊆ chordSet K k q v := chordSet_mono v hnq
  unfold chordWeight
  gcongr
  exact chordSet_mono _ hnq

lemma tendsto_chordWeight (v : Fin 3 → ℝ) :
    Filter.Tendsto (fun n : ℕ => chordWeight K k n v) Filter.atTop
      (nhds (chordWeightInf K k v)) := by
  have hvol : Filter.Tendsto (fun n : ℕ => volume (chordSet K k n v)) Filter.atTop
      (nhds (volume (fitChord K k v))) := by
    rw [← iUnion_chordSet]
    exact tendsto_measure_iUnion_atTop (chordSet_mono v)
  have hind : Filter.Tendsto (fun n : ℕ => {v | (chordSet K k n v).Nonempty}.indicator
      (1 : (Fin 3 → ℝ) → ℝ≥0∞) v) Filter.atTop
      (nhds ({v | (fitChord K k v).Nonempty}.indicator 1 v)) := by
    by_cases h : (fitChord K k v).Nonempty
    · obtain ⟨c, hc⟩ := h
      rw [← iUnion_chordSet] at hc
      obtain ⟨n, hn⟩ := mem_iUnion.mp hc
      rw [indicator_of_mem (show v ∈ {v | (fitChord K k v).Nonempty} from ⟨c, (iUnion_chordSet v ▸
        hc : c ∈ fitChord K k v)⟩)]
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop n] with q hq
      rw [indicator_of_mem (show v ∈ {v | (chordSet K k q v).Nonempty} from
        ⟨c, chordSet_mono v hq hn⟩)]
    · rw [indicator_of_notMem (show v ∉ {v | (fitChord K k v).Nonempty} from h)]
      apply tendsto_const_nhds.congr'
      filter_upwards with q
      rw [indicator_of_notMem (show v ∉ {v | (chordSet K k q v).Nonempty} from
        fun ⟨c, hc⟩ => h ⟨c, hc.1⟩)]
  unfold chordWeight chordWeightInf
  exact ENNReal.Tendsto.const_mul (hind.add (ENNReal.Tendsto.const_mul hvol
    (Or.inr ENNReal.ofReal_ne_top))) (Or.inr ENNReal.ofReal_ne_top)

/-- **Removal of the cutoff** for genuine segment-candidate probabilities. -/
theorem seg_candidate_limit (hP : ParPair K k kb) :
    Filter.Tendsto (fun n : ℕ =>
      PoissonPP.law (Λ K n) {ω | HasSegCand K k kb n ω}) Filter.atTop
      (nhds (segDensity K k kb * ∫⁻ v, chordWeightInf K k v)) := by
  simp_rw [seg_count_factor hP]
  have hint : Filter.Tendsto (fun n : ℕ => ∫⁻ v, chordWeight K k n v) Filter.atTop
      (nhds (∫⁻ v, chordWeightInf K k v)) :=
    lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (measurable_chordWeight K k n).aemeasurable)
      (Filter.Eventually.of_forall chordWeight_mono)
      (Filter.Eventually.of_forall tendsto_chordWeight)
  have hmono : Monotone (fun n : ℕ => ∫⁻ v, chordWeight K k n v) :=
    fun n q hnq => lintegral_mono fun v => chordWeight_mono v hnq
  have hsup : (⨆ n : ℕ, ∫⁻ v, chordWeight K k n v) = ∫⁻ v, chordWeightInf K k v :=
    tendsto_nhds_unique (tendsto_atTop_iSup hmono) hint
  have hmono' : Monotone (fun n : ℕ => segDensity K k kb * ∫⁻ v, chordWeight K k n v) :=
    fun n q hnq => mul_le_mul_of_nonneg_left (hmono hnq) bot_le
  rw [← hsup, ENNReal.mul_iSup]
  exact tendsto_atTop_iSup hmono'

end Enclosing
