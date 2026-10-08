import LeanProofs.TwoTri.Main
import LeanProofs.TwoTri.Extend

/-!
# Theorem 2: every hull size

Points `par i = (i, i²)` on the parabola are in convex position, and two of their chords cross
exactly when the indices interleave. This turns the convex seed of Lemma 8 (two hull-disjoint
triangulations of a convex `h`-gon) into index arithmetic.
-/

set_option linter.unusedSectionVars false

namespace TwoTri.Hulls

open TwoTri

/-- The `i`-th point of the parabola. -/
def par (i : ℕ) : ℚ × ℚ := ((i : ℚ), (i : ℚ) ^ 2)

lemma orient_par (a b c : ℕ) :
    orient (par a) (par b) (par c) = ((b : ℚ) - a) * ((c : ℚ) - a) * ((c : ℚ) - b) := by
  unfold orient par; ring

lemma par_injective : Function.Injective par := by
  intro i j h
  have := congrArg Prod.fst h
  simpa [par] using this

/-- Chords `ij` and `kl` (with `i < j`, `k < l`) interleave. -/
def Inter (i j k l : ℕ) : Prop := (i < k ∧ k < j ∧ j < l) ∨ (k < i ∧ i < l ∧ l < j)

theorem scross_par_iff {i j k l : ℕ} (hij : i < j) (hkl : k < l) :
    SCross (par i) (par j) (par k) (par l) ↔ Inter i j k l := by
  simp only [SCross, orient_par, mul_neg_iff, mul_pos_iff, sub_pos, sub_neg, Nat.cast_lt, Inter]
  omega

/-! ## Sign of the orientation on the parabola -/

lemma orient_par_pos {i j k : ℕ} (hij : i < j) :
    0 < orient (par i) (par j) (par k) ↔ k < i ∨ j < k := by
  rw [orient_par]; simp only [mul_pos_iff, mul_neg_iff, sub_pos, sub_neg, Nat.cast_lt]; omega

lemma orient_par_neg {i j k : ℕ} (hij : i < j) :
    orient (par i) (par j) (par k) < 0 ↔ i < k ∧ k < j := by
  rw [orient_par]; simp only [mul_pos_iff, mul_neg_iff, sub_pos, sub_neg, Nat.cast_lt]; omega

/-- Convex position: no point of the parabola lies strictly inside a triangle of three others. -/
lemma not_inTri_par (a b c k : ℕ) : ¬ InTri (par a) (par b) (par c) (par k) := by
  simp only [InTri, orient_par, mul_pos_iff, mul_neg_iff, sub_pos, sub_neg, Nat.cast_lt]; omega

/-! ## The convex `h`-gon and its segments -/

/-- The convex `h`-gon `par 0, …, par (h - 1)`, in order around its hull. -/
def cvx (h : ℕ) : Finset (ℚ × ℚ) := (Finset.range h).image par

lemma mem_cvx {h : ℕ} {q : ℚ × ℚ} : q ∈ cvx h ↔ ∃ i < h, par i = q := by simp [cvx]

lemma par_mem {h i : ℕ} (hi : i < h) : par i ∈ cvx h := mem_cvx.mpr ⟨i, hi, rfl⟩

lemma card_cvx (h : ℕ) : (cvx h).card = h := by
  rw [cvx, Finset.card_image_of_injective _ par_injective, Finset.card_range]

lemma genPos_cvx (h : ℕ) : GenPos (cvx h) := by
  intro a ha b hb c hc hab hac hbc
  obtain ⟨i, -, rfl⟩ := mem_cvx.mp ha
  obtain ⟨j, -, rfl⟩ := mem_cvx.mp hb
  obtain ⟨k, -, rfl⟩ := mem_cvx.mp hc
  have hij : i ≠ j := fun e => hab (by rw [e])
  have hik : i ≠ k := fun e => hac (by rw [e])
  have hjk : j ≠ k := fun e => hbc (by rw [e])
  rw [orient_par]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> rw [sub_ne_zero, Ne, Nat.cast_inj] <;> omega

lemma pair_inj {i j k l : ℕ} (hij : i < j) (hkl : k < l)
    (h : s(par i, par j) = s(par k, par l)) : i = k ∧ j = l := by
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨par_injective h1, par_injective h2⟩
  · have := par_injective h1; have := par_injective h2; omega

lemma par_seg_mem {h i j : ℕ} (hij : i < j) (hj : j < h) : s(par i, par j) ∈ segs (cvx h) :=
  mk_mem_segs.mpr ⟨par_mem (by omega), par_mem hj, fun e => by have := par_injective e; omega⟩

lemma segs_cvx {h : ℕ} {s : Sym2 (ℚ × ℚ)} (hs : s ∈ segs (cvx h)) :
    ∃ i j, i < j ∧ j < h ∧ s = s(par i, par j) := by
  induction s using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb, hab⟩ := mk_mem_segs.mp hs
    obtain ⟨i, hi, rfl⟩ := mem_cvx.mp ha
    obtain ⟨j, hj, rfl⟩ := mem_cvx.mp hb
    rcases lt_trichotomy i j with hl | rfl | hl
    · exact ⟨i, j, hl, hj, rfl⟩
    · exact absurd rfl hab
    · exact ⟨j, i, hl, hi, Sym2.eq_swap⟩

/-- The segments `par i par j` (`i < j < h`) whose indices satisfy `R`. -/
noncomputable def eset (h : ℕ) (R : ℕ → ℕ → Prop) : Finset (Sym2 (ℚ × ℚ)) := by
  classical exact (segs (cvx h)).filter (fun s => ∃ i j, i < j ∧ j < h ∧ R i j ∧ s = s(par i, par j))

lemma mem_eset {h : ℕ} {R : ℕ → ℕ → Prop} {s : Sym2 (ℚ × ℚ)} :
    s ∈ eset h R ↔ ∃ i j, i < j ∧ j < h ∧ R i j ∧ s = s(par i, par j) := by
  classical
  unfold eset
  rw [Finset.mem_filter]
  constructor
  · exact fun hs => hs.2
  · rintro ⟨i, j, hij, hj, hR, rfl⟩
    exact ⟨par_seg_mem hij hj, i, j, hij, hj, hR, rfl⟩

lemma mk_mem_eset {h : ℕ} {R : ℕ → ℕ → Prop} {i j : ℕ} (hij : i < j) (hj : j < h) :
    s(par i, par j) ∈ eset h R ↔ R i j := by
  rw [mem_eset]
  constructor
  · rintro ⟨k, l, hkl, -, hR, e⟩
    obtain ⟨rfl, rfl⟩ := pair_inj hij hkl e
    exact hR
  · exact fun hR => ⟨i, j, hij, hj, hR, rfl⟩

lemma eset_sub (h : ℕ) (R : ℕ → ℕ → Prop) : eset h R ⊆ segs (cvx h) := fun s hs => by
  obtain ⟨i, j, hij, hj, -, rfl⟩ := mem_eset.mp hs
  exact par_seg_mem hij hj

/-- A rule on index pairs gives a triangulation of the convex `h`-gon if its chords do not
interleave and every other chord interleaves one of them. -/
theorem isTri_eset {h : ℕ} {R : ℕ → ℕ → Prop}
    (hnc : ∀ i j k l, i < j → j < h → k < l → l < h → R i j → R k l → ¬ Inter i j k l)
    (hmax : ∀ i j, i < j → j < h → ¬ R i j → ∃ k l, k < l ∧ l < h ∧ R k l ∧ Inter i j k l) :
    IsTri (cvx h) (eset h R) := by
  refine ⟨eset_sub h R, ?_, ?_⟩
  · intro s hs t ht hc
    obtain ⟨i, j, hij, hj, hR, rfl⟩ := mem_eset.mp hs
    obtain ⟨k, l, hkl, hl, hR', rfl⟩ := mem_eset.mp ht
    rw [cross_mk, scross_par_iff hij hkl] at hc
    exact hnc i j k l hij hj hkl hl hR hR' hc
  · intro s hs hsT
    obtain ⟨i, j, hij, hj, rfl⟩ := segs_cvx hs
    have hR : ¬ R i j := fun hR => hsT ((mk_mem_eset hij hj).mpr hR)
    obtain ⟨k, l, hkl, hl, hR', hI⟩ := hmax i j hij hj hR
    exact ⟨s(par k, par l), (mk_mem_eset hkl hl).mpr hR',
      by rw [cross_mk, scross_par_iff hij hkl]; exact hI⟩

/-! ## The hull of the convex `h`-gon -/

/-- Consecutive indices, and the closing pair `0, h - 1`. -/
def HullR (h i j : ℕ) : Prop := j = i + 1 ∨ (i = 0 ∧ j = h - 1)

theorem hull_cvx {h : ℕ} (h3 : 3 ≤ h) : hullEdges (cvx h) = eset h (HullR h) := by
  ext s
  constructor
  · intro hs
    obtain ⟨i, j, hij, hj, rfl⟩ := segs_cvx (Finset.mem_filter.mp hs).1
    refine (mk_mem_eset hij hj).mpr ?_
    obtain ⟨-, -, -, hH⟩ := mk_mem_hullEdges.mp hs
    by_contra hn
    unfold HullR at hn
    rcases hH with hpos | hneg
    · have := (orient_par_pos hij).mp (hpos (par (i + 1)) (par_mem (by omega))
        (fun e => by have := par_injective e; omega) (fun e => by have := par_injective e; omega))
      omega
    · by_cases hi0 : i = 0
      · subst hi0
        have := (orient_par_neg hij).mp (hneg (par (h - 1)) (par_mem (by omega))
          (fun e => by have := par_injective e; omega) (fun e => by have := par_injective e; omega))
        omega
      · have := (orient_par_neg hij).mp (hneg (par 0) (par_mem (by omega))
          (fun e => by have := par_injective e; omega) (fun e => by have := par_injective e; omega))
        omega
  · intro hs
    obtain ⟨i, j, hij, hj, hR, rfl⟩ := mem_eset.mp hs
    refine mk_mem_hullEdges.mpr ⟨par_mem (by omega), par_mem hj,
      fun e => by have := par_injective e; omega, ?_⟩
    rcases hR with rfl | ⟨rfl, rfl⟩
    · left
      intro c hc h1 h2
      obtain ⟨k, -, rfl⟩ := mem_cvx.mp hc
      have : k ≠ i := fun e => h1 (by rw [e])
      have : k ≠ i + 1 := fun e => h2 (by rw [e])
      exact (orient_par_pos hij).mpr (by omega)
    · right
      intro c hc h1 h2
      obtain ⟨k, hk, rfl⟩ := mem_cvx.mp hc
      have : k ≠ 0 := fun e => h1 (by rw [e])
      have : k ≠ h - 1 := fun e => h2 (by rw [e])
      exact (orient_par_neg hij).mpr (by omega)

theorem card_hull_cvx {h : ℕ} (h3 : 3 ≤ h) : (hullEdges (cvx h)).card = h := by
  classical
  have heq : eset h (HullR h) =
      insert s(par 0, par (h - 1)) ((Finset.range (h - 1)).image (fun i => s(par i, par (i + 1)))) := by
    ext s
    simp only [mem_eset, Finset.mem_insert, Finset.mem_image, Finset.mem_range, HullR]
    constructor
    · rintro ⟨i, j, hij, hj, (rfl | ⟨rfl, rfl⟩), rfl⟩
      · exact Or.inr ⟨i, by omega, rfl⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, h - 1, by omega, by omega, Or.inr ⟨rfl, rfl⟩, rfl⟩
      · exact ⟨i, i + 1, by omega, by omega, Or.inl rfl, rfl⟩
  have hinj : Function.Injective (fun i : ℕ => s(par i, par (i + 1))) := fun i k e =>
    (pair_inj (Nat.lt_succ_self i) (Nat.lt_succ_self k) e).1
  rw [hull_cvx h3, heq, Finset.card_insert_of_notMem, Finset.card_image_of_injective _ hinj,
    Finset.card_range]
  · omega
  · simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro i hi e
    have := pair_inj (Nat.lt_succ_self i) (by omega) e
    omega

/-! ## Lemma 8: the convex seed -/

/-- `A`: the triangle `v₁v₃v₅` (indices `0, 2, 4`) and the fan from `v₅`. -/
def AR (h i j : ℕ) : Prop :=
  HullR h i j ∨ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 4) ∨ (i = 0 ∧ j = 4) ∨ (i = 4 ∧ 6 ≤ j)

/-- `B`: the triangle `v₂v₄v₆` (indices `1, 3, 5`) and the fan from `v₂`. -/
def BR (h i j : ℕ) : Prop :=
  HullR h i j ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 5) ∨ (i = 1 ∧ j = 5) ∨ (i = 1 ∧ 6 ≤ j)

theorem isTri_A {h : ℕ} (h6 : 6 ≤ h) : IsTri (cvx h) (eset h (AR h)) := by
  refine isTri_eset ?_ ?_
  · intro i j k l _ _ _ _ h1 h2; unfold AR HullR at h1 h2; unfold Inter; omega
  · intro i j hij hj hn
    unfold AR HullR at hn
    unfold AR HullR Inter
    rcases (by omega : (i = 0 ∧ j = 3) ∨ (i = 0 ∧ 5 ≤ j) ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 5 ≤ i)
      with hc | hc | hc | hc | hc | hc
    · exact ⟨2, 4, by omega, by omega, by omega, by omega⟩
    · exact ⟨4, j + 1, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, 2, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, 4, by omega, by omega, by omega, by omega⟩
    · exact ⟨2, 4, by omega, by omega, by omega, by omega⟩
    · exact ⟨4, i + 1, by omega, by omega, by omega, by omega⟩

theorem isTri_B {h : ℕ} (h6 : 6 ≤ h) : IsTri (cvx h) (eset h (BR h)) := by
  refine isTri_eset ?_ ?_
  · intro i j k l _ _ _ _ h1 h2; unfold BR HullR at h1 h2; unfold Inter; omega
  · intro i j hij hj hn
    unfold BR HullR at hn
    unfold BR HullR Inter
    rcases (by omega : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ (j = 3 ∨ j = 4)) ∨ (i = 0 ∧ 5 ≤ j) ∨ i = 1 ∨
        i = 2 ∨ i = 3 ∨ i = 4 ∨ 5 ≤ i) with hc | hc | hc | hc | hc | hc | hc | hc
    · exact ⟨1, 3, by omega, by omega, by omega, by omega⟩
    · exact ⟨1, 5, by omega, by omega, by omega, by omega⟩
    · exact ⟨1, j + 1, by omega, by omega, by omega, by omega⟩
    · exact ⟨3, 5, by omega, by omega, by omega, by omega⟩
    · exact ⟨1, 3, by omega, by omega, by omega, by omega⟩
    · exact ⟨1, 5, by omega, by omega, by omega, by omega⟩
    · exact ⟨3, 5, by omega, by omega, by omega, by omega⟩
    · exact ⟨1, i + 1, by omega, by omega, by omega, by omega⟩

theorem inter_AB {h : ℕ} (h6 : 6 ≤ h) :
    eset h (AR h) ∩ eset h (BR h) = hullEdges (cvx h) := by
  rw [hull_cvx (by omega)]
  ext s
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hA, hB⟩
    obtain ⟨i, j, hij, hj, hR, rfl⟩ := mem_eset.mp hA
    have hR' := (mk_mem_eset hij hj).mp hB
    refine (mk_mem_eset hij hj).mpr ?_
    unfold AR HullR at hR; unfold BR HullR at hR'; unfold HullR; omega
  · intro hs
    obtain ⟨i, j, hij, hj, hR, rfl⟩ := mem_eset.mp hs
    exact ⟨(mk_mem_eset hij hj).mpr (Or.inl hR), (mk_mem_eset hij hj).mpr (Or.inl hR)⟩

/-- A triangle of the parabola with its three sides in `T` is a face. -/
lemma face_par {h : ℕ} {T : Finset (Sym2 (ℚ × ℚ))} {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (hc : c < h) (h1 : s(par a, par b) ∈ T) (h2 : s(par b, par c) ∈ T)
    (h3 : s(par c, par a) ∈ T) : Face (cvx h) T (par a) (par b) (par c) :=
  ⟨par_mem (by omega), par_mem (by omega), par_mem hc, (orient_par_pos hab).mpr (Or.inr hbc),
    h1, h2, h3, fun q hq => by obtain ⟨k, -, rfl⟩ := mem_cvx.mp hq; exact not_inTri_par a b c k⟩

/-- For `h ≥ 7` the seed satisfies the invariant of the induction: the side `v₁v₃` of the face
`v₁v₃v₅` of `A` passes through the faces `v₂v₄v₆` and `v₂v₆v₇` of `B`. -/
theorem inv_cvx {h : ℕ} (h7 : 7 ≤ h) : Inv (cvx h) (eset h (AR h)) (eset h (BR h)) := by
  have mA : ∀ i j, i < j → j < h → AR h i j → s(par i, par j) ∈ eset h (AR h) :=
    fun i j hij hj hR => (mk_mem_eset hij hj).mpr hR
  have mB : ∀ i j, i < j → j < h → BR h i j → s(par i, par j) ∈ eset h (BR h) :=
    fun i j hij hj hR => (mk_mem_eset hij hj).mpr hR
  have ne : ∀ i j : ℕ, i ≠ j → par i ≠ par j := fun i j hij e => hij (par_injective e)
  refine ⟨par 0, par 2, par 4, par 1, par 3, par 5, par 1, par 5, par 6,
    face_par (by norm_num) (by norm_num) (by omega) (mA 0 2 (by norm_num) (by omega) (by unfold AR; omega))
      (mA 2 4 (by norm_num) (by omega) (by unfold AR; omega))
      (by rw [Sym2.eq_swap]; exact mA 0 4 (by norm_num) (by omega) (by unfold AR; omega)),
    face_par (by norm_num) (by norm_num) (by omega) (mB 1 3 (by norm_num) (by omega) (by unfold BR; omega))
      (mB 3 5 (by norm_num) (by omega) (by unfold BR; omega))
      (by rw [Sym2.eq_swap]; exact mB 1 5 (by norm_num) (by omega) (by unfold BR; omega)),
    face_par (by norm_num) (by norm_num) (by omega) (mB 1 5 (by norm_num) (by omega) (by unfold BR; omega))
      (mB 5 6 (by norm_num) (by omega) (by unfold BR HullR; omega))
      (by rw [Sym2.eq_swap]; exact mB 1 6 (by norm_num) (by omega) (by unfold BR; omega)),
    ?_, ⟨ne 1 0 (by norm_num), ne 1 2 (by norm_num)⟩, ⟨ne 5 0 (by norm_num), ne 5 2 (by norm_num)⟩,
    ⟨ne 6 0 (by norm_num), ne 6 2 (by norm_num)⟩,
    ⟨par 6, Or.inr (Or.inr rfl), ne 6 1 (by norm_num), ne 6 3 (by norm_num), ne 6 5 (by norm_num)⟩,
    ⟨13 / 20, by norm_num, by norm_num, by norm_num [InTri, orient, lerp, par]⟩,
    ⟨61 / 100, by norm_num, by norm_num, by norm_num [InTri, orient, lerp, par]⟩⟩
  rintro v (rfl | rfl | rfl) <;>
    exact ⟨ne _ _ (by norm_num), ne _ _ (by norm_num), ne _ _ (by norm_num)⟩

lemma inter_eset {h : ℕ} {R S : ℕ → ℕ → Prop}
    (hRS : ∀ i j, i < j → j < h → (R i j ∧ S i j ↔ HullR h i j)) :
    eset h R ∩ eset h S = eset h (HullR h) := by
  ext s
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hA, hB⟩
    obtain ⟨i, j, hij, hj, hR, rfl⟩ := mem_eset.mp hA
    exact (mk_mem_eset hij hj).mpr ((hRS i j hij hj).mp ⟨hR, (mk_mem_eset hij hj).mp hB⟩)
  · intro hs
    obtain ⟨i, j, hij, hj, hR, rfl⟩ := mem_eset.mp hs
    obtain ⟨h1, h2⟩ := (hRS i j hij hj).mpr hR
    exact ⟨(mk_mem_eset hij hj).mpr h1, (mk_mem_eset hij hj).mpr h2⟩

/-! ## Convex position with three, four and five points -/

def A4 (i j : ℕ) : Prop := HullR 4 i j ∨ (i = 0 ∧ j = 2)
def B4 (i j : ℕ) : Prop := HullR 4 i j ∨ (i = 1 ∧ j = 3)
def A5 (i j : ℕ) : Prop := HullR 5 i j ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3)
def B5 (i j : ℕ) : Prop := HullR 5 i j ∨ (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4)

theorem isTri_3 : IsTri (cvx 3) (eset 3 (HullR 3)) := by
  refine isTri_eset ?_ ?_
  · intro i j k l _ _ _ _ h1 h2; unfold HullR at h1 h2; unfold Inter; omega
  · intro i j hij hj hn; unfold HullR at hn; omega

theorem isTri_A4 : IsTri (cvx 4) (eset 4 A4) := by
  refine isTri_eset ?_ ?_
  · intro i j k l _ _ _ _ h1 h2; unfold A4 HullR at h1 h2; unfold Inter; omega
  · intro i j hij hj hn; unfold A4 HullR at hn; unfold A4 HullR Inter
    exact ⟨0, 2, by omega, by omega, by omega, by omega⟩

theorem isTri_B4 : IsTri (cvx 4) (eset 4 B4) := by
  refine isTri_eset ?_ ?_
  · intro i j k l _ _ _ _ h1 h2; unfold B4 HullR at h1 h2; unfold Inter; omega
  · intro i j hij hj hn; unfold B4 HullR at hn; unfold B4 HullR Inter
    exact ⟨1, 3, by omega, by omega, by omega, by omega⟩

theorem isTri_A5 : IsTri (cvx 5) (eset 5 A5) := by
  refine isTri_eset ?_ ?_
  · intro i j k l _ _ _ _ h1 h2; unfold A5 HullR at h1 h2; unfold Inter; omega
  · intro i j hij hj hn; unfold A5 HullR at hn; unfold A5 HullR Inter
    rcases (by omega : i = 1 ∨ i = 2) with hc | hc
    · exact ⟨0, 2, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, 3, by omega, by omega, by omega, by omega⟩

theorem isTri_B5 : IsTri (cvx 5) (eset 5 B5) := by
  refine isTri_eset ?_ ?_
  · intro i j k l _ _ _ _ h1 h2; unfold B5 HullR at h1 h2; unfold Inter; omega
  · intro i j hij hj hn; unfold B5 HullR at hn; unfold B5 HullR Inter
    rcases (by omega : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ i = 2) with hc | hc | hc
    · exact ⟨1, 3, by omega, by omega, by omega, by omega⟩
    · exact ⟨1, 4, by omega, by omega, by omega, by omega⟩
    · exact ⟨1, 3, by omega, by omega, by omega, by omega⟩

/-! ## Seven points with a hexagonal hull (Section 7) -/

namespace Seven

def q1 : ℚ × ℚ := (1, 2)
def q2 : ℚ × ℚ := (0, 0)
def q3 : ℚ × ℚ := (1, 0)
def q4 : ℚ × ℚ := (4, 1)
def q5 : ℚ × ℚ := (5, 2)
def q6 : ℚ × ℚ := (6, 6)
def q7 : ℚ × ℚ := (2, 1)

def P7 : Finset (ℚ × ℚ) := {q1, q2, q3, q4, q5, q6, q7}
def H7 : Finset (Sym2 (ℚ × ℚ)) :=
  {s(q1, q2), s(q2, q3), s(q3, q4), s(q4, q5), s(q5, q6), s(q6, q1)}
def A7 : Finset (Sym2 (ℚ × ℚ)) :=
  H7 ∪ {s(q1, q3), s(q1, q4), s(q1, q5), s(q1, q7), s(q3, q7), s(q4, q7)}
def B7 : Finset (Sym2 (ℚ × ℚ)) :=
  H7 ∪ {s(q2, q4), s(q2, q5), s(q2, q6), s(q2, q7), s(q5, q7), s(q6, q7)}

theorem card_P7 : P7.card = 7 := by decide +kernel
theorem genPos_P7 : GenPos P7 := by decide +kernel
theorem hull_P7 : hullEdges P7 = H7 := by decide +kernel
theorem card_H7 : H7.card = 6 := by decide +kernel
theorem isTri_A7 : IsTri P7 A7 := by decide +kernel
theorem isTri_B7 : IsTri P7 B7 := by decide +kernel
theorem inter_A7_B7 : A7 ∩ B7 = H7 := by decide +kernel

/-- The invariant: the side `13` of the face `137` of `A` passes through the faces `245` and
`276` of `B`, at parameters `17/20` and `11/20`. -/
theorem inv7 : Inv P7 A7 B7 := by
  refine ⟨q1, q3, q7, q2, q4, q5, q2, q7, q6, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨q6, Or.inr (Or.inr rfl), by decide +kernel⟩,
    ⟨17 / 20, by norm_num, by norm_num, by decide +kernel⟩,
    ⟨11 / 20, by norm_num, by norm_num, by decide +kernel⟩⟩
  rintro v (rfl | rfl | rfl) <;> decide +kernel

end Seven

/-! ## Growing a seed, and passing to `ℝ` -/

/-- From any hull-disjoint seed carrying the invariant, every larger size is reached with the
same hull. -/
theorem grow {P₀ : Finset (ℚ × ℚ)} {A₀ B₀ : Finset (Sym2 (ℚ × ℚ))} (hP₀ : GenPos P₀)
    (hA₀ : IsTri P₀ A₀) (hB₀ : IsTri P₀ B₀) (hAB₀ : A₀ ∩ B₀ = hullEdges P₀) (hI₀ : Inv P₀ A₀ B₀)
    (n : ℕ) (hn : P₀.card ≤ n) :
    ∃ P : Finset (ℚ × ℚ), P.card = n ∧ GenPos P ∧ (hullEdges P).card = (hullEdges P₀).card ∧
      ∃ A B : Finset (Sym2 (ℚ × ℚ)), IsTri P A ∧ IsTri P B ∧ A ∩ B = hullEdges P ∧
        Inv P A B := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨P₀, rfl, hP₀, rfl, A₀, B₀, hA₀, hB₀, hAB₀, hI₀⟩
  | succ n _ ih =>
    obtain ⟨P, hcard, hP, hh, A, B, hA, hB, hAB, hI⟩ := ih
    obtain ⟨p, A', B', hpP, hP', hA', hB', hhull, hinter, hI'⟩ := step hP hA hB hI
    exact ⟨insert p P, by rw [Finset.card_insert_of_notMem hpP, hcard], hP',
      by rw [hhull]; exact hh, A', B', hA', hB', by rw [hinter, hAB, hhull], hI'⟩

/-- Some set of `n` points in general position in `ℝ²`, with `h` hull edges, has two
triangulations whose only common edges are the hull edges. -/
def HullOnly (n h : ℕ) : Prop :=
  ∃ P : Finset (ℝ × ℝ), P.card = n ∧ GenPos P ∧ (hullEdges P).card = h ∧
    ∃ A B : Finset (Sym2 (ℝ × ℝ)), IsTri P A ∧ IsTri P B ∧ A ∩ B = hullEdges P

theorem hullOnly_of_rat {P : Finset (ℚ × ℚ)} {A B : Finset (Sym2 (ℚ × ℚ))} (hP : GenPos P)
    (hA : IsTri P A) (hB : IsTri P B) (hAB : A ∩ B = hullEdges P) :
    HullOnly P.card (hullEdges P).card := by
  set f : ℚ →+* ℝ := Rat.castHom ℝ
  have hf : StrictMono f := Rat.cast_strictMono
  have inj := pmap_inj f hf
  have injS : Function.Injective (Sym2.map (pmap f)) := Sym2.map.injective inj
  refine ⟨P.image (pmap f), Finset.card_image_of_injective _ inj, genPos_image f hf hP,
    by rw [hullEdges_image f hf, Finset.card_image_of_injective _ injS],
    A.image (Sym2.map (pmap f)), B.image (Sym2.map (pmap f)), isTri_image f hf hA,
    isTri_image f hf hB, ?_⟩
  rw [← Finset.image_inter_of_injOn _ _ injS.injOn, hAB, hullEdges_image f hf]

theorem hullOnly_cvx {h : ℕ} {R S : ℕ → ℕ → Prop} (h3 : 3 ≤ h) (hR : IsTri (cvx h) (eset h R))
    (hS : IsTri (cvx h) (eset h S)) (hRS : eset h R ∩ eset h S = hullEdges (cvx h)) :
    HullOnly h h := by
  have := hullOnly_of_rat (genPos_cvx h) hR hS hRS
  rwa [card_cvx, card_hull_cvx h3] at this

/-! ## Theorem 2 -/

/-- **Theorem 2, the constructions.** Sharing only the hull is possible when `n = h`, when
`h ≥ 6`, and when `h = 5` and `n ≥ 9`. -/
theorem hullOnly_of {n h : ℕ} (h3 : 3 ≤ h) (hhn : h ≤ n)
    (hc : n = h ∨ 6 ≤ h ∨ (h = 5 ∧ 9 ≤ n)) : HullOnly n h := by
  have convex : ∀ m, 3 ≤ m → HullOnly m m := by
    intro m hm
    rcases (by omega : m = 3 ∨ m = 4 ∨ m = 5 ∨ 6 ≤ m) with rfl | rfl | rfl | h6
    · exact hullOnly_cvx (by norm_num) isTri_3 isTri_3 (by rw [Finset.inter_self, hull_cvx le_rfl])
    · exact hullOnly_cvx (by norm_num) isTri_A4 isTri_B4
        (by rw [hull_cvx (by norm_num)]; exact inter_eset fun i j _ _ => by unfold A4 B4 HullR; omega)
    · exact hullOnly_cvx (by norm_num) isTri_A5 isTri_B5
        (by rw [hull_cvx (by norm_num)]; exact inter_eset fun i j _ _ => by unfold A5 B5 HullR; omega)
    · exact hullOnly_cvx (by omega) (isTri_A h6) (isTri_B h6) (inter_AB h6)
  rcases hc with rfl | h6 | ⟨rfl, h9⟩
  · exact convex n h3
  · rcases eq_or_lt_of_le hhn with rfl | hlt
    · exact convex h h3
    rcases (by omega : h = 6 ∨ 7 ≤ h) with rfl | h7
    · obtain ⟨P, hc, hP, hh, A, B, hA, hB, hAB, -⟩ :=
        grow Seven.genPos_P7 Seven.isTri_A7 Seven.isTri_B7
          (by rw [Seven.inter_A7_B7, Seven.hull_P7]) Seven.inv7 n
          (by rw [Seven.card_P7]; omega)
      have := hullOnly_of_rat hP hA hB hAB
      rwa [hc, hh, Seven.hull_P7, Seven.card_H7] at this
    · obtain ⟨P, hc, hP, hh, A, B, hA, hB, hAB, -⟩ :=
        grow (genPos_cvx h) (isTri_A (by omega)) (isTri_B (by omega)) (inter_AB (by omega))
          (inv_cvx h7) n (by rw [card_cvx]; omega)
      have := hullOnly_of_rat hP hA hB hAB
      rwa [hc, hh, card_hull_cvx (by omega)] at this
  · obtain ⟨P, hc, hP, hh, A, B, hA, hB, hAB⟩ := upper (K := ℝ) n h9
    exact ⟨P, hc, hP, hh, A, B, hA, hB, hAB⟩

/-- **Theorem 2, small hulls.** A hull of at most four edges with a point off it forces shared
edges beyond the hull. -/
theorem not_hullOnly_small {n h : ℕ} (h3 : 3 ≤ h) (h4 : h ≤ 4) (hlt : h < n) :
    ¬ HullOnly n h := by
  rintro ⟨P, rfl, hP, rfl, A, B, hA, hB, hAB⟩
  have h6 := six_unavoidable hP (by omega) hlt h4
  have := Finset.card_le_card (unav_sub_inter hA hB)
  rw [hAB] at this
  omega

/-- The input from the order-type enumeration (Section 6): no set of six, seven or eight points
in general position with a pentagonal hull has two triangulations sharing only the hull. This
rests on the completeness of the Aichholzer–Aurenhammer–Krasser database and is not proved here. -/
def PentagonGap : Prop := ∀ n, 6 ≤ n → n ≤ 8 → ¬ HullOnly n 5

/-- **Theorem 2.** Let `3 ≤ h ≤ n`. Some set of `n` points in general position with `h` hull edges
has two triangulations sharing only the hull iff `n = h`, or `h ≥ 6`, or `h = 5` and `n ≥ 9`.
The case `h = 5`, `6 ≤ n ≤ 8` of the forward direction is the hypothesis `PentagonGap`. -/
theorem theorem2 (hgap : PentagonGap) {n h : ℕ} (h3 : 3 ≤ h) (hhn : h ≤ n) :
    HullOnly n h ↔ n = h ∨ 6 ≤ h ∨ (h = 5 ∧ 9 ≤ n) := by
  refine ⟨fun H => ?_, hullOnly_of h3 hhn⟩
  by_contra hn
  rcases (by omega : (h ≤ 4 ∧ h < n) ∨ (h = 5 ∧ 6 ≤ n ∧ n ≤ 8)) with ⟨h4, hlt⟩ | ⟨rfl, h6, h8⟩
  · exact not_hullOnly_small h3 h4 hlt H
  · exact hgap n h6 h8 H

end TwoTri.Hulls
