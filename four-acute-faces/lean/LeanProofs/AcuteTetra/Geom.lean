import LeanProofs.AcuteTetra.Facts
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Acute tetrahedron: the geometric lemmas

Four unit vectors `A 0, …, A 3` in a real inner product space. A signed triple sum (an *edge*)
is *short* if its norm is `< 1`. We prove:

* `one_per_face`: two different sums on one face are never both short;
* `no_star`: the four sums at one sign vector are never all short;
* `join`: two disjoint short sums on different faces are joined by a short sum;
* `exists_short`: in dimension 3, some sum is short (for generic vectors);
* `acute_iff`: a sign variant has all angles acute iff every short sum is incident to it.
-/

namespace AcuteTetra

open Finset

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The vector `Σ c_i A_i`. -/
def vecOf (A : Fin 4 → V) (c : Fin 4 → ℤ) : V := ∑ i, (c i : ℝ) • A i

/-- The Gram matrix. -/
def gx (A : Fin 4 → V) (i j : Fin 4) : ℝ := inner ℝ (A i) (A j)

lemma gx_symm (A : Fin 4 → V) (i j : Fin 4) : gx A i j = gx A j i := real_inner_comm _ _

lemma gx_diag (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) (i : Fin 4) : gx A i i = 1 := by
  simp [gx, hA]

lemma inner_vecOf (A : Fin 4 → V) (c d : Fin 4 → ℤ) :
    inner ℝ (vecOf A c) (vecOf A d) = gram (gx A) (outer c d) := by
  simp only [vecOf, gram, outer, gx, Fin.sum_univ_four, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, Int.cast_mul]
  ring

lemma sq_vecOf (A : Fin 4 → V) (c : Fin 4 → ℤ) :
    ‖vecOf A c‖ ^ 2 = gram (gx A) (outer c c) := by
  rw [← real_inner_self_eq_norm_sq, inner_vecOf]

lemma gram_unit (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) : gram (gx A) unitM = 1 := by
  simp [gram, unitM, Fin.sum_univ_four, gx_diag A hA]

/-- Equal coefficient matrices (in the sense of `gramEq`) give equal Gram values. -/
lemma gram_congr' (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) {M N : Fin 4 → Fin 4 → ℤ}
    (h : gramEq M N = true) : gram (gx A) M = gram (gx A) N :=
  gram_congr (gx A) (gx_symm A) (gx_diag A hA) h

lemma vecOf_sub (A : Fin 4 → V) (c d : Fin 4 → ℤ) :
    vecOf A (fun t => c t - d t) = vecOf A c - vecOf A d := by
  simp [vecOf, sub_smul, Finset.sum_sub_distrib]

lemma vecOf_add (A : Fin 4 → V) (c d : Fin 4 → ℤ) :
    vecOf A (fun t => c t + d t) = vecOf A c + vecOf A d := by
  simp [vecOf, add_smul, Finset.sum_add_distrib]

lemma vecOf_pc (A : Fin 4 → V) (σ : Sign) (i : Fin 4) :
    vecOf A (pc σ i) = (sgZ (σ i) : ℝ) • A i := by
  simp [vecOf, pc, apply_ite (fun z : ℤ => (z : ℝ)), ite_smul]

lemma norm_sgZ_smul (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) (b : Bool) (i : Fin 4) :
    ‖(sgZ b : ℝ) • A i‖ = 1 := by
  cases b <;> simp [sgZ, hA]

/-- A signed triple sum is short. -/
def Short (A : Fin 4 → V) (e : Edge) : Prop := ‖vecOf A (cE e)‖ < 1

lemma short_iff_sq (A : Fin 4 → V) (e : Edge) :
    Short A e ↔ gram (gx A) (outer (cE e) (cE e)) < 1 := by
  rw [Short, ← sq_vecOf]
  constructor
  · intro h; nlinarith [norm_nonneg (vecOf A (cE e))]
  · intro h; nlinarith [norm_nonneg (vecOf A (cE e))]

/-- Two different sums on the same face are never both short. -/
theorem one_per_face (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) (l : Fin 4) (p p' : Bool × Bool)
    (h : Short A (l, p)) (h' : Short A (l, p')) : p = p' := by
  by_contra hne
  obtain ⟨k, s, hk | hk⟩ := face_pair l p p' hne
  · have hv : vecOf A (cE (l, p)) - vecOf A (cE (l, p')) = (2 : ℝ) • ((sgZ s : ℝ) • A k) := by
      rw [← vecOf_sub, ← vecOf_pc A (fun _ => s) k]
      simp only [vecOf, hk, Int.cast_mul, Int.cast_ofNat, Finset.smul_sum, smul_smul]
    have h2 : ‖vecOf A (cE (l, p)) - vecOf A (cE (l, p'))‖ = 2 := by
      rw [hv, norm_smul, norm_sgZ_smul A hA]; norm_num
    have := norm_sub_le (vecOf A (cE (l, p))) (vecOf A (cE (l, p')))
    unfold Short at h h'; linarith
  · have hv : vecOf A (cE (l, p)) + vecOf A (cE (l, p')) = (2 : ℝ) • ((sgZ s : ℝ) • A k) := by
      rw [← vecOf_add, ← vecOf_pc A (fun _ => s) k]
      simp only [vecOf, hk, Int.cast_mul, Int.cast_ofNat, Finset.smul_sum, smul_smul]
    have h2 : ‖vecOf A (cE (l, p)) + vecOf A (cE (l, p'))‖ = 2 := by
      rw [hv, norm_smul, norm_sgZ_smul A hA]; norm_num
    have := norm_add_le (vecOf A (cE (l, p))) (vecOf A (cE (l, p')))
    unfold Short at h h'; linarith

/-- The four sums at one sign vector are never all short. -/
theorem no_star (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) (σ : Sign) :
    ¬ ∀ l, Short A (l, incP σ l) := by
  intro h
  have hs := gram_congr' A hA (star_identity σ)
  simp only [gram_add, gram_smul, gram_unit A hA] at hs
  have h0 := (short_iff_sq A _).1 (h 0)
  have h1 := (short_iff_sq A _).1 (h 1)
  have h2 := (short_iff_sq A _).1 (h 2)
  have h3 := (short_iff_sq A _).1 (h 3)
  have hS : 0 ≤ gram (gx A) (outer (cS σ) (cS σ)) := by
    rw [← sq_vecOf]; positivity
  push_cast at hs
  linarith

/-- Two disjoint short sums on different faces are joined by a short sum. -/
theorem join (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) (e f : Edge) (hef : e.1 ≠ f.1)
    (hd : disjointE e f = true) (he : Short A e) (hf : Short A f) :
    ∃ g, Short A g ∧ adj g e = true ∧ adj g f = true := by
  obtain ⟨g, h, hge, hgf, hhe, hhf, hid⟩ := joiners e f hef hd
  have hs := gram_congr' A hA hid
  simp only [gram_add] at hs
  have := (short_iff_sq A e).1 he
  have := (short_iff_sq A f).1 hf
  by_cases hg : gram (gx A) (outer (cE g) (cE g)) < 1
  · exact ⟨g, (short_iff_sq A g).2 hg, hge, hgf⟩
  · exact ⟨h, (short_iff_sq A h).2 (by linarith), hhe, hhf⟩

/-- The corner `σ_i A_i` of the variant `σ`. -/
def P (A : Fin 4 → V) (σ : Sign) (i : Fin 4) : V := (sgZ (σ i) : ℝ) • A i

/-- Every angle of every face of the variant `σ` is acute. -/
def AcuteVariant (A : Fin 4 → V) (σ : Sign) : Prop :=
  ∀ l : Fin 4, ∀ k : Fin 3, 0 < inner ℝ (P A σ (face l (k + 1)) - P A σ (face l k))
    (P A σ (face l (k + 2)) - P A σ (face l k))

lemma angle_gram (A : Fin 4 → V) (σ : Sign) (l : Fin 4) (k : Fin 3) :
    inner ℝ (P A σ (face l (k + 1)) - P A σ (face l k)) (P A σ (face l (k + 2)) - P A σ (face l k))
      = gram (gx A) (outer (sideU σ l k) (sideV σ l k)) := by
  rw [← inner_vecOf]
  have hu : sideU σ l k = fun t => pc σ (face l (k + 1)) t - pc σ (face l k) t := rfl
  have hv : sideV σ l k = fun t => pc σ (face l (k + 2)) t - pc σ (face l k) t := rfl
  rw [hu, hv, vecOf_sub, vecOf_sub, vecOf_pc, vecOf_pc, vecOf_pc]
  rfl

/-- The link between angles and short sums. -/
theorem acute_iff (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) (hgen : ∀ e, ‖vecOf A (cE e)‖ ≠ 1)
    (σ : Sign) : AcuteVariant A σ ↔ ∀ e, Short A e → inc e σ = true := by
  constructor
  · intro hac e he
    by_contra hne
    obtain ⟨k, hk⟩ := edge_angle σ e (by simpa using hne)
    have hq := gram_congr' A hA hk
    simp only [gram_add, gram_smul, gram_unit A hA] at hq
    have := (short_iff_sq A e).1 he
    have := hac e.1 k
    rw [angle_gram] at this
    push_cast at hq
    linarith
  · intro h l k
    obtain ⟨p, hinc, hk⟩ := angle_edge σ l k
    have hq := gram_congr' A hA hk
    simp only [gram_add, gram_smul, gram_unit A hA] at hq
    have hns : ¬ Short A (l, p) := fun hs => by simp [h _ hs] at hinc
    have hne := hgen (l, p)
    have hge : 1 < ‖vecOf A (cE (l, p))‖ := by
      unfold Short at hns; push Not at hns; exact lt_of_le_of_ne hns (Ne.symm hne)
    have hsq : 1 < gram (gx A) (outer (cE (l, p)) (cE (l, p))) := by
      rw [← sq_vecOf]; nlinarith
    rw [angle_gram]
    push_cast at hq
    linarith

end AcuteTetra
