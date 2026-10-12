import LeanProofs.AcuteTetra.Main

/-!
# Acute tetrahedron: the paper's form of the count

An earlier version of the paper counts, over the eight
tetrahedra `T_X` (vertex `a` kept fixed), the number `N` with four acute faces and the number `C`
having one or two short face sums, and proves `N + C = 4` (Lemma 4). Here:

* `angle_identity` (Lemma 1): `(x - z)·(y - z) = (‖x + y - z‖² - 1)/2` for unit vectors;
* `threshold` (equation (3)): for an even and an odd sign vector, the squared totals add up to
  `2‖L‖² + 2`, where `L` is the vertex sum of their common face;
* `count_sixteen`, `count_eight`: `N + C = 8` over all sixteen sign vectors and `N + C = 4` over
  the eight with the first sign `+`.

`k σ` is the number of short face sums `‖Σ_{i ≠ l} σ_i A_i‖ < 1` of the variant `σ`.
-/

namespace AcuteTetra

open Finset

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Lemma 1.** The angle at `z` in `xyz` is tested by the fourth parallelogram corner. -/
theorem angle_identity (x y z : V) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    inner ℝ (x - z) (y - z) = (‖x + y - z‖ ^ 2 - 1) / 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have hx' := real_inner_self_eq_norm_sq x
  have hy' := real_inner_self_eq_norm_sq y
  have hz' := real_inner_self_eq_norm_sq z
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_comm x y, real_inner_comm x z, real_inner_comm y z] at *
  rw [hx'] at *; rw [hy'] at *; rw [hz'] at *
  rw [hx, hy, hz]; ring

/-! ## Finite facts -/

/-- Number of short entries incident to `σ`, read face by face. -/
theorem deg_eq : ∀ c : Fin 4 → Option (Bool × Bool), ∀ σ : Sign,
    deg c σ = ((List.finRange 4).filter fun l => c l == some (incP σ l)).length := by
  decide +kernel

/-- The face sum `Σ_{i ≠ l} σ_i A_i` is, up to sign, the entry `(l, incP σ l)`. -/
theorem drop_incP : ∀ σ : Sign, ∀ l : Fin 4,
    gramEq (outer (cE (l, incP σ l)) (cE (l, incP σ l))) (outer (cDrop σ l) (cDrop σ l)) = true := by
  decide

def evenSigns : List Sign := allSigns.filter fun σ => σ 0

/-- The paper's count, over all sixteen sign vectors and over the eight with `σ 0 = +`. -/
def identity16 (c : Fin 4 → Option (Bool × Bool)) : Bool :=
  (allSigns.filter (covers c)).length +
    (allSigns.filter fun σ => 1 ≤ deg c σ && deg c σ ≤ 2).length == 8

def identity8 (c : Fin 4 → Option (Bool × Bool)) : Bool :=
  (evenSigns.filter (covers c)).length +
    (evenSigns.filter fun σ => 1 ≤ deg c σ && deg c σ ≤ 2).length == 4

theorem comb16 : ∀ c : Fin 4 → Option (Bool × Bool), constraints c = true → identity16 c = true := by
  decide +kernel

theorem comb8 : ∀ c : Fin 4 → Option (Bool × Bool), constraints c = true → identity8 c = true := by
  decide +kernel

/-- Even/odd parity of a sign vector relative to `σ 0`: the number of `i ∈ {1,2,3}` flipped. -/
def oddSign (σ : Sign) : Bool := (σ 1 != σ 0) ^^ (σ 2 != σ 0) ^^ (σ 3 != σ 0)

/-- **Equation (3).** An even and an odd variant share exactly one face entry `e` (their common
face), and their squared totals add up to `2‖e‖² + 2`. -/
theorem threshold_fin : ∀ σ τ : Sign, oddSign σ = false → oddSign τ = true →
    ∃ e : Edge, inc e σ = true ∧ inc e τ = true ∧
      (∀ e' : Edge, inc e' σ = true → inc e' τ = true → e' = e) ∧
      gramEq (outer (cS σ) (cS σ) + outer (cS τ) (cS τ))
        ((2 : ℤ) • outer (cE e) (cE e) + (2 : ℤ) • unitM) = true := by
  decide +kernel

/-! ## Geometric statements -/

/-- The face sum of the variant `σ` opposite vertex `l`. -/
def faceSum (A : Fin 4 → V) (σ : Sign) (l : Fin 4) : V := vecOf A (cDrop σ l)

/-- The squared total of the variant `σ`. -/
def total (A : Fin 4 → V) (σ : Sign) : V := vecOf A (cS σ)

open Classical in
/-- `k`: the number of short face sums of the variant `σ`. -/
noncomputable def kShort (A : Fin 4 → V) (σ : Sign) : ℕ :=
  ((List.finRange 4).filter fun l => decide (‖faceSum A σ l‖ < 1)).length

lemma short_faceSum_iff (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) (σ : Sign) (l : Fin 4) :
    ‖faceSum A σ l‖ < 1 ↔ Short A (l, incP σ l) := by
  have h := gram_congr' A hA (drop_incP σ l)
  rw [← sq_vecOf, ← sq_vecOf] at h
  have hn : ‖vecOf A (cE (l, incP σ l))‖ = ‖faceSum A σ l‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h
  rw [Short, hn]

/-- **Equation (3), geometric form.** -/
theorem threshold (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) (σ τ : Sign)
    (hσ : oddSign σ = false) (hτ : oddSign τ = true) :
    ∃ e : Edge, inc e σ = true ∧ inc e τ = true ∧
      ‖total A σ‖ ^ 2 + ‖total A τ‖ ^ 2 = 2 * ‖vecOf A (cE e)‖ ^ 2 + 2 := by
  obtain ⟨e, hσe, hτe, -, h⟩ := threshold_fin σ τ hσ hτ
  refine ⟨e, hσe, hτe, ?_⟩
  have := gram_congr' A hA h
  simp only [gram_add, gram_smul, gram_unit A hA] at this
  rw [total, total, sq_vecOf, sq_vecOf, sq_vecOf, this]
  push_cast; ring

/-- A cell of the table is marked (its entry is short) exactly when its margins add to `< 4`. -/
theorem marked_iff (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) (σ τ : Sign)
    (hσ : oddSign σ = false) (hτ : oddSign τ = true) :
    ∃ e : Edge, inc e σ = true ∧ inc e τ = true ∧
      (Short A e ↔ ‖total A σ‖ ^ 2 + ‖total A τ‖ ^ 2 < 4) := by
  obtain ⟨e, hσe, hτe, h⟩ := threshold A hA σ τ hσ hτ
  refine ⟨e, hσe, hτe, ?_⟩
  rw [h, Short]
  constructor
  · intro h1; nlinarith [norm_nonneg (vecOf A (cE e))]
  · intro h1; nlinarith [norm_nonneg (vecOf A (cE e))]

lemma all_of_three_lt : ∀ f : Fin 4 → Bool, 3 < ((List.finRange 4).filter f).length →
    ∀ l, f l = true := by
  decide

/-- **Lemma 3.** The marks are nonempty (dimension 3), at most three lie on a line (no variant
has four short face sums) and at most one lies on each face (so at most four in total). -/
theorem restrictions [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 3) (A : Fin 4 → V)
    (hA : ∀ i, ‖A i‖ = 1) (hgen : ∀ e, ‖vecOf A (cE e)‖ ≠ 1) :
    (∃ e, Short A e) ∧ (∀ σ, kShort A σ ≤ 3) ∧
      (∀ l p p', Short A (l, p) → Short A (l, p') → p = p') := by
  classical
  refine ⟨exists_short hdim A hA hgen, fun σ => ?_, one_per_face A hA⟩
  have hns := no_star A hA σ
  unfold kShort
  by_contra hlt
  push Not at hlt
  have h4 := all_of_three_lt _ hlt
  exact hns fun l => (short_faceSum_iff A hA σ l).1 (by simpa using h4 l)

lemma kShort_eq_deg (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) (σ : Sign) :
    kShort A σ = deg (shortChoice A) σ := by
  classical
  rw [deg_eq, kShort]
  congr 1
  apply List.filter_congr
  intro l _
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, short_faceSum_iff A hA,
    short_iff_choice A hA]

open Classical in
/-- **Lemma 4 (sixteen sign vectors).** `N + C = 8`. -/
theorem count_sixteen [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 3) (A : Fin 4 → V)
    (hA : ∀ i, ‖A i‖ = 1) (hgen : ∀ e, ‖vecOf A (cE e)‖ ≠ 1) :
    (allSigns.filter fun σ => decide (AcuteVariant A σ)).length +
      (allSigns.filter fun σ => decide (1 ≤ kShort A σ ∧ kShort A σ ≤ 2)).length = 8 := by
  classical
  have hcons := constraints_of A hA hdim hgen
  have hid := comb16 _ hcons
  simp only [identity16, beq_iff_eq] at hid
  rw [← hid]
  congr 1
  · exact congrArg List.length (List.filter_congr fun σ _ => (covers_eq A hA hgen σ).symm)
  · exact congrArg List.length (List.filter_congr fun σ _ => by
      rw [kShort_eq_deg A hA]; simp)

open Classical in
/-- **Lemma 4.** Over the eight tetrahedra `T_X` (first vertex fixed), `N + C = 4`. -/
theorem count_eight [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 3) (A : Fin 4 → V)
    (hA : ∀ i, ‖A i‖ = 1) (hgen : ∀ e, ‖vecOf A (cE e)‖ ≠ 1) :
    (evenSigns.filter fun σ => decide (AcuteVariant A σ)).length +
      (evenSigns.filter fun σ => decide (1 ≤ kShort A σ ∧ kShort A σ ≤ 2)).length = 4 := by
  classical
  have hcons := constraints_of A hA hdim hgen
  have hid := comb8 _ hcons
  simp only [identity8, beq_iff_eq] at hid
  rw [← hid]
  congr 1
  · exact congrArg List.length (List.filter_congr fun σ _ => (covers_eq A hA hgen σ).symm)
  · exact congrArg List.length (List.filter_congr fun σ _ => by
      rw [kShort_eq_deg A hA]; simp)

end AcuteTetra
