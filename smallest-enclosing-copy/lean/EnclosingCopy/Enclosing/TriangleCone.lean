import EnclosingCopy.Enclosing.TriangleModel

/-!
# The cone density of a triangle

`coneVertexDensity K = (1/24) ∑_κ f(κ)` sums, over side tuples `κ : Fin 4 → Fin 3`, the integral
`f(κ)` of `|det|` over positions satisfying the cone condition.

* `coneTerm_perm`: `f(κ ∘ e) = f(κ)` (rows of the vertex matrix are permuted);
* `coneTerm_missing`: a tuple missing a side gives `0` (two non-parallel normals have no positive
  dependency);
* the remaining tuples have one side twice; they form three classes of `12` tuples each
  (`tuple_class`, `card_class`, both small finite checks);
* `coneTerm_canon`: for `κ = (k, k, i, j)`, `|det| = |s₁ - s₀| |D₃|`, the cone condition says that
  `x = -(Lᵢ s₂ + Lⱼ s₃)/Lₖ` lies strictly between `s₀` and `s₁`, and the inner integral is
  `Lₖ ((x - aₖ)(bₖ - x))₊`.
-/

namespace Enclosing
open MeasureTheory Set Matrix ENNReal

variable {K : Sides 3}

variable (K) in
/-- The cone-density integrand of a side tuple. -/
noncomputable def coneIntegrand (κ : Fin 4 → Fin 3) (s : Fin 4 → ℝ) : ℝ :=
  {s | vertexConeCondition K κ s}.indicator
    (fun s => |(vertexMatrix K (pointsOf κ s 0)).det|) s

variable (K) in
/-- The per-tuple term of the cone density. -/
noncomputable def coneTerm (κ : Fin 4 → Fin 3) : ℝ≥0∞ :=
  ∫⁻ s, ENNReal.ofReal (coneIntegrand K κ s)
    ∂(Measure.pi fun r => volume.restrict (Icc (K.a (κ r)) (K.b (κ r))))

lemma coneVertexDensity_eq : coneVertexDensity K = (1 / 24) * ∑ κ, coneTerm K κ := rfl

/-! ### Permuting the four points -/

lemma coneIntegrand_perm (κ : Fin 4 → Fin 3) (e : Equiv.Perm (Fin 4)) (s : Fin 4 → ℝ) :
    coneIntegrand K (κ ∘ e) s = coneIntegrand K κ (s ∘ e.symm) := by
  have hA : vertexMatrix K (pointsOf (κ ∘ e) s 0)
      = (vertexMatrix K (pointsOf κ (s ∘ e.symm) 0)).submatrix e id := by
    funext r c; simp [vertexMatrix, pointsOf]
  have hK : vertexConeCondition K (κ ∘ e) s ↔ vertexConeCondition K κ (s ∘ e.symm) := by
    unfold vertexConeCondition
    have hrow : ∀ r, row K (pointsOf (κ ∘ e) s 0 r) = row K (pointsOf κ (s ∘ e.symm) 0 (e r)) := by
      intro r; simp [pointsOf]
    simp_rw [hrow]
    constructor
    · rintro ⟨l, hl, hc⟩
      refine ⟨l ∘ e.symm, fun i => hl _, fun c => ?_⟩
      rw [← hc c, ← Equiv.sum_comp e]
      simp
    · rintro ⟨l, hl, hc⟩
      refine ⟨l ∘ e, fun i => hl _, fun c => ?_⟩
      rw [← hc c]
      exact Equiv.sum_comp e (fun j => l j * row K (pointsOf κ (s ∘ e.symm) 0 j) c)
  unfold coneIntegrand
  by_cases h : vertexConeCondition K (κ ∘ e) s
  · rw [indicator_of_mem (show s ∈ {s | vertexConeCondition K (κ ∘ e) s} from h),
      indicator_of_mem (show s ∘ e.symm ∈ {s | vertexConeCondition K κ s} from hK.1 h), hA,
      det_permute, abs_mul]
    have hs : |((Equiv.Perm.sign e : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]
    rw [hs, one_mul]
  · rw [indicator_of_notMem (show s ∉ {s | vertexConeCondition K (κ ∘ e) s} from h),
      indicator_of_notMem (show s ∘ e.symm ∉ {s | vertexConeCondition K κ s} from
        fun h' => h (hK.2 h'))]

lemma coneTerm_perm (κ : Fin 4 → Fin 3) (e : Equiv.Perm (Fin 4)) :
    coneTerm K (κ ∘ e) = coneTerm K κ := by
  have hmp := measurePreserving_piCongrLeft
    (fun r => volume.restrict (Icc (K.a (κ r)) (K.b (κ r)))) e
  have happ : ∀ σ : Fin 4 → ℝ, MeasurableEquiv.piCongrLeft (fun _ => ℝ) e σ = σ ∘ e.symm := by
    intro σ; funext j
    rw [← e.apply_symm_apply j]
    simp only [MeasurableEquiv.coe_piCongrLeft, Function.comp_apply, Equiv.symm_apply_apply]
    exact Equiv.piCongrLeft_apply_apply _ _ _ _
  unfold coneTerm
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [happ, ← coneIntegrand_perm]
  rfl

/-- Tuples with the same number of points on each side differ by a permutation. -/
lemma exists_perm_of_card {κ κ' : Fin 4 → Fin 3}
    (h : ∀ j, (Finset.univ.filter fun r => κ' r = j).card =
      (Finset.univ.filter fun r => κ r = j).card) :
    ∃ e : Equiv.Perm (Fin 4), κ' = κ ∘ e := by
  have hf : ∀ j, {r // κ' r = j} ≃ {r // κ r = j} := fun j =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype, h j])
  refine ⟨Equiv.ofFiberEquiv hf, funext fun r => ?_⟩
  exact (Equiv.ofFiberEquiv_map hf r).symm

lemma coneTerm_of_card {κ κ' : Fin 4 → Fin 3}
    (h : ∀ j, (Finset.univ.filter fun r => κ' r = j).card =
      (Finset.univ.filter fun r => κ r = j).card) :
    coneTerm K κ' = coneTerm K κ := by
  obtain ⟨e, rfl⟩ := exists_perm_of_card h
  exact coneTerm_perm κ e

/-! ### A tuple missing a side contributes nothing -/

/-- If `κ` takes only the values `i₁, i₂`, the `u`-columns of the cone condition force every
weight on side `i₁` to vanish. -/
lemma no_weight_on_side (hG : GoodSides K) {κ : Fin 4 → Fin 3} {i₁ i₂ : Fin 3} (h12 : i₁ ≠ i₂)
    (hκ : ∀ r, κ r = i₁ ∨ κ r = i₂) {s : Fin 4 → ℝ} (hc : vertexConeCondition K κ s) :
    ∀ r, κ r ≠ i₁ := by
  obtain ⟨l, hl, he⟩ := hc
  have h1 := he 1
  have h2 := he 2
  simp only [row, pointsOf, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.cons_val_zero, Matrix.tail_cons, if_neg (by decide : (1 : Fin 4) ≠ 0),
    if_neg (by decide : (2 : Fin 4) ≠ 0)] at h1 h2
  set c := cross (K.u i₁) (K.u i₂)
  have hc0 : c ≠ 0 := tri_cross_ne hG h12
  have hterm : ∀ r, l r * (K.u (κ r)).1 * (K.u i₂).2 - l r * (K.u (κ r)).2 * (K.u i₂).1
      = c * (if κ r = i₁ then l r else 0) := by
    intro r
    rcases hκ r with h | h
    · rw [if_pos h, h]; simp only [c, cross]; ring
    · rw [if_neg (by rw [h]; exact h12.symm), h]; ring
  have hsum : c * ∑ r, (if κ r = i₁ then l r else 0) = 0 := by
    rw [Finset.mul_sum, ← Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, h1, h2]
    ring
  have hS : ∑ r, (if κ r = i₁ then l r else 0) = 0 :=
    (mul_eq_zero.mp hsum).resolve_left hc0
  intro r hr
  have hpos : 0 < ∑ r, (if κ r = i₁ then l r else 0) :=
    Finset.sum_pos' (fun q _ => by split_ifs <;> [exact (hl q).le; exact le_rfl])
      ⟨r, Finset.mem_univ _, by rw [if_pos hr]; exact hl r⟩
  linarith

lemma cone_false_of_missing (hG : GoodSides K) {κ : Fin 4 → Fin 3} {j : Fin 3}
    (hj : ∀ r, κ r ≠ j) (s : Fin 4 → ℝ) : ¬ vertexConeCondition K κ s := by
  intro hc
  obtain ⟨i₁, i₂, h12, hcover⟩ : ∃ i₁ i₂ : Fin 3, i₁ ≠ i₂ ∧ ∀ x, x = j ∨ x = i₁ ∨ x = i₂ := by
    fin_cases j
    · exact ⟨1, 2, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide⟩
  have hκ : ∀ r, κ r = i₁ ∨ κ r = i₂ := fun r =>
    (hcover (κ r)).resolve_left (hj r)
  have hκ' : ∀ r, κ r = i₂ ∨ κ r = i₁ := fun r => (hκ r).symm
  have n1 := no_weight_on_side hG h12 hκ hc
  have n2 := no_weight_on_side hG h12.symm hκ' hc
  rcases hκ 0 with h | h
  · exact n1 0 h
  · exact n2 0 h

lemma coneTerm_missing (hG : GoodSides K) {κ : Fin 4 → Fin 3} {j : Fin 3}
    (hj : ∀ r, κ r ≠ j) : coneTerm K κ = 0 := by
  have h0 : ∀ s, coneIntegrand K κ s = 0 := fun s =>
    indicator_of_notMem (show s ∉ {s | vertexConeCondition K κ s} from
      fun h => cone_false_of_missing hG hj s h) _
  unfold coneTerm
  simp [h0]

/-! ### Counting tuples -/

/-- The canonical tuple with side `k` twice: `(0,0,1,2)`, `(1,1,0,2)`, `(2,2,0,1)`. -/
def canon : Fin 3 → Fin 4 → Fin 3 := ![![0, 0, 1, 2], ![1, 1, 0, 2], ![2, 2, 0, 1]]

/-- The number of points of a tuple on each side. -/
def sideCount (κ : Fin 4 → Fin 3) (j : Fin 3) : ℕ := (Finset.univ.filter fun r => κ r = j).card

/-- Every tuple misses a side or has the side counts of exactly one canonical tuple. -/
lemma tuple_class (κ : Fin 4 → Fin 3) :
    ((∃ j, ∀ r, κ r ≠ j) ∧ ∀ k, sideCount κ ≠ sideCount (canon k)) ∨
      ∃ k, sideCount κ = sideCount (canon k) ∧ ∀ k', sideCount κ = sideCount (canon k') → k' = k := by
  revert κ
  decide

lemma card_class (k : Fin 3) :
    (Finset.univ.filter fun κ : Fin 4 → Fin 3 => sideCount κ = sideCount (canon k)).card = 12 := by
  revert k
  decide

/-! ### The canonical tuple `(k, k, i, j)` -/

/-- The point `x` on side `k` determined by the positions on sides `i` and `j`. -/
noncomputable def xpos (K : Sides 3) (k i j : Fin 3) (si sj : ℝ) : ℝ :=
  -(sideL K i * si + sideL K j * sj) / sideL K k

/-- The cone condition for `(k, k, i, j)` as four scalar equations. -/
lemma cone_canon_eqs (k i j : Fin 3) (s : Fin 4 → ℝ) :
    vertexConeCondition K ![k, k, i, j] s ↔ ∃ l : Fin 4 → ℝ, (∀ r, 0 < l r) ∧
      l 0 * K.h k + l 1 * K.h k + l 2 * K.h i + l 3 * K.h j = 1 ∧
      l 0 * (K.u k).1 + l 1 * (K.u k).1 + l 2 * (K.u i).1 + l 3 * (K.u j).1 = 0 ∧
      l 0 * (K.u k).2 + l 1 * (K.u k).2 + l 2 * (K.u i).2 + l 3 * (K.u j).2 = 0 ∧
      l 0 * s 0 + l 1 * s 1 + l 2 * s 2 + l 3 * s 3 = 0 := by
  unfold vertexConeCondition
  constructor
  · rintro ⟨l, hl, he⟩
    have e0 := he 0
    have e1 := he 1
    have e2 := he 2
    have e3 := he 3
    simp [Fin.sum_univ_four, row, pointsOf] at e0 e1 e2 e3
    exact ⟨l, hl, e0, e1, e2, by linarith⟩
  · rintro ⟨l, hl, e0, e1, e2, e3⟩
    refine ⟨l, hl, fun c => ?_⟩
    fin_cases c <;> simp [Fin.sum_univ_four, row, pointsOf] <;> linarith

/-- The three sides in the order `k, i, j`. -/
structure Triple (k i j : Fin 3) : Prop where
  sum3 : ∀ f : Fin 3 → ℝ, ∑ x, f x = f k + f i + f j
  ki : k ≠ i
  kj : k ≠ j
  ij : i ≠ j

lemma Triple.sum_u1 {k i j : Fin 3} (t : Triple k i j) :
    sideL K k * (K.u k).1 + sideL K i * (K.u i).1 + sideL K j * (K.u j).1 = 0 := by
  have h := K.sum_u1; rw [t.sum3] at h; exact h

lemma Triple.sum_u2 {k i j : Fin 3} (t : Triple k i j) :
    sideL K k * (K.u k).2 + sideL K i * (K.u i).2 + sideL K j * (K.u j).2 = 0 := by
  have h := K.sum_u2; rw [t.sum3] at h; exact h

lemma Triple.sum_h {k i j : Fin 3} (t : Triple k i j) :
    sideL K k * K.h k + sideL K i * K.h i + sideL K j * K.h j = 2 := by
  have h := K.sum_h; rw [t.sum3] at h; exact h

/-- **The cone condition for `(k, k, i, j)`**: when `s₀ ≠ s₁`, it says that `x` lies strictly
between `s₀` and `s₁`. -/
lemma cone_canon_iff (hG : GoodSides K) {k i j : Fin 3} (t : Triple k i j) (s : Fin 4 → ℝ)
    (hs : s 0 ≠ s 1) :
    vertexConeCondition K ![k, k, i, j] s ↔
      min (s 0) (s 1) < xpos K k i j (s 2) (s 3) ∧ xpos K k i j (s 2) (s 3) < max (s 0) (s 1) := by
  have hLk := sideL_pos (K := K) k
  have hLi := sideL_pos (K := K) i
  have hLj := sideL_pos (K := K) j
  set x := xpos K k i j (s 2) (s 3) with hx
  have hxL : sideL K k * x = -(sideL K i * s 2 + sideL K j * s 3) := by
    rw [hx, xpos]; field_simp
  rw [cone_canon_eqs]
  constructor
  · rintro ⟨l, hl, -, e1, e2, e3⟩
    set M := l 0 + l 1
    have s1 := t.sum_u1 (K := K)
    have s2 := t.sum_u2 (K := K)
    have hc : cross (K.u i) (K.u j) ≠ 0 := tri_cross_ne hG t.ij
    have hα : (l 2 * sideL K k - M * sideL K i) * cross (K.u i) (K.u j) = 0 := by
      simp only [cross, M]
      linear_combination ((K.u j).2 * sideL K k) * e1 - ((K.u j).2 * (l 0 + l 1)) * s1 -
        ((K.u j).1 * sideL K k) * e2 + ((K.u j).1 * (l 0 + l 1)) * s2
    have hβ : (l 3 * sideL K k - M * sideL K j) * cross (K.u i) (K.u j) = 0 := by
      simp only [cross, M]
      linear_combination -((K.u i).2 * sideL K k) * e1 + ((K.u i).2 * (l 0 + l 1)) * s1 +
        ((K.u i).1 * sideL K k) * e2 - ((K.u i).1 * (l 0 + l 1)) * s2
    have h2 := (mul_eq_zero.mp hα).resolve_right hc
    have h3 := (mul_eq_zero.mp hβ).resolve_right hc
    have key : sideL K k * (l 0 * (s 0 - x) + l 1 * (s 1 - x)) = 0 := by
      simp only [M] at h2 h3
      linear_combination sideL K k * e3 - s 2 * h2 - s 3 * h3 - (l 0 + l 1) * hxL
    have key' : l 0 * (s 0 - x) + l 1 * (s 1 - x) = 0 :=
      (mul_eq_zero.mp key).resolve_left hLk.ne'
    have h0 := hl 0
    have h1 := hl 1
    rcases lt_or_gt_of_ne hs with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]
      constructor
      · by_contra hc'
        rw [not_lt] at hc'
        nlinarith [mul_nonneg h0.le (sub_nonneg.mpr hc'), mul_pos h1 (sub_pos.mpr (lt_of_le_of_lt hc' h))]
      · by_contra hc'
        rw [not_lt] at hc'
        nlinarith [mul_nonneg h1.le (sub_nonneg.mpr hc'), mul_pos h0 (sub_pos.mpr (lt_of_lt_of_le h hc'))]
    · rw [min_eq_right h.le, max_eq_left h.le]
      constructor
      · by_contra hc'
        rw [not_lt] at hc'
        nlinarith [mul_nonneg h1.le (sub_nonneg.mpr hc'), mul_pos h0 (sub_pos.mpr (lt_of_le_of_lt hc' h))]
      · by_contra hc'
        rw [not_lt] at hc'
        nlinarith [mul_nonneg h0.le (sub_nonneg.mpr hc'), mul_pos h1 (sub_pos.mpr (lt_of_lt_of_le h hc'))]
  · rintro ⟨hlo, hhi⟩
    have hd : s 1 - s 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
    have hw0 : 0 < (s 1 - x) / (s 1 - s 0) := by
      rcases lt_or_gt_of_ne hs with h | h
      · rw [min_eq_left h.le, max_eq_right h.le] at *
        exact div_pos (by linarith) (by linarith)
      · rw [min_eq_right h.le, max_eq_left h.le] at *
        exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hw1 : 0 < (x - s 0) / (s 1 - s 0) := by
      rcases lt_or_gt_of_ne hs with h | h
      · rw [min_eq_left h.le, max_eq_right h.le] at *
        exact div_pos (by linarith) (by linarith)
      · rw [min_eq_right h.le, max_eq_left h.le] at *
        exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hsum01 : (s 1 - x) / (s 1 - s 0) + (x - s 0) / (s 1 - s 0) = 1 := by
      field_simp; ring
    have hmom : (s 1 - x) / (s 1 - s 0) * s 0 + (x - s 0) / (s 1 - s 0) * s 1 = x := by
      field_simp; ring
    refine ⟨![sideL K k / 2 * ((s 1 - x) / (s 1 - s 0)), sideL K k / 2 * ((x - s 0) / (s 1 - s 0)),
      sideL K i / 2, sideL K j / 2], fun r => ?_, ?_, ?_, ?_, ?_⟩
    · fin_cases r <;> simp <;> positivity
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.cons_val_three, Matrix.tail_cons]
      linear_combination (K.h k / 2 * sideL K k) * hsum01 + t.sum_h (K := K) / 2
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.cons_val_three, Matrix.tail_cons]
      linear_combination ((K.u k).1 / 2 * sideL K k) * hsum01 + t.sum_u1 (K := K) / 2
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.cons_val_three, Matrix.tail_cons]
      linear_combination ((K.u k).2 / 2 * sideL K k) * hsum01 + t.sum_u2 (K := K) / 2
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.cons_val_three, Matrix.tail_cons]
      linear_combination (sideL K k / 2) * hmom + hxL / 2

lemma triple0 : Triple 0 1 2 := ⟨fun f => Fin.sum_univ_three f, by decide, by decide, by decide⟩
lemma triple1 : Triple 1 0 2 :=
  ⟨fun f => by rw [Fin.sum_univ_three]; ring, by decide, by decide, by decide⟩
lemma triple2 : Triple 2 0 1 :=
  ⟨fun f => by rw [Fin.sum_univ_three]; ring, by decide, by decide, by decide⟩

lemma det_canon0 (s : Fin 4 → ℝ) :
    (vertexMatrix K (pointsOf ![0, 0, 1, 2] s 0)).det = (s 0 - s 1) * D3 K := by
  simp [vertexMatrix, row, pointsOf, Matrix.det_succ_row_zero, Fin.sum_univ_succ, D3,
    Fin.succAbove]
  ring

lemma det_canon1 (s : Fin 4 → ℝ) :
    (vertexMatrix K (pointsOf ![1, 1, 0, 2] s 0)).det = (s 1 - s 0) * D3 K := by
  simp [vertexMatrix, row, pointsOf, Matrix.det_succ_row_zero, Fin.sum_univ_succ, D3,
    Fin.succAbove]
  ring

lemma det_canon2 (s : Fin 4 → ℝ) :
    (vertexMatrix K (pointsOf ![2, 2, 0, 1] s 0)).det = (s 0 - s 1) * D3 K := by
  simp [vertexMatrix, row, pointsOf, Matrix.det_succ_row_zero, Fin.sum_univ_succ, D3,
    Fin.succAbove]
  ring

/-! ### The inner integral over the two points on side `k` -/

/-- Pairs with `x` strictly between them. -/
def betweenSet (x : ℝ) : Set (ℝ × ℝ) := {q | min q.1 q.2 < x ∧ x < max q.1 q.2}

/-- For `q₁ < x`, the inner integrand is the indicator of `q₂ > x`. -/
lemma pair_slice_lt {x q₁ : ℝ} (h : q₁ < x) (q₂ : ℝ) :
    (betweenSet x).indicator (fun q => |q.2 - q.1|) (q₁, q₂) =
      (Ioi x).indicator (fun q₂ => -q₁ - (-1) * q₂) q₂ := by
  by_cases h2 : x < q₂
  · rw [indicator_of_mem (show q₂ ∈ Ioi x from h2), indicator_of_mem]
    · rw [abs_of_pos (by simp only; linarith)]; ring
    · simp only [betweenSet, mem_ofPred_eq]
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]; exact ⟨h, h2⟩
  · rw [indicator_of_notMem (show q₂ ∉ Ioi x from h2), indicator_of_notMem]
    simp only [betweenSet, mem_ofPred_eq, not_and, not_lt]
    intro _
    exact max_le h.le (not_lt.mp h2)

lemma pair_slice_gt {x q₁ : ℝ} (h : x < q₁) (q₂ : ℝ) :
    (betweenSet x).indicator (fun q => |q.2 - q.1|) (q₁, q₂) =
      (Iio x).indicator (fun q₂ => q₁ - 1 * q₂) q₂ := by
  by_cases h2 : q₂ < x
  · rw [indicator_of_mem (show q₂ ∈ Iio x from h2), indicator_of_mem]
    · rw [abs_of_neg (by simp only; linarith)]; ring
    · simp only [betweenSet, mem_ofPred_eq]
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]; exact ⟨h2, h⟩
  · rw [indicator_of_notMem (show q₂ ∉ Iio x from h2), indicator_of_notMem]
    simp only [betweenSet, mem_ofPred_eq, not_and, not_lt]
    intro h'
    exact absurd h' (not_lt.mpr (le_min h.le (not_lt.mp h2)))

lemma pair_slice_eq {x : ℝ} (q₂ : ℝ) :
    (betweenSet x).indicator (fun q => |q.2 - q.1|) (x, q₂) = 0 := by
  rw [indicator_of_notMem]
  simp only [betweenSet, mem_ofPred_eq, not_and, not_lt]
  intro h
  rcases le_total x q₂ with h2 | h2
  · rw [min_eq_left h2] at h; exact absurd h (lt_irrefl x)
  · exact max_le le_rfl h2

/-- `∫⁻_{[a,b]} 1_{S}(q) ofReal (f q)` for `S ∩ [a,b]` an interval `[p, q]` up to null sets. -/
lemma lintegral_slice {a b p q : ℝ} {S : Set ℝ} (hS : MeasurableSet S) {f : ℝ → ℝ}
    (hf : Continuous f) (hpq : p ≤ q) (hSI : S ∩ Icc a b =ᵐ[volume] Icc p q)
    (hnn : ∀ y ∈ Icc p q, 0 ≤ f y) :
    ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (f y)) y ∂(volume.restrict (Icc a b)) =
      ENNReal.ofReal (∫ y in p..q, f y) := by
  rw [lintegral_indicator hS, Measure.restrict_restrict hS, Measure.restrict_congr_set hSI,
    lintegral_Icc_ofReal hf hpq hnn]

lemma inter_Ioi_Icc {a b x : ℝ} (hx : a < x) (_hxb : x < b) :
    Ioi x ∩ Icc a b =ᵐ[volume] Icc x b := by
  have : Ioi x ∩ Icc a b = Ioc x b := by
    ext y; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩
  rw [this]; exact Ioc_ae_eq_Icc

lemma inter_Iio_Icc {a b x : ℝ} (_hx : a < x) (hxb : x < b) :
    Iio x ∩ Icc a b =ᵐ[volume] Icc a x := by
  have : Iio x ∩ Icc a b = Ico a x := by
    ext y; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, h2, by linarith⟩
  rw [this]; exact Ico_ae_eq_Icc

/-- **The two points on side `k`**: `∫∫_{[a,b]²} 1{x between q₁, q₂} |q₂ - q₁| = (b-a) ((x-a)(b-x))₊`. -/
lemma inner_pair {a b : ℝ} (hab : a < b) (x : ℝ) :
    ∫⁻ q₁, ∫⁻ q₂, ENNReal.ofReal ((betweenSet x).indicator
        (fun q => |q.2 - q.1|) (q₁, q₂)) ∂(volume.restrict (Icc a b)) ∂(volume.restrict (Icc a b))
      = ENNReal.ofReal ((b - a) * max 0 ((x - a) * (b - x))) := by
  by_cases hx : a < x ∧ x < b
  swap
  · have hz : ∀ q₁ ∈ Icc a b, ∀ q₂ ∈ Icc a b, (betweenSet x).indicator (fun q => |q.2 - q.1|) (q₁, q₂) = 0 := by
      intro q₁ h₁ q₂ h₂
      rw [indicator_of_notMem]
      rintro ⟨hlo, hhi⟩
      exact hx ⟨lt_of_le_of_lt (le_min h₁.1 h₂.1) hlo, lt_of_lt_of_le hhi (max_le h₁.2 h₂.2)⟩
    have hmax : max 0 ((x - a) * (b - x)) = 0 := by
      apply max_eq_left
      rcases not_and_or.mp hx with h | h
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.mp h]) (by linarith [not_lt.mp h])
      · exact mul_nonpos_of_nonneg_of_nonpos (by linarith [not_lt.mp h]) (by linarith [not_lt.mp h])
    rw [hmax, mul_zero, ENNReal.ofReal_zero]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q₁ h₁
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q₂ h₂
    rw [hz q₁ h₁ q₂ h₂, ENNReal.ofReal_zero]
  obtain ⟨hax, hxb⟩ := hx
  set g₁ : ℝ → ℝ := fun q => (b ^ 2 - x ^ 2) / 2 - (b - x) * q
  set g₂ : ℝ → ℝ := fun q => -(x ^ 2 - a ^ 2) / 2 - (-(x - a)) * q
  -- the integral over `q₂`
  have hin : ∀ q₁ ∈ Icc a b, ∫⁻ q₂, ENNReal.ofReal ((betweenSet x).indicator (fun q => |q.2 - q.1|) (q₁, q₂))
      ∂(volume.restrict (Icc a b)) = (Iio x).indicator (fun q => ENNReal.ofReal (g₁ q)) q₁ +
        (Ioi x).indicator (fun q => ENNReal.ofReal (g₂ q)) q₁ := by
    intro q₁ h₁
    rcases lt_trichotomy q₁ x with h | h | h
    · rw [indicator_of_mem (show q₁ ∈ Iio x from h),
        indicator_of_notMem (show q₁ ∉ Ioi x from fun h' => lt_asymm h h'), add_zero]
      simp_rw [pair_slice_lt h]
      have e : ∀ y, ENNReal.ofReal ((Ioi x).indicator (fun q₂ => -q₁ - (-1) * q₂) y) =
          (Ioi x).indicator (fun q₂ => ENNReal.ofReal (-q₁ - (-1) * q₂)) y := by
        intro y; by_cases hy : y ∈ Ioi x
        · rw [indicator_of_mem hy, indicator_of_mem hy]
        · rw [indicator_of_notMem hy, indicator_of_notMem hy, ENNReal.ofReal_zero]
      simp_rw [e]
      rw [lintegral_slice measurableSet_Ioi (by fun_prop) hxb.le (inter_Ioi_Icc hax hxb)
        (fun y hy => by linarith [hy.1]), integral_affine]
      congr 1; simp only [g₁]; ring
    · subst h
      simp_rw [pair_slice_eq, ENNReal.ofReal_zero, lintegral_zero]
      rw [indicator_of_notMem (by simp : q₁ ∉ Iio q₁),
        indicator_of_notMem (by simp : q₁ ∉ Ioi q₁), add_zero]
    · rw [indicator_of_notMem (show q₁ ∉ Iio x from fun h' => lt_asymm h h'),
        indicator_of_mem (show q₁ ∈ Ioi x from h), zero_add]
      simp_rw [pair_slice_gt h]
      have e : ∀ y, ENNReal.ofReal ((Iio x).indicator (fun q₂ => q₁ - 1 * q₂) y) =
          (Iio x).indicator (fun q₂ => ENNReal.ofReal (q₁ - 1 * q₂)) y := by
        intro y; by_cases hy : y ∈ Iio x
        · rw [indicator_of_mem hy, indicator_of_mem hy]
        · rw [indicator_of_notMem hy, indicator_of_notMem hy, ENNReal.ofReal_zero]
      simp_rw [e]
      rw [lintegral_slice measurableSet_Iio (by fun_prop) hax.le (inter_Iio_Icc hax hxb)
        (fun y hy => by linarith [hy.2]), integral_affine]
      congr 1; simp only [g₂]; ring
  have hae : (fun q₁ => ∫⁻ q₂, ENNReal.ofReal ((betweenSet x).indicator (fun q => |q.2 - q.1|)
      (q₁, q₂)) ∂(volume.restrict (Icc a b))) =ᵐ[volume.restrict (Icc a b)]
      fun q₁ => (Iio x).indicator (fun q => ENNReal.ofReal (g₁ q)) q₁ +
        (Ioi x).indicator (fun q => ENNReal.ofReal (g₂ q)) q₁ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q₁ h₁
    exact hin q₁ h₁
  rw [lintegral_congr_ae hae]
  rw [lintegral_add_left ((by fun_prop : Measurable fun q => ENNReal.ofReal (g₁ q)).indicator
      measurableSet_Iio),
    lintegral_slice measurableSet_Iio (by fun_prop) hax.le (inter_Iio_Icc hax hxb)
      (fun y hy => by simp only [g₁]; nlinarith [hy.2]),
    lintegral_slice measurableSet_Ioi (by fun_prop) hxb.le (inter_Ioi_Icc hax hxb)
      (fun y hy => by simp only [g₂]; nlinarith [hy.1]),
    integral_affine, integral_affine,
    ← ENNReal.ofReal_add
      (by rw [show (b ^ 2 - x ^ 2) / 2 * (x - a) - (b - x) * (x ^ 2 - a ^ 2) / 2
        = (b - x) * (x - a) * (b - a) / 2 by ring]
          exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
            zero_le_two)
      (by rw [show -(x ^ 2 - a ^ 2) / 2 * (b - x) - -(x - a) * (b ^ 2 - x ^ 2) / 2
        = (b - x) * (x - a) * (b - a) / 2 by ring]
          exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
            zero_le_two),
    max_eq_right (by nlinarith)]
  congr 1
  ring

/-! ### Fubini for a canonical tuple -/

variable (K) in
/-- Lebesgue measure on side `q`. -/
noncomputable abbrev sideMeasure (q : Fin 3) : Measure ℝ := volume.restrict (Icc (K.a q) (K.b q))

/-- `Fin 4 ≃ Fin 2 ⊕ Fin 2`: the points `2, 3` on sides `i, j`, the points `0, 1` on side `k`. -/
def split4 : Fin 4 ≃ Fin 2 ⊕ Fin 2 where
  toFun := ![Sum.inr 0, Sum.inr 1, Sum.inl 0, Sum.inl 1]
  invFun := Sum.elim ![2, 3] ![0, 1]
  left_inv := by decide
  right_inv := by decide

lemma mp_quad (k i j : Fin 3) :
    MeasurePreserving (fun σ : Fin 4 → ℝ => ((σ 2, σ 3), (σ 0, σ 1)))
      (Measure.pi fun r => sideMeasure K (![k, k, i, j] r))
      (((sideMeasure K i).prod (sideMeasure K j)).prod ((sideMeasure K k).prod (sideMeasure K k))) := by
  let κ' : Fin 2 ⊕ Fin 2 → Fin 3 := Sum.elim ![i, j] (fun _ => k)
  let μ : Fin 2 ⊕ Fin 2 → Measure ℝ := fun q => sideMeasure K (κ' q)
  have : ∀ a, SigmaFinite (![sideMeasure K i, sideMeasure K j] a) :=
    Fin.forall_fin_two.2 ⟨inferInstanceAs (SigmaFinite (sideMeasure K i)),
      inferInstanceAs (SigmaFinite (sideMeasure K j))⟩
  have : ∀ q, SigmaFinite (μ q) := fun q =>
    inferInstanceAs (SigmaFinite (volume.restrict (Icc (K.a (κ' q)) (K.b (κ' q)))))
  have h1 := measurePreserving_piCongrLeft μ split4
  have h2 := measurePreserving_sumPiEquivProdPi μ
  have e1 : (Measure.pi fun r => μ (split4 r)) = Measure.pi fun r => sideMeasure K (![k, k, i, j] r) := by
    congr 1; funext r; fin_cases r <;> rfl
  have e2 : (Measure.pi fun a => μ (Sum.inl a)) = Measure.pi ![sideMeasure K i, sideMeasure K j] := by
    congr 1; funext a; fin_cases a <;> rfl
  have e3 : (Measure.pi fun b => μ (Sum.inr b)) = Measure.pi fun _ => sideMeasure K k := rfl
  rw [e1] at h1
  rw [e2, e3] at h2
  have h3 := (measurePreserving_finTwoArrow_vec (sideMeasure K i) (sideMeasure K j)).prod
    (measurePreserving_finTwoArrow (sideMeasure K k))
  have h := h3.comp (h2.comp h1)
  convert h using 1
  funext σ
  have hσ : ∀ r : Fin 4, (MeasurableEquiv.piCongrLeft (fun _ => ℝ) split4 σ) (split4 r) = σ r :=
    fun r => Equiv.piCongrLeft_apply_apply _ _ _ _
  simp only [Function.comp_apply, Prod.map, MeasurableEquiv.sumPiEquivProdPi]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · exact (hσ 2).symm
  · exact (hσ 3).symm
  · exact (hσ 0).symm
  · exact (hσ 1).symm

lemma continuous_xpos (k i j : Fin 3) : Continuous fun p : ℝ × ℝ => xpos K k i j p.1 p.2 := by
  unfold xpos; fun_prop

/-- The canonical integrand: `|D₃|` times the indicator that `x` lies between `s₀` and `s₁`,
weighted by `|s₁ - s₀|`. -/
lemma coneIntegrand_canon (hG : GoodSides K) {k i j : Fin 3} (t : Triple k i j)
    (hdet : ∀ s, |(vertexMatrix K (pointsOf ![k, k, i, j] s 0)).det| = |s 1 - s 0| * |D3 K|)
    (s : Fin 4 → ℝ) :
    coneIntegrand K ![k, k, i, j] s = |D3 K| *
      (betweenSet (xpos K k i j (s 2) (s 3))).indicator (fun q => |q.2 - q.1|) (s 0, s 1) := by
  unfold coneIntegrand
  by_cases hs : s 0 = s 1
  · have h0 : |(vertexMatrix K (pointsOf ![k, k, i, j] s 0)).det| = 0 := by
      rw [hdet, hs, sub_self, abs_zero, zero_mul]
    have h0' : (betweenSet (xpos K k i j (s 2) (s 3))).indicator (fun q => |q.2 - q.1|)
        (s 0, s 1) = 0 := by
      by_cases hm : (s 0, s 1) ∈ betweenSet (xpos K k i j (s 2) (s 3))
      · rw [indicator_of_mem hm]; simp [hs]
      · rw [indicator_of_notMem hm]
    rw [h0', mul_zero]
    by_cases hc : s ∈ {s | vertexConeCondition K ![k, k, i, j] s}
    · rw [indicator_of_mem hc, h0]
    · rw [indicator_of_notMem hc]
  · have hiff := cone_canon_iff hG t s hs
    by_cases hc : vertexConeCondition K ![k, k, i, j] s
    · rw [indicator_of_mem (show s ∈ {s | vertexConeCondition K ![k, k, i, j] s} from hc),
        indicator_of_mem (show (s 0, s 1) ∈ betweenSet (xpos K k i j (s 2) (s 3)) from hiff.1 hc),
        hdet, mul_comm]
    · rw [indicator_of_notMem (show s ∉ {s | vertexConeCondition K ![k, k, i, j] s} from hc),
        indicator_of_notMem (show (s 0, s 1) ∉ betweenSet (xpos K k i j (s 2) (s 3)) from
          fun h => hc (hiff.2 h)), mul_zero]

/-- **The term of a canonical tuple** `(k, k, i, j)`:
`|D₃| Lₖ ∫∫ ((x - aₖ)(bₖ - x))₊ dsᵢ dsⱼ`. -/
theorem coneTerm_canon (hG : GoodSides K) {k i j : Fin 3} (t : Triple k i j)
    (hdet : ∀ s, |(vertexMatrix K (pointsOf ![k, k, i, j] s 0)).det| = |s 1 - s 0| * |D3 K|) :
    coneTerm K ![k, k, i, j] = ENNReal.ofReal |D3 K| * ENNReal.ofReal (sideL K k *
      ∫ si in K.a i..K.b i, ∫ sj in K.a j..K.b j,
        max 0 ((xpos K k i j si sj - K.a k) * (K.b k - xpos K k i j si sj))) := by
  let G : (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((betweenSet (xpos K k i j p.1.1 p.1.2)).indicator (fun q => |q.2 - q.1|) p.2)
  have hGm : Measurable G := by
    have hset : MeasurableSet {p : (ℝ × ℝ) × (ℝ × ℝ) |
        min p.2.1 p.2.2 < xpos K k i j p.1.1 p.1.2 ∧ xpos K k i j p.1.1 p.1.2 < max p.2.1 p.2.2} := by
      have hx := (continuous_xpos (K := K) k i j).comp
        (continuous_fst : Continuous fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1)
      exact (measurableSet_lt (by fun_prop) hx.measurable).inter
        (measurableSet_lt hx.measurable (by fun_prop))
    exact ENNReal.measurable_ofReal.comp
      ((by fun_prop : Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => |p.2.2 - p.2.1|).indicator hset)
  have hcoe : ∀ s : Fin 4 → ℝ, ENNReal.ofReal (coneIntegrand K ![k, k, i, j] s) =
      ENNReal.ofReal |D3 K| * G ((s 2, s 3), (s 0, s 1)) := by
    intro s
    rw [coneIntegrand_canon hG t hdet, ENNReal.ofReal_mul (abs_nonneg _)]
  unfold coneTerm
  simp_rw [hcoe]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  change ∫⁻ s, G ((s 2, s 3), (s 0, s 1)) ∂(Measure.pi fun r => sideMeasure K (![k, k, i, j] r)) = _
  rw [(mp_quad k i j).lintegral_comp hGm, lintegral_prod _ hGm.aemeasurable]
  -- the inner integral over the two points on side `k`
  have hin : ∀ p : ℝ × ℝ, ∫⁻ q, G (p, q) ∂((sideMeasure K k).prod (sideMeasure K k)) =
      ENNReal.ofReal (sideL K k *
        max 0 ((xpos K k i j p.1 p.2 - K.a k) * (K.b k - xpos K k i j p.1 p.2))) := by
    intro p
    rw [lintegral_prod (fun q => G (p, q))
      (hGm.comp (measurable_const.prodMk measurable_id)).aemeasurable]
    exact inner_pair (K.hab k) (xpos K k i j p.1 p.2)
  simp_rw [hin]
  have hcont : Continuous fun p : ℝ × ℝ => sideL K k *
      max 0 ((xpos K k i j p.1 p.2 - K.a k) * (K.b k - xpos K k i j p.1 p.2)) := by
    have := continuous_xpos (K := K) k i j
    fun_prop
  rw [lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal (sideL K k *
      max 0 ((xpos K k i j p.1 p.2 - K.a k) * (K.b k - xpos K k i j p.1 p.2))))
    (ENNReal.measurable_ofReal.comp hcont.measurable).aemeasurable]
  have hmid : ∀ si, ∫⁻ sj, ENNReal.ofReal (sideL K k *
      max 0 ((xpos K k i j (si, sj).1 (si, sj).2 - K.a k) * (K.b k - xpos K k i j (si, sj).1 (si, sj).2)))
      ∂(sideMeasure K j) = ENNReal.ofReal (∫ sj in K.a j..K.b j, sideL K k *
        max 0 ((xpos K k i j si sj - K.a k) * (K.b k - xpos K k i j si sj))) := by
    intro si
    exact lintegral_Icc_ofReal (hcont.comp (continuous_const.prodMk continuous_id))
      (K.hab j).le (fun _ _ => mul_nonneg (sideL_pos k).le (le_max_left _ _))
  simp_rw [hmid]
  have hcont2 : Continuous fun si => ∫ sj in K.a j..K.b j, sideL K k *
      max 0 ((xpos K k i j si sj - K.a k) * (K.b k - xpos K k i j si sj)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun si sj => sideL K k *
        max 0 ((xpos K k i j si sj - K.a k) * (K.b k - xpos K k i j si sj))) hcont _ _
  rw [sideMeasure, lintegral_Icc_ofReal hcont2 (K.hab i).le
    (fun _ _ => intervalIntegral.integral_nonneg (K.hab j).le
      (fun _ _ => mul_nonneg (sideL_pos k).le (le_max_left _ _)))]
  congr 1
  simp_rw [intervalIntegral.integral_const_mul]

/-! ### Summing over tuples -/

lemma sum_coneTerm (hG : GoodSides K) :
    ∑ κ, coneTerm K κ = ∑ k : Fin 3, 12 * coneTerm K (canon k) := by
  have hκ : ∀ κ, coneTerm K κ = ∑ k, if sideCount κ = sideCount (canon k)
      then coneTerm K (canon k) else 0 := by
    intro κ
    rcases tuple_class κ with ⟨⟨j, hj⟩, hne⟩ | ⟨k, hk, huniq⟩
    · rw [coneTerm_missing hG hj]
      exact (Finset.sum_eq_zero fun k _ => if_neg (hne k)).symm
    · rw [Finset.sum_eq_single k (fun k' _ hk' => if_neg (fun h => hk' (huniq k' h)))
        (by simp), if_pos hk]
      exact coneTerm_of_card (fun j => congrFun hk j)
  rw [Finset.sum_congr rfl (fun κ _ => hκ κ), Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, card_class, nsmul_eq_mul]
  norm_num

variable (K) in
/-- `Jₖ = ∫∫ ((x - aₖ)(bₖ - x))₊ dsᵢ dsⱼ`. -/
noncomputable def Jint (k i j : Fin 3) : ℝ :=
  ∫ si in K.a i..K.b i, ∫ sj in K.a j..K.b j,
    max 0 ((xpos K k i j si sj - K.a k) * (K.b k - xpos K k i j si sj))

lemma Jint_nonneg (k i j : Fin 3) : 0 ≤ Jint K k i j :=
  intervalIntegral.integral_nonneg (K.hab i).le fun _ _ =>
    intervalIntegral.integral_nonneg (K.hab j).le fun _ _ => le_max_left _ _

lemma coneTerm_canon' (hG : GoodSides K) (k : Fin 3) :
    coneTerm K (canon k) = ENNReal.ofReal (|D3 K| * (sideL K k *
      Jint K k (![1, 0, 0] k) (![2, 2, 1] k))) := by
  rw [ENNReal.ofReal_mul (abs_nonneg _)]
  fin_cases k
  · exact coneTerm_canon hG triple0 fun s => by
      rw [det_canon0, abs_mul, abs_sub_comm]
  · exact coneTerm_canon hG triple1 fun s => by rw [det_canon1, abs_mul]
  · exact coneTerm_canon hG triple2 fun s => by rw [det_canon2, abs_mul, abs_sub_comm]

/-- **`Iₖ = (Lₖ/2) Jₖ`** in the closed form of Section 6. -/
lemma Jint_eq {k i j : Fin 3} (t : Triple k i j) :
    sideL K k / 2 * Jint K k i j = sideL K i * sideL K j * sideL K k * sideL K k ^ 2 *
      gfun (sideL K i ^ 2 / sideL K k ^ 2) (sideL K j ^ 2 / sideL K k ^ 2) / 8 := by
  have hsum : sideL K i * ((K.a i + K.b i) / 2) + sideL K j * ((K.a j + K.b j) / 2) +
      sideL K k * ((K.a k + K.b k) / 2) = 0 := by
    have h := K.sum_sq
    rw [t.sum3] at h
    unfold sideL; linear_combination h / 2
  have h := Ik_eq (sideL_pos (K := K) i) (sideL_pos j) (sideL_pos k) hsum
  have e : ∀ q, (K.a q + K.b q) / 2 - sideL K q / 2 = K.a q := fun q => by unfold sideL; ring
  have e' : ∀ q, (K.a q + K.b q) / 2 + sideL K q / 2 = K.b q := fun q => by unfold sideL; ring
  rw [e i, e j, e k, e' i, e' j, e' k] at h
  exact h

/-- **The cone density of a triangle**: `|D₃| (I₁ + I₂ + I₃)`. -/
theorem cone_triangle (hG : GoodSides K) :
    let L₁ := sideL K 0
    let L₂ := sideL K 1
    let L₃ := sideL K 2
    coneVertexDensity K = ENNReal.ofReal (|D3 K| *
      (L₂ * L₃ * L₁ * L₁ ^ 2 * gfun (L₂ ^ 2 / L₁ ^ 2) (L₃ ^ 2 / L₁ ^ 2) / 8 +
        L₁ * L₃ * L₂ * L₂ ^ 2 * gfun (L₁ ^ 2 / L₂ ^ 2) (L₃ ^ 2 / L₂ ^ 2) / 8 +
        L₁ * L₂ * L₃ * L₃ ^ 2 * gfun (L₁ ^ 2 / L₃ ^ 2) (L₂ ^ 2 / L₃ ^ 2) / 8)) := by
  intro L₁ L₂ L₃
  rw [coneVertexDensity_eq, sum_coneTerm hG]
  simp_rw [coneTerm_canon' hG]
  have hnn : ∀ k : Fin 3, 0 ≤ |D3 K| * (sideL K k * Jint K k (![1, 0, 0] k) (![2, 2, 1] k)) :=
    fun k => mul_nonneg (abs_nonneg _) (mul_nonneg (sideL_pos k).le (Jint_nonneg _ _ _))
  have h12 : (12 : ℝ≥0∞) = ENNReal.ofReal 12 := by simp
  have h24 : (1 / 24 : ℝ≥0∞) = ENNReal.ofReal (1 / 24) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  simp_rw [h12, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (by norm_num) (hnn k)), h24,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  have j0 := Jint_eq (K := K) triple0
  have j1 := Jint_eq (K := K) triple1
  have j2 := Jint_eq (K := K) triple2
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [L₁, L₂, L₃]
  linear_combination (|D3 K|) * (j0 + j1 + j2)

/-! ### Corollary 2 in the Poisson model -/

/-- **A triangle in the Poisson model.** For side data of a triangle satisfying `GoodSides`, the
probability that an optimal copy fits below the cutoff `n` tends to the triangle formula of
Corollary 2, `p(L₁², L₂², L₃²)`. -/
theorem triangle_optFit_limit (hG : GoodSides K) :
    Filter.Tendsto (fun n : ℕ => PoissonPP.law (Λ K n) {ω | OptFit K n ω}) Filter.atTop
      (nhds (ENNReal.ofReal (ptri (sideL K 0 ^ 2) (sideL K 1 ^ 2) (sideL K 2 ^ 2)))) := by
  have h := general_optFit_limit hG
  rw [parPairs_tri hG, Finset.sum_empty, add_zero, ← fit_integral_eq_spatial,
    fit_integral_triangle hG, cone_triangle hG] at h
  convert h using 2
  have h0 := sideL_pos (K := K) 0
  have h1 := sideL_pos (K := K) 1
  have h2 := sideL_pos (K := K) 2
  have hQ := Qtri_pos (K := K)
  have hD : 0 < |D3 K| := abs_pos.mpr (D3_ne hG)
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hD.le),
    ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hD.le) (by positivity))]
  congr 1
  have hp := p_from_Ik h0 h1 h2
  simp only at hp
  rw [← hp]
  have hQe : Qtri K = (sideL K 0 ^ 2 + sideL K 1 ^ 2 + sideL K 2 ^ 2) / 2 := by
    unfold Qtri; rw [Fin.sum_univ_three]
  rw [hQe]
  field_simp

/-! ### The equilateral triangle of area one -/

/-- Side length of the equilateral triangle of area one: `L² = 4/√3`. -/
noncomputable def eqL : ℝ := Real.sqrt (4 / Real.sqrt 3)

lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
lemma eqL_pos : 0 < eqL := Real.sqrt_pos.mpr (div_pos (by norm_num) sqrt3_pos)
lemma eqL_sq : eqL ^ 2 = 4 / Real.sqrt 3 := Real.sq_sqrt (div_pos (by norm_num) sqrt3_pos).le

/-- The equilateral triangle of area one: outer normals `(0,-1)`, `(√3/2, 1/2)`, `(-√3/2, 1/2)`,
inradius `L/(2√3)`, each side `[-L/2, L/2]`. -/
noncomputable def eqTri : Sides 3 where
  h _ := eqL / (2 * Real.sqrt 3)
  u := ![(0, -1), (Real.sqrt 3 / 2, 1 / 2), (-(Real.sqrt 3 / 2), 1 / 2)]
  a _ := -(eqL / 2)
  b _ := eqL / 2
  hab _ := by have := eqL_pos; linarith
  sum_u1 := by simp [Fin.sum_univ_three]
  sum_u2 := by simp [Fin.sum_univ_three]; ring
  sum_h := by
    simp only [Fin.sum_univ_three]
    have h3 := sqrt3_pos
    have hL := eqL_sq
    field_simp
    rw [hL]
    field_simp
    nlinarith [sqrt3_sq]
  sum_sq := by simp

lemma eqTri_good : GoodSides eqTri where
  unit i := by
    fin_cases i <;> simp [eqTri] <;> nlinarith [sqrt3_sq]
  inj := by
    intro i j h
    have h3 := sqrt3_pos
    fin_cases i <;> fin_cases j <;> simp [eqTri] at h ⊢ <;> linarith
  width i j _ := by
    have := eqL_pos; have := sqrt3_pos
    simp only [eqTri]; positivity
  nondeg k := by
    fin_cases k
    · exact ⟨1, by simp [eqTri, cross]⟩
    · exact ⟨0, by simp [eqTri, cross]⟩
    · exact ⟨0, by simp [eqTri, cross]⟩

lemma ptri_equal {c : ℝ} (hc : 0 < c) : ptri c c c = 13 / 48 := by
  simp only [ptri, div_self hc.ne', g_one_one]
  field_simp
  ring

/-- **The equilateral triangle in the Poisson model: `P(E_n) → 13/48`.** -/
theorem equilateral_optFit_limit :
    Filter.Tendsto (fun n : ℕ => PoissonPP.law (Λ eqTri n) {ω | OptFit eqTri n ω}) Filter.atTop
      (nhds (ENNReal.ofReal (13 / 48))) := by
  have h := triangle_optFit_limit eqTri_good
  have hL : ∀ i, sideL eqTri i = eqL := fun i => by simp [sideL, eqTri]
  rwa [hL, hL, hL, ptri_equal (by have := eqL_pos; positivity)] at h

end Enclosing
