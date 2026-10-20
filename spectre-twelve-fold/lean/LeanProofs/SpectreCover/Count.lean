import LeanProofs.SpectreCover.Ae

/-!
# The value of the constant (MO 516016)

If the count is almost everywhere `c`, integrating it over a fundamental parallelogram of the
lattice gives `c · |det(v, w)| = Σᵢ area(triangle i)` (`count_mul_det`). Ingredients:
`volume_closedTri` (a counterclockwise triangle has area `orient/2`), `volume_fd` (the
parallelogram has area `|det(v, w)|`) and Mathlib's fundamental-domain unfolding.
-/

namespace SpectreCover

open MeasureTheory Classical
open scoped Pointwise

/-! ### Area of a triangle -/

/-- The standard simplex. -/
def simplex0 : Set (ℝ × ℝ) := {u | 0 ≤ u.1 ∧ 0 ≤ u.2 ∧ u.1 + u.2 ≤ 1}

theorem volume_simplex0 : volume simplex0 = ENNReal.ofReal (1 / 2) := by
  set R := regionBetween (fun _ => (0 : ℝ)) (fun x => 1 - x) (Set.Icc 0 1)
  have hR : volume R = ENNReal.ofReal (1 / 2) := by
    rw [Measure.volume_eq_prod, volume_regionBetween_eq_lintegral' measurable_const
      (by fun_prop) measurableSet_Icc]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
      simp only [Pi.sub_apply, sub_zero]
      rw [intervalIntegral.integral_sub (by simp) (by simp)]
      simp; norm_num
    · exact (Continuous.integrableOn_Icc (by fun_prop))
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]; linarith [hx.2]
  have sub1 : R ⊆ simplex0 := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [Set.mem_Ioo] at hy
    exact ⟨hx.1, hy.1.le, by linarith [hy.2]⟩
  have sub2 : simplex0 ⊆ R ∪ (segment ℝ (0, 0) (1, 0) ∪ segment ℝ (1, 0) (0, 1)) := by
    rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    by_cases h0 : y = 0
    · right; left
      subst h0
      refine ⟨1 - x, x, by linarith, hx, by ring, ?_⟩
      ext <;> simp
    · by_cases h1 : x + y = 1
      · right; right
        refine ⟨x, y, hx, hy, h1, ?_⟩
        ext <;> simp
      · left
        refine ⟨⟨hx, by linarith [lt_of_le_of_ne hy (Ne.symm h0)]⟩, ?_, ?_⟩
        · exact lt_of_le_of_ne hy (Ne.symm h0)
        · show y < 1 - x; exact lt_of_le_of_ne (by linarith) (fun h => h1 (by linarith))
  apply le_antisymm
  · calc volume simplex0 ≤ volume (R ∪ (segment ℝ (0, 0) (1, 0) ∪ segment ℝ (1, 0) (0, 1))) :=
          measure_mono sub2
      _ ≤ volume R + volume (segment ℝ ((0 : ℝ), (0 : ℝ)) (1, 0) ∪ segment ℝ (1, 0) (0, 1)) :=
          measure_union_le _ _
      _ = volume R := by
          rw [measure_union_null (volume_segment _ _) (volume_segment _ _), add_zero]
      _ = _ := hR
  · rw [← hR]; exact measure_mono sub1

/-- **Area of a triangle.** -/
theorem volume_closedTri {A B C : ℝ × ℝ} (hD : 0 < orient A B C) :
    volume (closedTri A B C) = ENNReal.ofReal (orient A B C / 2) := by
  set M := Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![B.1 - A.1, C.1 - A.1; B.2 - A.2, C.2 - A.2]
  have hM : ∀ u : ℝ × ℝ, M u = ((B.1 - A.1) * u.1 + (C.1 - A.1) * u.2,
      (B.2 - A.2) * u.1 + (C.2 - A.2) * u.2) := fun u => Matrix.toLin_finTwoProd_apply _ _ _ _ u
  have hdet : LinearMap.det M = orient A B C := by
    rw [LinearMap.det_toLin, Matrix.det_fin_two_of]; unfold orient; ring
  have hD0 : orient A B C ≠ 0 := hD.ne'
  have hset : closedTri A B C = (fun u => A + u) '' (M '' simplex0) := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩
      have k1 := bary_shift A B C z
      have k2 := bary_shift_snd A B C z
      have hs := bary_sum A B C z
      refine ⟨M (orient C A z / orient A B C, orient A B z / orient A B C),
        ⟨_, ⟨div_nonneg h3 hD.le, div_nonneg h1 hD.le, ?_⟩, rfl⟩, ?_⟩
      · rw [← add_div, div_le_one hD]; linarith
      · rw [hM]
        ext
        · simp only [Prod.fst_add]; field_simp; linear_combination -k1
        · simp only [Prod.snd_add]; field_simp; linear_combination -k2
    · rintro ⟨_, ⟨u, ⟨hu1, hu2, hu3⟩, rfl⟩, rfl⟩
      rw [hM]
      refine ⟨?_, ?_, ?_⟩
      · have : orient A B (A + ((B.1 - A.1) * u.1 + (C.1 - A.1) * u.2,
            (B.2 - A.2) * u.1 + (C.2 - A.2) * u.2)) = u.2 * orient A B C := by
          unfold orient; simp only [Prod.fst_add, Prod.snd_add]; ring
        rw [this]; positivity
      · have : orient B C (A + ((B.1 - A.1) * u.1 + (C.1 - A.1) * u.2,
            (B.2 - A.2) * u.1 + (C.2 - A.2) * u.2)) = (1 - u.1 - u.2) * orient A B C := by
          unfold orient; simp only [Prod.fst_add, Prod.snd_add]; ring
        rw [this]; exact mul_nonneg (by linarith) hD.le
      · have : orient C A (A + ((B.1 - A.1) * u.1 + (C.1 - A.1) * u.2,
            (B.2 - A.2) * u.1 + (C.2 - A.2) * u.2)) = u.1 * orient A B C := by
          unfold orient; simp only [Prod.fst_add, Prod.snd_add]; ring
        rw [this]; positivity
  rw [hset, Set.image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap, hdet,
    volume_simplex0, ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos hD]
  ring_nf

theorem isClosed_closedTri (A B C : ℝ × ℝ) : IsClosed (closedTri A B C) := by
  have hc : ∀ P Q : ℝ × ℝ, Continuous fun z => orient P Q z := fun P Q => by
    unfold orient; fun_prop
  have e : closedTri A B C = {z | (0 : ℝ) ≤ orient A B z} ∩ {z | (0 : ℝ) ≤ orient B C z} ∩
      {z | (0 : ℝ) ≤ orient C A z} := by
    ext; simp [closedTri, and_assoc]
  rw [e]
  exact ((isClosed_le continuous_const (hc A B)).inter
    (isClosed_le continuous_const (hc B C))).inter (isClosed_le continuous_const (hc C A))

theorem image_add_closedTri (t A B C : ℝ × ℝ) :
    (fun z => t + z) '' closedTri A B C = closedTri (A + t) (B + t) (C + t) := by
  ext z
  simp only [Set.mem_image, closedTri, Set.mem_setOf_eq]
  have e : ∀ P Q : ℝ × ℝ, orient (P + t) (Q + t) z = orient P Q (z - t) := fun P Q => by
    unfold orient; simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring
  rw [e, e, e]
  constructor
  · rintro ⟨u, hu, rfl⟩; simpa using hu
  · intro h; exact ⟨z - t, h, by abel⟩

/-! ### The fundamental parallelogram -/

theorem fd_finTwoProd : ZSpan.fundamentalDomain (Module.Basis.finTwoProd ℝ) =
    Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1 := by
  ext x
  simp [ZSpan.fundamentalDomain, Module.Basis.coe_finTwoProd_repr, Fin.forall_fin_two]

theorem volume_fd_finTwoProd :
    volume (ZSpan.fundamentalDomain (Module.Basis.finTwoProd ℝ)) = 1 := by
  rw [fd_finTwoProd, Measure.volume_eq_prod, Measure.prod_prod]; simp

section Family

variable {v w : ℝ × ℝ}

theorem li_pair (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) : LinearIndependent ℝ ![v, w] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.fst_zero, Prod.snd_zero] at h1 h2
  have es : s * (v.1 * w.2 - v.2 * w.1) = 0 := by linear_combination w.2 * h1 - w.1 * h2
  have et : t * (v.1 * w.2 - v.2 * w.1) = 0 := by linear_combination v.1 * h2 - v.2 * h1
  exact ⟨(mul_eq_zero.mp es).resolve_right hdet, (mul_eq_zero.mp et).resolve_right hdet⟩

/-- The basis `v, w` of the plane. -/
noncomputable def basisVW (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) : Module.Basis (Fin 2) ℝ (ℝ × ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank (li_pair hdet) (by simp)

theorem basisVW_apply (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) : ⇑(basisVW hdet) = ![v, w] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

theorem volume_fd (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) :
    volume (ZSpan.fundamentalDomain (basisVW hdet)) = ENNReal.ofReal |v.1 * w.2 - v.2 * w.1| := by
  rw [ZSpan.measure_fundamentalDomain _ _ (Module.Basis.finTwoProd ℝ), volume_fd_finTwoProd,
    mul_one, Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, Module.Basis.coe_finTwoProd_repr, basisVW_apply]
  ring_nf

/-- The lattice points, as elements of Mathlib's `ℤ`-span. -/
noncomputable def latEquiv (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) :
    ℤ × ℤ ≃ (Submodule.span ℤ (Set.range (basisVW hdet))).toAddSubgroup := by
  refine Equiv.ofBijective (fun m => ⟨lat v w m, ?_⟩) ⟨?_, ?_⟩
  · show lat v w m ∈ Submodule.span ℤ (Set.range (basisVW hdet))
    rw [basisVW_apply]
    unfold lat
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ m.1 (Submodule.subset_span (⟨0, rfl⟩ : v ∈ Set.range ![v, w])))
      (Submodule.smul_mem _ m.2 (Submodule.subset_span (⟨1, rfl⟩ : w ∈ Set.range ![v, w])))
  · intro m m' h
    have h' : lat v w m = lat v w m' := congrArg Subtype.val h
    have := (li_pair hdet).eq_of_pair (s := (m.1 : ℝ)) (t := m.2) (s' := m'.1) (t' := m'.2) h'
    exact Prod.ext (by exact_mod_cast this.1) (by exact_mod_cast this.2)
  · rintro ⟨x, hx⟩
    have hx' : x ∈ Submodule.span ℤ (Set.range (basisVW hdet)) := hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx'
    refine ⟨(c 0, c 1), Subtype.ext ?_⟩
    simp only [lat, ← hc, Fin.sum_univ_two, basisVW_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Int.cast_smul_eq_zsmul]

theorem latEquiv_apply (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) (m : ℤ × ℤ) :
    ((latEquiv hdet m : (Submodule.span ℤ (Set.range (basisVW hdet))).toAddSubgroup) :
      ℝ × ℝ) = lat v w m := rfl

variable {ι : Type*} [Fintype ι] {V : ι → Fin 3 → ℝ × ℝ}

/-- Unfolding over the fundamental parallelogram: the translates of one triangle cut it into
pieces of total area the area of the triangle. -/
theorem tsum_tri (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) (i : ι) :
    ∑' m : ℤ × ℤ, volume (tri V v w i m ∩ ZSpan.fundamentalDomain (basisVW hdet)) =
      volume (tri V v w i 0) := by
  have hF := ZSpan.isAddFundamentalDomain' (basisVW hdet) volume
  have : Countable (Submodule.span ℤ (Set.range (basisVW hdet))).toAddSubgroup :=
    Countable.of_equiv _ (latEquiv hdet)
  rw [hF.measure_eq_tsum, ← (latEquiv hdet).tsum_eq]
  congr 1; ext m
  congr 2
  rw [show ((latEquiv hdet m) +ᵥ tri V v w i 0) = (fun x => lat v w m + x) '' tri V v w i 0
    from rfl, tri, tri, image_add_closedTri]
  simp [lat]

theorem lintegral_count (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) :
    ∫⁻ z in ZSpan.fundamentalDomain (basisVW hdet),
      ∑ i, ∑' m : ℤ × ℤ, (tri V v w i m).indicator 1 z = ∑ i, volume (tri V v w i 0) := by
  have hm : ∀ i m, MeasurableSet (tri V v w i m) := fun i m =>
    (isClosed_closedTri _ _ _).measurableSet
  rw [lintegral_finsetSum' _ (fun i _ => (Measurable.ennreal_tsum fun m =>
    (measurable_one.indicator (hm i m))).aemeasurable)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_tsum (fun m => (measurable_one.indicator (hm i m)).aemeasurable)]
  simp_rw [lintegral_indicator_one (hm _ _), Measure.restrict_apply (hm _ _)]
  exact tsum_tri hdet i

theorem tsum_indicator_tri {i : ι} {z : ℝ × ℝ} (hfin : {m | z ∈ tri V v w i m}.Finite) :
    ∑' m : ℤ × ℤ, (tri V v w i m).indicator 1 z = (hfin.toFinset.card : ENNReal) := by
  rw [tsum_eq_sum (s := hfin.toFinset) (fun m hm => by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hm
    simp [Set.indicator, hm])]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hm
  simp [Set.indicator, hm]

theorem finsum_ite_tri {i : ι} {z : ℝ × ℝ} (hfin : {m | z ∈ tri V v w i m}.Finite) :
    ∑ᶠ m : ℤ × ℤ, (if z ∈ tri V v w i m then (1 : ℤ) else 0) = (hfin.toFinset.card : ℤ) := by
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (fun m hm => by
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      not_not] at hm
    simpa using hm)]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hm
  simp [hm]

/-- **Integrating the constant count over a period cell.** -/
theorem count_mul_det (hD : ∀ i, 0 < orient (V i 0) (V i 1) (V i 2))
    (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) (c : ℕ)
    (hc : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), cnt V v w z = c) :
    (c : ℝ) * |v.1 * w.2 - v.2 * w.1| = ∑ i, orient (V i 0) (V i 1) (V i 2) / 2 := by
  have hfin : ∀ i z, {m | z ∈ tri V v w i m}.Finite := fun i z => by
    have := tri_finite hD hdet i z
    refine this.subset fun m hm => ?_
    simp only [Set.mem_setOf_eq] at hm
    simp [hm]
  have pt : ∀ z, cnt V v w z = c →
      (∑ i, ∑' m : ℤ × ℤ, (tri V v w i m).indicator 1 z : ENNReal) = c := by
    intro z hz
    have e1 : cnt V v w z = ((∑ i, (hfin i z).toFinset.card : ℕ) : ℤ) := by
      unfold cnt; push_cast; exact Finset.sum_congr rfl fun i _ => finsum_ite_tri (hfin i z)
    have e2 : (∑ i, (hfin i z).toFinset.card : ℕ) = c := by
      have := e1.symm.trans hz; exact_mod_cast this
    simp only [fun i => tsum_indicator_tri (hfin i z)]
    rw [← e2]; push_cast; rfl
  have hint := lintegral_count (V := V) hdet
  rw [setLIntegral_congr_fun_ae (ZSpan.fundamentalDomain_measurableSet _)
    (hc.mono fun z hz _ => pt z hz), setLIntegral_const, volume_fd] at hint
  have hvol : ∀ i, volume (tri V v w i 0) =
      ENNReal.ofReal (orient (V i 0) (V i 1) (V i 2) / 2) := by
    intro i
    have h0 : lat v w 0 = 0 := by simp [lat]
    rw [tri, h0, add_zero, add_zero, add_zero]
    exact volume_closedTri (hD i)
  simp only [hvol] at hint
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := hD i; positivity),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at hint
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity)
    (Finset.sum_nonneg fun i _ => by have := hD i; positivity)).mp hint

end Family

end SpectreCover
