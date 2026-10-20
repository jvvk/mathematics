import LeanProofs.SpectreCover.Cover

/-!
# The count is constant almost everywhere (MO 516016)

`hmove` is `vmove` for horizontal lines, obtained by exchanging the coordinates: the exchange
reverses orientation, so the swapped family lists each triangle's vertices as `A, C, B`.
`cnt_const_on_good` joins any two generic points by a vertical, a horizontal and a vertical
move. The non-generic points (on a vertical or horizontal line through a vertex, or on an edge)
form a null set, so the count is almost everywhere equal to a constant (`cnt_ae_const`).
-/

namespace SpectreCover

open Classical MeasureTheory

theorem orient_swap_coords (p q r : ℝ × ℝ) : orient p.swap q.swap r.swap = -orient p q r := by
  unfold orient; simp only [Prod.fst_swap, Prod.snd_swap]; ring

theorem lat_swap (v w : ℝ × ℝ) (m : ℤ × ℤ) : lat v.swap w.swap m = (lat v w m).swap := by
  ext <;> simp [lat]

theorem mem_segment_swap {a b z : ℝ × ℝ} :
    z.swap ∈ segment ℝ a.swap b.swap ↔ z ∈ segment ℝ a b := by
  constructor <;> rintro ⟨s, t, hs, ht, hst, h⟩ <;> refine ⟨s, t, hs, ht, hst, ?_⟩
  · ext
    · have := congrArg Prod.snd h; simpa using this
    · have := congrArg Prod.fst h; simpa using this
  · ext
    · have := congrArg Prod.snd h; simpa using this
    · have := congrArg Prod.fst h; simpa using this

theorem orient_of_mem_segment {P Q z : ℝ × ℝ} (h : z ∈ segment ℝ P Q) : orient P Q z = 0 := by
  obtain ⟨s, t, -, -, hst, rfl⟩ := h
  unfold orient
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [show s = 1 - t by linarith]; ring

theorem fst_of_mem_segment_vertical {P Q z : ℝ × ℝ} (hv : P.1 = Q.1) (h : z ∈ segment ℝ P Q) :
    z.1 = P.1 := by
  obtain ⟨s, t, -, -, hst, rfl⟩ := h
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, ← hv]
  rw [show s = 1 - t by linarith]; ring

/-- A column off the endpoints' `x`-coordinates meets a segment in at most one point. -/
theorem segment_slice_subsingleton {P Q : ℝ × ℝ} {x : ℝ} (hP : P.1 ≠ x) :
    {y : ℝ | ((x, y) : ℝ × ℝ) ∈ segment ℝ P Q}.Subsingleton := by
  intro y₁ h₁ y₂ h₂
  by_cases hv : P.1 = Q.1
  · exact absurd (fst_of_mem_segment_vertical hv h₁).symm hP
  · have o₁ := orient_of_mem_segment h₁
    have o₂ := orient_of_mem_segment h₂
    unfold orient at o₁ o₂
    have : (Q.1 - P.1) * (y₁ - y₂) = 0 := by linear_combination o₁ - o₂
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linarith : P.1 = Q.1) hv
    · linarith

/-- Segments are null. -/
theorem volume_segment (P Q : ℝ × ℝ) : volume (segment ℝ P Q) = 0 := by
  by_cases hv : P.1 = Q.1
  · refine measure_mono_null (t := {P.1} ×ˢ Set.univ) (fun z hz => ?_) ?_
    · exact ⟨fst_of_mem_segment_vertical hv hz, trivial⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  · set L := {z : ℝ × ℝ | orient P Q z = 0}
    refine measure_mono_null (t := L) (fun z hz => orient_of_mem_segment hz) ?_
    have hL : MeasurableSet L := by
      refine measurableSet_eq_fun ?_ measurable_const
      unfold orient; fun_prop
    rw [Measure.volume_eq_prod, Measure.prod_apply hL]
    refine (lintegral_congr fun x => ?_).trans lintegral_zero
    refine Set.Subsingleton.measure_zero ?_ _
    intro y₁ h₁ y₂ h₂
    simp only [Set.mem_preimage, L, Set.mem_setOf_eq, orient] at h₁ h₂
    have : (Q.1 - P.1) * (y₁ - y₂) = 0 := by linear_combination h₁ - h₂
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linarith : P.1 = Q.1) hv
    · linarith

section Family

variable {ι : Type*} [Fintype ι] {V : ι → Fin 3 → ℝ × ℝ} {v w : ℝ × ℝ}

/-- The family with the coordinates exchanged; each triangle is relisted as `A, C, B`. -/
def swapFam (V : ι → Fin 3 → ℝ × ℝ) : ι → Fin 3 → ℝ × ℝ :=
  fun i => ![(V i 0).swap, (V i 2).swap, (V i 1).swap]

theorem orient_swap_add (a b l z : ℝ × ℝ) :
    orient (a.swap + l.swap) (b.swap + l.swap) z.swap = orient (b + l) (a + l) z := by
  unfold orient; simp only [Prod.fst_add, Prod.snd_add, Prod.fst_swap, Prod.snd_swap]; ring

theorem mem_tri_swap (i : ι) (m : ℤ × ℤ) (z : ℝ × ℝ) :
    z.swap ∈ tri (swapFam V) v.swap w.swap i m ↔ z ∈ tri V v w i m := by
  have e0 : swapFam V i 0 = (V i 0).swap := rfl
  have e1 : swapFam V i 1 = (V i 2).swap := rfl
  have e2 : swapFam V i 2 = (V i 1).swap := rfl
  simp only [tri, closedTri, Set.mem_setOf_eq, lat_swap, e0, e1, e2, orient_swap_add]
  tauto

theorem cnt_swap (z : ℝ × ℝ) : cnt (swapFam V) v.swap w.swap z.swap = cnt V v w z := by
  unfold cnt
  simp only [mem_tri_swap]

theorem swap_orient (hD : ∀ i, 0 < orient (V i 0) (V i 1) (V i 2)) (i : ι) :
    0 < orient (swapFam V i 0) (swapFam V i 1) (swapFam V i 2) := by
  rw [show swapFam V i 0 = (V i 0).swap from rfl, show swapFam V i 1 = (V i 2).swap from rfl,
    show swapFam V i 2 = (V i 1).swap from rfl, orient_swap_coords]
  have : orient (V i 0) (V i 2) (V i 1) = -orient (V i 0) (V i 1) (V i 2) := by unfold orient; ring
  linarith [hD i]

theorem swap_paired (hpair : Paired V v w) : Paired (swapFam V) v.swap w.swap := by
  intro H hH
  have := hpair (fun P Q => H Q.swap P.swap) (fun P Q m => by
    simp only [Prod.swap_add, ← lat_swap]; exact hH _ _ _)
  have e0 : ∀ i, swapFam V i 0 = (V i 0).swap := fun _ => rfl
  have e1 : ∀ i, swapFam V i 1 = (V i 2).swap := fun _ => rfl
  have e2 : ∀ i, swapFam V i 2 = (V i 1).swap := fun _ => rfl
  simp only [Fin.sum_univ_three, show ((1 : Fin 3) + 1) = 2 from rfl,
    show ((2 : Fin 3) + 1) = 0 from rfl, zero_add] at this ⊢
  simp only [e0, e1, e2]
  calc _ = ∑ x, (H (V x 1).swap (V x 0).swap + H (V x 2).swap (V x 1).swap +
        H (V x 0).swap (V x 2).swap) := Finset.sum_congr rfl fun x _ => by ring
    _ = _ := this
    _ = _ := Finset.sum_congr rfl fun x _ => by ring

/-- **Horizontal move.** -/
theorem hmove (hD : ∀ i, 0 < orient (V i 0) (V i 1) (V i 2))
    (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) (hpair : Paired V v w) {x₁ x₂ y : ℝ}
    (hy : ∀ i k m, (V i k + lat v w m).2 ≠ y)
    (h₁ : ∀ i k m, ((x₁, y) : ℝ × ℝ) ∉ segment ℝ (V i k + lat v w m) (V i (k + 1) + lat v w m))
    (h₂ : ∀ i k m, ((x₂, y) : ℝ × ℝ) ∉ segment ℝ (V i k + lat v w m) (V i (k + 1) + lat v w m)) :
    cnt V v w (x₁, y) = cnt V v w (x₂, y) := by
  rw [← cnt_swap (x₁, y), ← cnt_swap (x₂, y)]
  have hdet' : v.swap.1 * w.swap.2 - v.swap.2 * w.swap.1 ≠ 0 := by
    simp only [Prod.fst_swap, Prod.snd_swap]; intro h; apply hdet; linarith
  have vx : ∀ i k m, (swapFam V i k + lat v.swap w.swap m).1 ≠ y := by
    intro i k m
    rw [lat_swap]
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    · exact fun h => hy i 0 m (by simpa [swapFam] using h)
    · exact fun h => hy i 2 m (by simpa [swapFam] using h)
    · exact fun h => hy i 1 m (by simpa [swapFam] using h)
  have seg : ∀ x, (∀ i k m, ((x, y) : ℝ × ℝ) ∉
      segment ℝ (V i k + lat v w m) (V i (k + 1) + lat v w m)) → ∀ i k m,
      ((x, y) : ℝ × ℝ).swap ∉ segment ℝ (swapFam V i k + lat v.swap w.swap m)
        (swapFam V i (k + 1) + lat v.swap w.swap m) := by
    intro x hx i k m hm
    rw [lat_swap, show ((x, y) : ℝ × ℝ).swap = (y, x) from rfl] at hm
    have e0 : swapFam V i 0 = (V i 0).swap := rfl
    have e1 : swapFam V i 1 = (V i 2).swap := rfl
    have e2 : swapFam V i 2 = (V i 1).swap := rfl
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    · rw [show ((0 : Fin 3) + 1) = 1 from rfl, e0, e1, ← Prod.swap_add, ← Prod.swap_add,
        show ((y, x) : ℝ × ℝ) = ((x, y) : ℝ × ℝ).swap from rfl, mem_segment_swap,
        segment_symm] at hm
      exact hx i 2 m hm
    · rw [show ((1 : Fin 3) + 1) = 2 from rfl, e1, e2, ← Prod.swap_add, ← Prod.swap_add,
        show ((y, x) : ℝ × ℝ) = ((x, y) : ℝ × ℝ).swap from rfl, mem_segment_swap,
        segment_symm] at hm
      exact hx i 1 m hm
    · rw [show ((2 : Fin 3) + 1) = 0 from rfl, e2, e0, ← Prod.swap_add, ← Prod.swap_add,
        show ((y, x) : ℝ × ℝ) = ((x, y) : ℝ × ℝ).swap from rfl, mem_segment_swap,
        segment_symm] at hm
      exact hx i 0 m hm
  exact vmove (swap_orient hD) hdet' (swap_paired hpair) vx (seg x₁ h₁) (seg x₂ h₂)

/-- The generic points: off every vertical and horizontal line through a vertex, off every edge. -/
def Good (V : ι → Fin 3 → ℝ × ℝ) (v w : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {z | (∀ i k m, (V i k + lat v w m).1 ≠ z.1) ∧ (∀ i k m, (V i k + lat v w m).2 ≠ z.2) ∧
    ∀ i k m, z ∉ segment ℝ (V i k + lat v w m) (V i (k + 1) + lat v w m)}

theorem cnt_const_on_good (hD : ∀ i, 0 < orient (V i 0) (V i 1) (V i 2))
    (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) (hpair : Paired V v w) {z z' : ℝ × ℝ}
    (hz : z ∈ Good V v w) (hz' : z' ∈ Good V v w) : cnt V v w z = cnt V v w z' := by
  obtain ⟨hz1, hz2, hz3⟩ := hz
  obtain ⟨hz'1, hz'2, hz'3⟩ := hz'
  have a1 : ∀ᵐ y ∂(volume : Measure ℝ), ∀ p : ι × Fin 3 × (ℤ × ℤ),
      (V p.1 p.2.1 + lat v w p.2.2).2 ≠ y := by
    rw [ae_all_iff]; intro p; exact Measure.ae_ne volume _ |>.mono fun y h => Ne.symm h
  have a2 : ∀ x, (∀ i k m, (V i k + lat v w m).1 ≠ x) → ∀ᵐ y ∂(volume : Measure ℝ),
      ∀ p : ι × Fin 3 × (ℤ × ℤ), ((x, y) : ℝ × ℝ) ∉
        segment ℝ (V p.1 p.2.1 + lat v w p.2.2) (V p.1 (p.2.1 + 1) + lat v w p.2.2) := by
    intro x hx
    rw [ae_all_iff]; intro p
    exact (segment_slice_subsingleton (hx p.1 p.2.1 p.2.2)).countable.ae_notMem volume
  obtain ⟨y, hy1, hy2, hy3⟩ := (a1.and ((a2 z.1 hz1).and (a2 z'.1 hz'1))).exists
  have e1 : cnt V v w (z.1, z.2) = cnt V v w (z.1, y) :=
    vmove hD hdet hpair hz1 hz3 (fun i k m => hy2 (i, k, m))
  have e2 : cnt V v w (z.1, y) = cnt V v w (z'.1, y) :=
    hmove hD hdet hpair (fun i k m h => hy1 (i, k, m) h) (fun i k m => hy2 (i, k, m))
      (fun i k m => hy3 (i, k, m))
  have e3 : cnt V v w (z'.1, y) = cnt V v w (z'.1, z'.2) :=
    vmove hD hdet hpair hz'1 (fun i k m => hy3 (i, k, m)) hz'3
  exact e1.trans (e2.trans e3)

theorem good_ae [Countable ι] : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), z ∈ Good V v w := by
  have h1 : ∀ i k m, ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), (V i k + lat v w m).1 ≠ z.1 := by
    intro i k m
    rw [ae_iff]
    refine measure_mono_null (t := {(V i k + lat v w m).1} ×ˢ Set.univ) (fun z hz => ?_) ?_
    · simp only [Set.mem_setOf_eq, not_not] at hz; exact ⟨hz.symm, trivial⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  have h2 : ∀ i k m, ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), (V i k + lat v w m).2 ≠ z.2 := by
    intro i k m
    rw [ae_iff]
    refine measure_mono_null (t := Set.univ ×ˢ {(V i k + lat v w m).2}) (fun z hz => ?_) ?_
    · simp only [Set.mem_setOf_eq, not_not] at hz; exact ⟨trivial, hz.symm⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  have h3 : ∀ i k m, ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      z ∉ segment ℝ (V i k + lat v w m) (V i (k + 1) + lat v w m) := fun i k m =>
    measure_eq_zero_iff_ae_notMem.mp (volume_segment _ _)
  simp only [Good, Set.mem_setOf_eq, Filter.eventually_and, ae_all_iff]
  exact ⟨h1, h2, h3⟩

/-- **The count is almost everywhere constant.** -/
theorem cnt_ae_const [Countable ι] (hD : ∀ i, 0 < orient (V i 0) (V i 1) (V i 2))
    (hdet : v.1 * w.2 - v.2 * w.1 ≠ 0) (hpair : Paired V v w) :
    ∃ c : ℤ, ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), cnt V v w z = c := by
  obtain ⟨z₀, hz₀⟩ := (good_ae (V := V) (v := v) (w := w)).exists
  exact ⟨cnt V v w z₀, good_ae.mono fun z hz => cnt_const_on_good hD hdet hpair hz hz₀⟩

end Family

end SpectreCover
