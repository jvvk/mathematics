import EnclosingCopy.Enclosing.PolygonSampling

/-!
# Simultaneous containment and separation of trimmed side windows

A trimmed side rectangle has a uniform positive inward gap to any other supporting
line when its depth is sufficiently small. Consequently the finite family of
trimmed side windows is eventually contained in the polygon and pairwise disjoint.
-/
namespace Enclosing
open MeasureTheory Set Filter Topology
variable {m : ℕ} [NeZero m] {v : Fin m → ℝ × ℝ}

/-- A sufficiently shallow trimmed rectangle stays uniformly away from any other side. -/
theorem exists_sideWindow_gap (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (i j : Fin m) (hji : j ≠ i) {a b : ℝ} (ha : aEnd v i < a) (hab : a ≤ b)
    (hb : b < bEnd v i) :
    let K := sidesOf v hm hv harea
    ∃ η > 0, ∃ d₀ > 0, ∀ d ∈ Icc 0 d₀, ∀ x ∈ sideWindow K i a b d,
      η ≤ K.h j - dot x (K.u j) := by
  intro K
  have hA := sideChart_strict_other hm hv i j hji ha (hab.trans_lt hb)
  have hB := sideChart_strict_other hm hv i j hji (ha.trans_le hab) hb
  let η := min (K.h j - dot (sideChart (K.u i) (K.h i) (a, 0)) (K.u j))
    (K.h j - dot (sideChart (K.u i) (K.h i) (b, 0)) (K.u j)) / 2
  have hη : 0 < η := div_pos (lt_min (sub_pos.mpr hA) (sub_pos.mpr hB)) (by norm_num)
  have hAη : dot (sideChart (K.u i) (K.h i) (a, 0)) (K.u j) < K.h j - η := by
    have he := min_le_left (K.h j - dot (sideChart (K.u i) (K.h i) (a, 0)) (K.u j))
      (K.h j - dot (sideChart (K.u i) (K.h i) (b, 0)) (K.u j))
    dsimp [η] at hη ⊢; linarith
  have hBη : dot (sideChart (K.u i) (K.h i) (b, 0)) (K.u j) < K.h j - η := by
    have he := min_le_right (K.h j - dot (sideChart (K.u i) (K.h i) (a, 0)) (K.u j))
      (K.h j - dot (sideChart (K.u i) (K.h i) (b, 0)) (K.u j))
    dsimp [η] at hη ⊢; linarith
  have hca : Continuous (fun d : ℝ => dot (sideChart (K.u i) (K.h i) (a, d)) (K.u j)) := by
    unfold sideChart dot; fun_prop
  have hcb : Continuous (fun d : ℝ => dot (sideChart (K.u i) (K.h i) (b, d)) (K.u j)) := by
    unfold sideChart dot; fun_prop
  have he := ((hca.tendsto 0).eventually (Iio_mem_nhds hAη)).and
    ((hcb.tendsto 0).eventually (Iio_mem_nhds hBη))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨η, hη, r / 2, by positivity, ?_⟩
  intro d hd x hx
  obtain ⟨q, hq, rfl⟩ := hx
  have hsmall : dist q.2 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hq.2.1]
    linarith [hq.2.2, hd.2]
  have hends := hball hsmall
  have hdot := (affine_le_max_endpoints (K.u i) (K.u j) (K.h i) q.2 a b q.1 hq.1).trans
    (max_le hends.1.le hends.2.le)
  linarith

/-- Distinct trimmed side windows are disjoint once their common depth is small enough. -/
theorem sideWindows_disjoint_eventually (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (a b : Fin m → ℝ) (ha : ∀ i, aEnd v i < a i) (hab : ∀ i, a i ≤ b i)
    (hb : ∀ i, b i < bEnd v i) {T : ℝ} (hT : 0 ≤ T) :
    let K := sidesOf v hm hv harea
    ∀ᶠ n : ℕ in atTop, Pairwise (fun i j =>
      Disjoint (sideWindow K i (a i) (b i) (T / n))
        (sideWindow K j (a j) (b j) (T / n))) := by
  intro K
  have hpair (i j : Fin m) : ∀ᶠ n : ℕ in atTop, i ≠ j →
      Disjoint (sideWindow K i (a i) (b i) (T / n))
        (sideWindow K j (a j) (b j) (T / n)) := by
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => (h hij).elim
    obtain ⟨η, hη, d₀, hd₀, hgap⟩ := exists_sideWindow_gap hm hv harea i j (Ne.symm hij)
      (ha i) (hab i) (hb i)
    have hd := (tendsto_const_div_atTop_nhds_zero_nat T).eventually (Iio_mem_nhds hd₀)
    have hηn := (tendsto_const_div_atTop_nhds_zero_nat T).eventually (Iio_mem_nhds hη)
    filter_upwards [hd, hηn] with n hdn hηn _
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hnn : 0 ≤ T / (n : ℝ) := div_nonneg hT (Nat.cast_nonneg n)
    have hxgap := hgap _ ⟨hnn, hdn.le⟩ x hxi
    obtain ⟨q, hq, rfl⟩ := hxj
    have he := congrArg Prod.snd (sideCoords_chart (K.u j)
      ((goodSides_of_convex hm hv harea).unit j) (K.h j) q)
    change K.h j - dot (sideChart (K.u j) (K.h j) q) (K.u j) = q.2 at he
    linarith [hq.2.2]
  have hall : ∀ᶠ n : ℕ in atTop, ∀ i j : Fin m, i ≠ j →
      Disjoint (sideWindow K i (a i) (b i) (T / n))
        (sideWindow K j (a j) (b j) (T / n)) :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => hpair i j
  exact hall

/-- All trimmed side windows are eventually physical polygon windows simultaneously. -/
theorem sideWindows_subset_eventually (hm : 3 ≤ m) (hv : ConvexPos v) (harea : area v = 1)
    (a b : Fin m → ℝ) (ha : ∀ i, aEnd v i < a i) (hab : ∀ i, a i ≤ b i)
    (hb : ∀ i, b i < bEnd v i) {T : ℝ} (hT : 0 ≤ T) :
    let K := sidesOf v hm hv harea
    ∀ᶠ n : ℕ in atTop, ∀ i, sideWindow K i (a i) (b i) (T / n) ⊆ polygonRegion K := by
  intro K
  apply eventually_all.mpr
  intro i
  obtain ⟨d₀, hd₀, hsub⟩ := exists_sideWindow_subset hm hv harea i (ha i) (hab i) (hb i)
  filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat T).eventually (Iio_mem_nhds hd₀)]
    with n hn
  exact hsub _ ⟨div_nonneg hT (Nat.cast_nonneg n), hn.le⟩

end Enclosing
