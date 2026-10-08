import EnclosingCopy.Enclosing.Classification

/-!
# Classification of the optimum for a general polygon

`GoodSides`: unit, pairwise distinct normals, positive width across every pair of parallel sides,
and no side direction is parallel to all the others. Under these hypotheses the KKT support of a
fitting optimum (`optimum_kkt`) is, outside null events,

* four points: a certified vertex candidate;
* two points on a side `k` and one on its parallel side `k̄`, in the KKT order: a segment
  candidate;

and the remaining supports are null events:

* two points on antiparallel sides with `s_a + s_b = 0` (`Opp2`);
* three points on pairwise non-parallel sides with
  `[u_b, u_c] s_a + [u_c, u_a] s_b + [u_a, u_b] s_c = 0` (`Tri3`, `[·,·]` the cross product);
* one point (impossible).
-/

namespace Enclosing
open MeasureTheory Set Matrix ENNReal

/-- The planar cross product. -/
def cross (a b : ℝ × ℝ) : ℝ := a.1 * b.2 - a.2 * b.1

variable {m : ℕ} (K : Sides m)

/-- Hypotheses on the side data of a convex polygon used by the classification. -/
structure GoodSides : Prop where
  unit : ∀ i, (K.u i).1 ^ 2 + (K.u i).2 ^ 2 = 1
  inj : Function.Injective K.u
  width : ∀ i j, K.u j = -K.u i → 0 < K.h i + K.h j
  nondeg : ∀ k, ∃ j, cross (K.u k) (K.u j) ≠ 0

variable {K}

lemma dot_tang_eq_cross (j k : Fin m) : dot (K.u j) (tang K k) = cross (K.u k) (K.u j) := by
  simp only [dot, tang, cross]; ring

/-- Unit vectors with zero cross product are equal or opposite. -/
lemma unit_cross_zero {u v : ℝ × ℝ} (hu : u.1 ^ 2 + u.2 ^ 2 = 1) (hv : v.1 ^ 2 + v.2 ^ 2 = 1)
    (h : cross u v = 0) : v = u ∨ v = -u := by
  simp only [cross] at h
  set d := u.1 * v.1 + u.2 * v.2
  have h1 : v.1 = d * u.1 := by
    simp only [d]; linear_combination (-u.2) * h - v.1 * hu
  have h2 : v.2 = d * u.2 := by
    simp only [d]; linear_combination u.1 * h - v.2 * hu
  have hd : d ^ 2 = 1 := by
    have : v.1 ^ 2 + v.2 ^ 2 = d ^ 2 * (u.1 ^ 2 + u.2 ^ 2) := by rw [h1, h2]; ring
    rw [hu, hv] at this; linarith
  rcases sq_eq_one_iff.mp hd with hd | hd <;> [left; right] <;>
    ext <;> simp [h1, h2, hd]

lemma GoodSides.parallel (hG : GoodSides K) {i j : Fin m} (h : cross (K.u i) (K.u j) = 0) :
    j = i ∨ K.u j = -K.u i := by
  rcases unit_cross_zero (hG.unit i) (hG.unit j) h with h' | h'
  · exact Or.inl (hG.inj h')
  · exact Or.inr h'

/-- A pair of antiparallel sides satisfies `ParPair`. -/
lemma GoodSides.parPair (hG : GoodSides K) {k kb : Fin m} (h : K.u kb = -K.u k) :
    ParPair K k kb := by
  refine ⟨hG.unit k, h, hG.width k kb h, ?_⟩
  obtain ⟨j, hj⟩ := hG.nondeg k
  rw [← dot_tang_eq_cross] at hj
  rcases lt_or_gt_of_ne hj with hneg | hpos
  · by_contra hno
    simp only [not_exists, not_lt] at hno
    have hnn : ∀ i ∈ Finset.univ, (K.b i - K.a i) * dot (K.u i) (tang K k) ≤ 0 :=
      fun i _ => mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (K.hab i).le) (hno i)
    have hlt : (K.b j - K.a j) * dot (K.u j) (tang K k) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr (K.hab j)) hneg
    have hsum : ∑ i, (K.b i - K.a i) * dot (K.u i) (tang K k) < ∑ _i : Fin m, (0 : ℝ) :=
      Finset.sum_lt_sum hnn ⟨j, Finset.mem_univ j, hlt⟩
    rw [Finset.sum_const_zero] at hsum
    rw [tangent_balance] at hsum
    exact lt_irrefl _ hsum
  · exact ⟨j, hpos⟩

/-! ### Null events -/

variable (K) in
/-- Two points on antiparallel sides at opposite positions. -/
def Opp2 (x : Fin 1 → Pt m) (q : Pt m) : Prop :=
  K.u q.1 = -K.u (x 0).1 ∧ (x 0).2.1 + q.2.1 = 0

variable (K) in
/-- Three points on pairwise non-parallel sides satisfying the KKT relation of positions. -/
def Tri3 (x : Fin 2 → Pt m) (q : Pt m) : Prop :=
  cross (K.u (x 0).1) (K.u (x 1).1) ≠ 0 ∧
    cross (K.u (x 1).1) (K.u q.1) * (x 0).2.1 + cross (K.u q.1) (K.u (x 0).1) * (x 1).2.1 +
      cross (K.u (x 0).1) (K.u (x 1).1) * q.2.1 = 0

lemma measurable_side_fun {β : Type*} [MeasurableSpace β] (g : Fin m → ℝ) {f : β → Pt m}
    (hf : Measurable f) : Measurable fun b => g (f b).1 :=
  (measurable_of_countable g).comp (measurable_fst.comp hf)

lemma measurable_cross_sides {β : Type*} [MeasurableSpace β] {f g : β → Pt m}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => cross (K.u (f b).1) (K.u (g b).1) :=
  (measurable_of_countable fun ij : Fin m × Fin m => cross (K.u ij.1) (K.u ij.2)).comp
    ((measurable_fst.comp hf).prodMk (measurable_fst.comp hg))

lemma measurableSet_Opp2 : MeasurableSet {q : (Fin 1 → Pt m) × Pt m | Opp2 K q.1 q.2} := by
  have hx : Measurable fun q : (Fin 1 → Pt m) × Pt m => q.1 0 :=
    (measurable_pi_apply 0).comp measurable_fst
  have h1 : MeasurableSet {q : (Fin 1 → Pt m) × Pt m | K.u q.2.1 = -K.u (q.1 0).1} :=
    measurableSet_eq_fun ((measurable_of_countable K.u).comp (measurable_fst.comp measurable_snd))
      ((measurable_of_countable fun i => -K.u i).comp (measurable_fst.comp hx))
  exact h1.inter (measurableSet_eq_fun ((measurable_fst.comp (measurable_snd.comp hx)).add
    (measurable_fst.comp (measurable_snd.comp measurable_snd))) measurable_const)

lemma measurableSet_Tri3 : MeasurableSet {q : (Fin 2 → Pt m) × Pt m | Tri3 K q.1 q.2} := by
  have h0 : Measurable fun q : (Fin 2 → Pt m) × Pt m => q.1 0 :=
    (measurable_pi_apply 0).comp measurable_fst
  have h1 : Measurable fun q : (Fin 2 → Pt m) × Pt m => q.1 1 :=
    (measurable_pi_apply 1).comp measurable_fst
  have hq : Measurable fun q : (Fin 2 → Pt m) × Pt m => q.2 := measurable_snd
  have hs : ∀ {f : (Fin 2 → Pt m) × Pt m → Pt m}, Measurable f → Measurable fun q => (f q).2.1 :=
    fun hf => measurable_fst.comp (measurable_snd.comp hf)
  exact (measurableSet_eq_fun (measurable_cross_sides h0 h1) measurable_const).compl.inter
    (measurableSet_eq_fun ((((measurable_cross_sides h1 hq).mul (hs h0)).add
      ((measurable_cross_sides hq h0).mul (hs h1))).add
        ((measurable_cross_sides h0 h1).mul (hs hq))) measurable_const)

variable (K) in
theorem opp2_null (T : ℝ) : PoissonPP.law (Λ K T) {ω | BadP (Opp2 K) ω} = 0 :=
  badP_prob_zero K measurableSet_Opp2 T fun x =>
    measure_mono_null (fun q (hq : Opp2 K x q) => (show q.2.1 = -(x 0).2.1 by linarith [hq.2]))
      (intensity_position_zero K T _)

variable (K) in
theorem tri3_null (T : ℝ) : PoissonPP.law (Λ K T) {ω | BadP (Tri3 K) ω} = 0 := by
  refine badP_prob_zero K measurableSet_Tri3 T fun x => ?_
  let c : Fin m → ℝ := fun l => -(cross (K.u (x 1).1) (K.u l) * (x 0).2.1 +
    cross (K.u l) (K.u (x 0).1) * (x 1).2.1) / cross (K.u (x 0).1) (K.u (x 1).1)
  refine measure_mono_null (t := ⋃ l, {q : Pt m | q.2.1 = c l}) ?_
    (measure_iUnion_null fun l => intensity_position_zero K T _)
  intro q hq
  obtain ⟨hz, hrel⟩ := (hq : Tri3 K x q)
  refine mem_iUnion.mpr ⟨q.1, ?_⟩
  change q.2.1 = c q.1
  simp only [c]
  rw [eq_div_iff hz]
  linarith

/-! ### The support of the KKT multipliers -/

lemma row_apply0 (q : Pt m) : row K q 0 = K.h q.1 := rfl
lemma row_apply1 (q : Pt m) : row K q 1 = (K.u q.1).1 := rfl
lemma row_apply2 (q : Pt m) : row K q 2 = (K.u q.1).2 := rfl
lemma row_apply3 (q : Pt m) : row K q 3 = -q.2.1 := rfl

/-- Two positive multiples of unit vectors cancelling: equal weights, opposite vectors. -/
lemma pair_balance {u v : ℝ × ℝ} (hu : u.1 ^ 2 + u.2 ^ 2 = 1) (hv : v.1 ^ 2 + v.2 ^ 2 = 1)
    {M N : ℝ} (hM : 0 < M) (hN : 0 < N) (h1 : M * u.1 + N * v.1 = 0)
    (h2 : M * u.2 + N * v.2 = 0) : M = N ∧ v = -u := by
  have hsq : N ^ 2 = M ^ 2 := by
    have e1 : N * v.1 = -(M * u.1) := by linarith
    have e2 : N * v.2 = -(M * u.2) := by linarith
    calc N ^ 2 = (N * v.1) ^ 2 + (N * v.2) ^ 2 := by rw [mul_pow, mul_pow, ← mul_add, hv, mul_one]
      _ = (M * u.1) ^ 2 + (M * u.2) ^ 2 := by rw [e1, e2]; ring
      _ = M ^ 2 := by rw [mul_pow, mul_pow, ← mul_add, hu, mul_one]
  have hMN : M = N := by nlinarith
  subst hMN
  refine ⟨rfl, Prod.ext ?_ ?_⟩
  · have := mul_left_cancel₀ hM.ne' (show M * v.1 = M * (-u).1 by simp; linarith)
    exact this
  · have := mul_left_cancel₀ hM.ne' (show M * v.2 = M * (-u).2 by simp; linarith)
    exact this

variable (hG : GoodSides K)
include hG

lemma GoodSides.u_ne_zero (i : Fin m) {M : ℝ} (hM : 0 < M) (h1 : M * (K.u i).1 = 0)
    (h2 : M * (K.u i).2 = 0) : False := by
  have a := (mul_eq_zero.mp h1).resolve_left hM.ne'
  have b := (mul_eq_zero.mp h2).resolve_left hM.ne'
  have := hG.unit i
  rw [a, b] at this; norm_num at this

/-- **The support of the KKT multipliers, at most three points.** -/
theorem general_support {n : ℕ} (y : Fin n → Pt m) (t : Finset (Fin n)) (μ : Fin n → ℝ)
    (hμ : ∀ i ∈ t, 0 < μ i) (hli : LinearIndependent ℝ (fun i : t => row K (y i)))
    (he : (Pi.single 0 1 : Fin 4 → ℝ) = ∑ i ∈ t, μ i • row K (y i)) (h3 : t.card ≤ 3) :
    (∃ k kb : Fin m, ∃ a b c : Fin n, K.u kb = -K.u k ∧ t = {a, b, c} ∧ a ≠ b ∧
      (y a).1 = k ∧ (y b).1 = k ∧ (y c).1 = kb ∧
      (y a).2.1 < -(y c).2.1 ∧ -(y c).2.1 < (y b).2.1) ∨
    (∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ Opp2 K (fun _ => y a) (y b)) ∨
    (∃ a ∈ t, ∃ b ∈ t, ∃ c ∈ t, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Tri3 K ![y a, y b] (y c)) := by
  have hc : ∀ q : Fin 4, (Pi.single 0 1 : Fin 4 → ℝ) q = ∑ i ∈ t, μ i * row K (y i) q := by
    intro q; rw [he, Finset.sum_apply]; rfl
  have E0 : ∑ i ∈ t, μ i * K.h (y i).1 = 1 := by
    have := hc 0; simp only [row_apply0, Pi.single_eq_same] at this; exact this.symm
  have E1 : ∑ i ∈ t, μ i * (K.u (y i).1).1 = 0 := by
    have := hc 1; simp only [row_apply1] at this; simp [Pi.single_apply] at this; linarith
  have E2 : ∑ i ∈ t, μ i * (K.u (y i).1).2 = 0 := by
    have := hc 2; simp only [row_apply2] at this; simp [Pi.single_apply] at this; linarith
  have E3 : ∑ i ∈ t, μ i * (y i).2.1 = 0 := by
    have := hc 3
    simp only [row_apply3, mul_neg, Finset.sum_neg_distrib] at this
    simp [Pi.single_apply] at this; linarith
  -- distinct support points on a side have distinct positions
  have hpos : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → (y a).1 = (y b).1 → (y a).2.1 ≠ (y b).2.1 := by
    intro a ha b hb hab hs he'
    have h := hli.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (by
      funext q; fin_cases q <;> simp [row, hs, he'])
    exact hab (congrArg Subtype.val h)
  -- a segment from two points on a side and one on another
  have segcase : ∀ a b c : Fin n, a ∈ t → b ∈ t → c ∈ t → a ≠ b → t = {a, b, c} →
      (y a).1 = (y b).1 → K.u (y c).1 = -K.u (y a).1 → μ a + μ b = μ c →
      ∃ k kb : Fin m, ∃ a b c : Fin n, K.u kb = -K.u k ∧ t = {a, b, c} ∧ a ≠ b ∧
        (y a).1 = k ∧ (y b).1 = k ∧ (y c).1 = kb ∧
        (y a).2.1 < -(y c).2.1 ∧ -(y c).2.1 < (y b).2.1 := by
    intro a b c ha hb hc' hab htt hab' hu hsum
    have hac : a ≠ c := by
      intro h; rw [← h] at hu
      exact hG.u_ne_zero (y a).1 two_pos (by have := congrArg Prod.fst hu; simp at this; linarith)
        (by have := congrArg Prod.snd hu; simp at this; linarith)
    have hbc : b ≠ c := by
      intro h; rw [← h, ← hab'] at hu
      exact hG.u_ne_zero (y a).1 two_pos (by have := congrArg Prod.fst hu; simp at this; linarith)
        (by have := congrArg Prod.snd hu; simp at this; linarith)
    have hsum3 : ∀ f : Fin n → ℝ, ∑ i ∈ t, f i = f a + f b + f c := by
      intro f; rw [htt, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
        Finset.sum_singleton]; ring
    have e0 := E0; have e3 := E3
    rw [hsum3] at e0 e3
    have hw := hG.width (y a).1 (y c).1 hu
    have hw1 : (μ a + μ b) * (K.h (y a).1 + K.h (y c).1) = 1 := by
      rw [← hab'] at e0; rw [← hsum] at e0; linarith
    rcases lt_or_gt_of_ne (hpos a ha b hb hab hab') with hlt | hgt
    · obtain ⟨h1, h2⟩ := (kkt_segment_iff (s₃ := (y c).2.1) hlt hw).mp
        ⟨μ a, μ b, μ c, hμ a ha, hμ b hb, hμ c hc', hsum, hw1, e3⟩
      exact ⟨(y a).1, (y c).1, a, b, c, hu, htt, hab, rfl, hab'.symm, rfl, h1, h2⟩
    · obtain ⟨h1, h2⟩ := (kkt_segment_iff (s₃ := (y c).2.1)
        (w := K.h (y a).1 + K.h (y c).1) hgt hw).mp
        ⟨μ b, μ a, μ c, hμ b hb, hμ a ha, hμ c hc', by linarith, by linarith, by linarith⟩
      refine ⟨(y a).1, (y c).1, b, a, c, hu, by rw [htt, Finset.insert_comm], hab.symm, hab'.symm,
        rfl, rfl, h1, h2⟩
  rcases (by omega : t.card = 0 ∨ t.card = 1 ∨ t.card = 2 ∨ t.card = 3) with h0 | h1 | h2 | h3'
  · exfalso
    rw [Finset.card_eq_zero.mp h0] at E0
    simp at E0
  · exfalso
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    simp only [Finset.sum_singleton] at E1 E2
    exact hG.u_ne_zero _ (hμ a (by simp)) E1 E2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    rw [Finset.sum_pair hab] at E1 E2 E3
    obtain ⟨hMN, huv⟩ := pair_balance (hG.unit _) (hG.unit _) (hμ a (by simp)) (hμ b (by simp))
      E1 E2
    right; left
    refine ⟨a, by simp, b, by simp, hab, huv, ?_⟩
    rw [hMN] at E3
    have : μ b * ((y a).2.1 + (y b).2.1) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (hμ b (by simp)).ne'
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h3'
    have ha : a ∈ ({a, b, c} : Finset (Fin n)) := by simp
    have hb : b ∈ ({a, b, c} : Finset (Fin n)) := by simp
    have hc' : c ∈ ({a, b, c} : Finset (Fin n)) := by simp
    have hsum3 : ∀ f : Fin n → ℝ, ∑ i ∈ ({a, b, c} : Finset (Fin n)), f i = f a + f b + f c := by
      intro f; rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
        Finset.sum_singleton]; ring
    have e1 := E1; have e2 := E2; have e3 := E3
    rw [hsum3] at e1 e2 e3
    have hμa := hμ a ha; have hμb := hμ b hb; have hμc := hμ c hc'
    by_cases sab : (y a).1 = (y b).1
    · by_cases sac : (y a).1 = (y c).1
      · exfalso
        rw [← sab, ← sac] at e1 e2
        exact hG.u_ne_zero (y a).1 (by linarith : 0 < μ a + μ b + μ c) (by linarith) (by linarith)
      · rw [← sab] at e1 e2
        obtain ⟨hMN, huv⟩ := pair_balance (hG.unit (y a).1) (hG.unit (y c).1)
          (by linarith : 0 < μ a + μ b) hμc (by linarith) (by linarith)
        left
        exact segcase a b c ha hb hc' hab rfl sab huv hMN
    · by_cases sac : (y a).1 = (y c).1
      · rw [← sac] at e1 e2
        obtain ⟨hMN, huv⟩ := pair_balance (hG.unit (y a).1) (hG.unit (y b).1)
          (by linarith : 0 < μ a + μ c) hμb (by linarith) (by linarith)
        left
        exact segcase a c b ha hc' hb hac (by rw [Finset.pair_comm]) sac huv hMN
      · by_cases sbc : (y b).1 = (y c).1
        · rw [← sbc] at e1 e2
          obtain ⟨hMN, huv⟩ := pair_balance (hG.unit (y b).1) (hG.unit (y a).1)
            (by linarith : 0 < μ b + μ c) hμa (by linarith) (by linarith)
          left
          exact segcase b c a hb hc' ha hbc (by ext x; simp; tauto) sbc huv hMN
        · -- three pairwise non-parallel sides
          right; right
          refine ⟨a, ha, b, hb, c, hc', hab, hac, hbc, ?_⟩
          have hcr : cross (K.u (y a).1) (K.u (y b).1) ≠ 0 := by
            intro hz
            rcases hG.parallel hz with h | h
            · exact sab h.symm
            · rw [h] at e1 e2
              simp only [Prod.fst_neg, Prod.snd_neg] at e1 e2
              have hac0 : μ c * cross (K.u (y a).1) (K.u (y c).1) = 0 := by
                simp only [cross]
                linear_combination (K.u (y a).1).1 * e2 - (K.u (y a).1).2 * e1
              have hz' := (mul_eq_zero.mp hac0).resolve_left hμc.ne'
              rcases hG.parallel hz' with h' | h'
              · exact sac h'.symm
              · exact sbc (hG.inj (h.trans h'.symm))
          refine ⟨by simpa using hcr, ?_⟩
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
          have key : μ a * (cross (K.u (y b).1) (K.u (y c).1) * (y a).2.1 +
              cross (K.u (y c).1) (K.u (y a).1) * (y b).2.1 +
              cross (K.u (y a).1) (K.u (y b).1) * (y c).2.1) = 0 := by
            simp only [cross]
            linear_combination
              ((K.u (y b).1).1 * (K.u (y c).1).2 - (K.u (y b).1).2 * (K.u (y c).1).1) * e3 +
              (y b).2.1 * ((K.u (y c).1).1 * e2 - (K.u (y c).1).2 * e1) +
              (y c).2.1 * ((K.u (y b).1).2 * e1 - (K.u (y b).1).1 * e2)
          exact (mul_eq_zero.mp key).resolve_left hμa.ne'

/-! ### Every fitting optimum is a candidate, almost surely -/

omit hG in
lemma badP_one {n : ℕ} {P : (Fin 1 → Pt m) → Pt m → Prop} (y : Fin n → Pt m) {a b : Fin n}
    (hab : a ≠ b) (h : P (fun _ => y a) (y b)) : BadP P ⟨n, y⟩ := by
  refine ⟨⟨![a, b], fun r r' hr => ?_⟩, ?_⟩
  · fin_cases r <;> fin_cases r' <;> simp_all [eq_comm]
  · have hx : (fun r : Fin 1 => (y ∘ ![a, b]) ((Fin.last 1).succAbove r)) = fun _ => y a := by
      funext r; fin_cases r; rfl
    change P (fun r : Fin 1 => (y ∘ ![a, b]) ((Fin.last 1).succAbove r)) (y b)
    rw [hx]; exact h

omit hG in
lemma badP_two {n : ℕ} {P : (Fin 2 → Pt m) → Pt m → Prop} (y : Fin n → Pt m) {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h : P ![y a, y b] (y c)) : BadP P ⟨n, y⟩ := by
  refine ⟨⟨![a, b, c], fun r r' hr => ?_⟩, ?_⟩
  · fin_cases r <;> fin_cases r' <;> simp_all [eq_comm]
  · have hx : (fun r : Fin 2 => (y ∘ ![a, b, c]) ((Fin.last 2).succAbove r)) = ![y a, y b] := by
      funext r; fin_cases r <;> rfl
    change P (fun r : Fin 2 => (y ∘ ![a, b, c]) ((Fin.last 2).succAbove r)) (y c)
    rw [hx]; exact h

/-- **Classification of fitting optima.** If some optimal copy fits (below the cutoff), there is
a certified vertex candidate, or a segment candidate on an ordered pair of parallel sides, or one
of the two null events `Opp2`, `Tri3` occurs. -/
theorem general_classify (T : ℝ) (ω : PoissonPP.Sample (Pt m)) (h : OptFit K T ω) :
    HasVertexCandidate K T ω ∨ (∃ k kb : Fin m, K.u kb = -K.u k ∧ HasSegCand K k kb T ω) ∨
      BadP (Opp2 K) ω ∨ BadP (Tri3 K) ω := by
  classical
  obtain ⟨n, y⟩ := ω
  obtain ⟨z, hF, hB, hfeas, hopt⟩ := h
  obtain ⟨t, μ, ht, hμ, hli, he⟩ := optimum_kkt K y z hfeas hopt
  have hle4 : t.card ≤ 4 := by
    have := hli.fintype_card_le_finrank
    simpa using this
  by_cases h4 : t.card = 4
  · -- four tight points: a vertex candidate
    left
    let e : t ≃ Fin 4 := t.equivFinOfCardEq h4
    let f : Fin 4 ↪ Fin n := ⟨fun r => (e.symm r).1, fun r r' hr =>
      e.symm.injective (Subtype.ext hr)⟩
    have hli4 : LinearIndependent ℝ (fun r => row K (y (f r))) :=
      hli.comp e.symm e.symm.injective
    have hA : (vertexMatrix K (y ∘ f)).det ≠ 0 := by
      have hu : IsUnit (vertexMatrix K (y ∘ f)) := Matrix.linearIndependent_rows_iff_isUnit.mp hli4
      exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    have hsum : ∑ i ∈ t, μ i • row K (y i) = ∑ r, μ (f r) • row K (y (f r)) := by
      rw [← Finset.sum_coe_sort t]
      exact (Equiv.sum_comp e.symm (fun i : t => μ i • row K (y i))).symm
    have hcert : ∀ c, ∑ r, μ (f r) * row K ((y ∘ f) r) c = if c = 0 then 1 else 0 := by
      intro c
      have h1 := congrFun he c
      rw [hsum, Finset.sum_apply] at h1
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h1
      exact h1.symm
    have hmem : ∀ r, f r ∈ t := fun r => (e.symm r).2
    have hc := vertexCert_eq_of_certificate K (y ∘ f) hA _ hcert
    have hz := vertexCopy_eq_of_tight K (y ∘ f) hA z fun r => ht _ (hmem r)
    refine ⟨f, ⟨hA, ?_, ?_, ?_⟩, ?_⟩
    · rw [hc]; exact fun r => hμ _ (hmem r)
    · rw [hz]; exact hF
    · rw [hz]; exact hB
    · rw [hz]; exact hfeas
  rcases general_support hG y t μ hμ hli he (by omega) with hS | hO | hT
  · -- a segment candidate
    right; left
    obtain ⟨k, kb, a, b, c, hu, htt, hab, hsa, hsb, hsc, h1, h2⟩ := hS
    have hP := hG.parPair hu
    have hac : a ≠ c := by intro h; rw [h, hsc] at hsa; exact hP.ne hsa.symm
    have hbc : b ≠ c := by intro h; rw [h, hsc] at hsb; exact hP.ne hsb.symm
    let g : Fin 3 ↪ Fin n := ⟨![a, b, c], fun r r' hr => by
      fin_cases r <;> fin_cases r' <;> simp_all [eq_comm]⟩
    have hg : SegGood k kb (y ∘ g) := ⟨hsa, hsb, hsc, h1, h2⟩
    have htight : ∀ r, gx K z ((y ∘ g) r) = 0 := by
      intro r
      fin_cases r
      · exact ht a (by rw [htt]; simp)
      · exact ht b (by rw [htt]; simp)
      · exact ht c (by rw [htt]; simp)
    have hz := segCopy_of_tight K hP hg z htight
    refine ⟨k, kb, hu, g, hg, dot z.2.1 (tang K k), ⟨?_, ?_⟩, ?_⟩
    · rw [← hz]; exact hF
    · rw [← hz]; exact hB
    · rw [← hz]; exact hfeas
  · right; right; left
    obtain ⟨a, -, b, -, hab, hO⟩ := hO
    exact badP_one y hab hO
  · right; right; right
    obtain ⟨a, -, b, -, c, -, hab, hac, hbc, hT⟩ := hT
    exact badP_two y hab hac hbc hT

/-! ### The candidate events overlap only on null events -/

/-- A certified vertex candidate and a segment candidate: only on a null event. The segment
points would be tight vertex points, and the segment multipliers would give a second
certificate, missing the fourth row. -/
lemma vertex_seg_null_gen (T : ℝ) {k kb : Fin m} (hu : K.u kb = -K.u k)
    (ω : PoissonPP.Sample (Pt m)) (hV : HasVertexCandidate K T ω) (hS : HasSegCand K k kb T ω) :
    BadExtra K (vertexCopy K) ω := by
  classical
  obtain ⟨n, y⟩ := ω
  by_contra hbad
  have hP := hG.parPair hu
  obtain ⟨i, hgV, hfV⟩ := hV
  obtain ⟨j, hg, c, -, hfS⟩ := hS
  have hfV' := (feasible_config_iff K y _).mp hfV
  have hfS' := (feasible_config_iff K y _).mp hfS
  have h1 := vertexGood_optimal K T _ hgV _ fun r => hfS' (i r)
  have h2 := (seg_optimal hP hg (vertexCopy K (y ∘ i)) fun r => hfV' (j r)).1
  have heq := vertexGood_unique K T _ hgV _ (fun r => hfS' (i r)) (le_antisymm h2 h1)
  have hin : ∀ r, ∃ r', i r' = j r := by
    intro r
    have ht : gx K (vertexCopy K (y ∘ i)) (y (j r)) = 0 := by
      rw [← heq]; exact segCopy_tight hP hg c r
    exact tight_index_in_range K y hbad i (j r) ht
  choose σ hσ using hin
  have hσi : Function.Injective σ := fun r r' h => j.injective (by rw [← hσ, ← hσ, h])
  obtain ⟨r4, hr4⟩ : ∃ r4, ∀ r, σ r ≠ r4 := by
    by_contra hno
    push Not at hno
    have := Fintype.card_le_of_surjective σ fun x => (hno x).imp fun r h => h
    simp at this
  -- the segment multipliers
  obtain ⟨μ0, μ1, _, -, -, -, rfl, hw, hs⟩ :=
    (kkt_segment_iff (s₃ := (y (j 2)).2.1) hg.lt hP.width).mpr ⟨hg.2.2.2.1, hg.2.2.2.2⟩
  simp only [Function.comp_apply] at hs
  let μ : Fin 3 → ℝ := ![μ0, μ1, μ0 + μ1]
  have a0 : (y (j 0)).1 = k := hg.1
  have a1 : (y (j 1)).1 = k := hg.2.1
  have a2 : (y (j 2)).1 = kb := hg.2.2.1
  have hμrow : ∀ c', ∑ r, μ r * row K (y (j r)) c' = if c' = 0 then 1 else 0 := by
    intro c'
    fin_cases c' <;>
      simp [Fin.sum_univ_three, μ, row_apply0, row_apply1, row_apply2, row_apply3, a0, a1, a2, hu]
    · linear_combination hw
    · ring
    · ring
    · linear_combination -hs
  -- the vertex certificate
  have hl := vertexCert_eq K (y ∘ i) hgV.1
  let l' : Fin 4 → ℝ := fun x => ∑ r, if σ r = x then μ r else 0
  have hl' : ∀ c', ∑ x, l' x * row K ((y ∘ i) x) c' = if c' = 0 then 1 else 0 := by
    intro c'
    rw [← hμrow c']
    simp only [l', Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_ite_eq]
    simp [hσ]
  have hli4 : LinearIndependent ℝ (fun r => row K ((y ∘ i) r)) :=
    Matrix.linearIndependent_rows_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hgV.1))
  have hzero := Fintype.linearIndependent_iff.mp hli4 (fun x => vertexCert K (y ∘ i) x - l' x)
    (by
      funext c'
      have := hl c'; have := hl' c'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul,
        Finset.sum_sub_distrib]
      linarith) r4
  have hl'4 : l' r4 = 0 := Finset.sum_eq_zero fun r _ => by simp [hr4 r]
  have := hgV.2.1 r4
  rw [sub_eq_zero.mp hzero, hl'4] at this
  exact lt_irrefl 0 this

/-- Segment candidates on a pair and on the reversed pair: only on a null event. -/
lemma seg_rev_null_gen (T : ℝ) {k kb : Fin m} (hu : K.u kb = -K.u k)
    (ω : PoissonPP.Sample (Pt m)) (hS : HasSegCand K k kb T ω) (hS' : HasSegCand K kb k T ω) :
    BadExtra K (segBase K k kb) ω := by
  obtain ⟨n, y⟩ := ω
  by_contra hbad
  obtain ⟨i, hg, c, -, hf⟩ := hS
  obtain ⟨j, hg', c', -, hf'⟩ := hS'
  have hP := hG.parPair hu
  have hP' := hG.parPair (show K.u k = -K.u kb by rw [hu, neg_neg])
  have hfi := (feasible_config_iff K y _).mp hf
  have hfj := (feasible_config_iff K y _).mp hf'
  have h1 := (seg_optimal hP hg _ fun r => hfj (i r)).1
  have h2 := seg_optimal hP' hg' _ fun r => hfi (j r)
  rw [segCopy_fst] at h1 h2
  have hrange : ∀ r, ∃ r', i r' = j r := by
    intro r
    have ht := h2.2 (le_antisymm h2.1 h1).symm r
    have hside : (y (j r)).1 = k ∨ (y (j r)).1 = kb := by
      match r with
      | 0 => exact Or.inr hg'.1
      | 1 => exact Or.inr hg'.2.1
      | 2 => exact Or.inl hg'.2.2.1
    change gx K (segCopy K k (segVec K k kb (y ∘ i)) c) (y (j r)) = 0 at ht
    rw [gx_segCopy_side hP _ _ _ hside] at ht
    exact seg_tight_in_range y hbad i (j r) ht
  have hk : ∀ r, (y (j r)).1 = kb → ∀ r', i r' = j r → r' = 2 := by
    intro r hr r' he
    have a0 : (y (i 0)).1 = k := hg.1
    have a1 : (y (i 1)).1 = k := hg.2.1
    match r', he with
    | 0, he => rw [← he, a0] at hr; exact absurd hr hP.ne
    | 1, he => rw [← he, a1] at hr; exact absurd hr hP.ne
    | 2, _ => rfl
  obtain ⟨r0, hr0⟩ := hrange 0
  obtain ⟨r1, hr1⟩ := hrange 1
  have e0 := hk 0 hg'.1 r0 hr0
  have e1 := hk 1 hg'.2.1 r1 hr1
  rw [e0] at hr0; rw [e1] at hr1
  exact absurd (j.injective (hr0.symm.trans hr1)) (by decide)

/-- Three segment points and a point on a non-parallel side have an invertible tight matrix. -/
lemma gen_perp_det {k kb k' : Fin m} (hu : K.u kb = -K.u k) (hk' : cross (K.u k) (K.u k') ≠ 0)
    (q : Fin 4 → Pt m) (h0 : (q 0).1 = k) (h1 : (q 1).1 = k) (h2 : (q 2).1 = kb)
    (h3 : (q 3).1 = k') (hs : (q 0).2.1 ≠ (q 1).2.1) : (vertexMatrix K q).det ≠ 0 := by
  have hli : LinearIndependent ℝ (vertexMatrix K q).row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e : ∀ c, ∑ r, g r * row K (q r) c = 0 := fun c => by
      have := congrFun hg c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      exact this
    have c0 := e 0
    have c1 := e 1
    have c2 := e 2
    have c3 := e 3
    simp only [Fin.sum_univ_four, row_apply0, row_apply1, row_apply2, row_apply3, h0, h1, h2, h3,
      hu, Prod.fst_neg, Prod.snd_neg] at c0 c1 c2 c3
    have g3 : g 3 = 0 := by
      have hm : g 3 * cross (K.u k) (K.u k') = 0 := by
        simp only [cross]; linear_combination (K.u k).1 * c2 - (K.u k).2 * c1
      exact (mul_eq_zero.mp hm).resolve_right hk'
    rw [g3] at c0 c1 c2 c3
    have hG' : g 0 + g 1 - g 2 = 0 := by
      linear_combination (K.u k).1 * c1 + (K.u k).2 * c2 - (g 0 + g 1 - g 2) * hG.unit k
    have hsum : g 0 + g 1 = 0 := by
      have hw := hG.width k kb hu
      have hm : (g 0 + g 1) * (K.h k + K.h kb) = 0 := by
        have : g 2 = g 0 + g 1 := by linarith
        rw [this] at c0; linarith
      exact (mul_eq_zero.mp hm).resolve_right hw.ne'
    have g2 : g 2 = 0 := by linarith
    have g10 : g 1 = -g 0 := by linarith
    have hm : g 0 * ((q 0).2.1 - (q 1).2.1) = 0 := by
      rw [g2, g10] at c3; linarith
    have g0 : g 0 = 0 := (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hs)
    intro r
    fin_cases r <;> simp [g0, g2, g3, g10]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hli)).ne_zero

/-- Segment candidates on two different parallel classes: only on a null event. -/
lemma seg_perp_null_gen (T : ℝ) {k kb k' kb' : Fin m} (hu : K.u kb = -K.u k)
    (hu' : K.u kb' = -K.u k') (hk : k' ≠ k) (hkb : k' ≠ kb) (ω : PoissonPP.Sample (Pt m))
    (hS : HasSegCand K k kb T ω) (hS' : HasSegCand K k' kb' T ω) :
    BadExtra K (vertexCopy K) ω := by
  obtain ⟨n, y⟩ := ω
  by_contra hbad
  obtain ⟨i, hg, c, -, hf⟩ := hS
  obtain ⟨j, hg', c', -, hf'⟩ := hS'
  have hP := hG.parPair hu
  have hP' := hG.parPair hu'
  have hcr : cross (K.u k) (K.u k') ≠ 0 := by
    intro hz
    rcases hG.parallel hz with h | h
    · exact hk h
    · exact hkb (hG.inj (h.trans hu.symm))
  have hfi := (feasible_config_iff K y _).mp hf
  have hfj := (feasible_config_iff K y _).mp hf'
  have h1 := (seg_optimal hP hg _ fun r => hfj (i r)).1
  have h2 := seg_optimal hP' hg' _ fun r => hfi (j r)
  rw [segCopy_fst] at h1 h2
  set zS := segCopy K k (segVec K k kb (y ∘ i)) c
  have htj : ∀ r, gx K zS (y (j r)) = 0 := h2.2 (le_antisymm h2.1 h1).symm
  have hsi : ∀ r, (y (i r)).1 = k ∨ (y (i r)).1 = kb := fun r => by
    match r with
    | 0 => exact Or.inl hg.1
    | 1 => exact Or.inl hg.2.1
    | 2 => exact Or.inr hg.2.2.1
  have hj0 : (y (j 0)).1 = k' := hg'.1
  have hj1 : (y (j 1)).1 = k' := hg'.2.1
  have hij : ∀ r, i r ≠ j 0 ∧ i r ≠ j 1 := by
    intro r
    constructor <;> intro he <;> rcases hsi r with h | h
    · rw [he, hj0] at h; exact hk h
    · rw [he, hj0] at h; exact hkb h
    · rw [he, hj1] at h; exact hk h
    · rw [he, hj1] at h; exact hkb h
  let f : Fin 4 ↪ Fin n := ⟨![i 0, i 1, i 2, j 0], fun r r' hr => by
    have h01 : i 0 ≠ i 1 := i.injective.ne (by decide)
    have h02 : i 0 ≠ i 2 := i.injective.ne (by decide)
    have h12 : i 1 ≠ i 2 := i.injective.ne (by decide)
    have := hij 0; have := hij 1; have := hij 2
    fin_cases r <;> fin_cases r' <;> simp_all [eq_comm]⟩
  have hdet : (vertexMatrix K (y ∘ f)).det ≠ 0 :=
    gen_perp_det hG hu hcr (y ∘ f) hg.1 hg.2.1 hg.2.2.1 hj0 hg.lt.ne
  have hz : vertexCopy K (y ∘ f) = zS := by
    apply vertexCopy_eq_of_tight K _ hdet
    intro r
    fin_cases r
    · exact segCopy_tight hP hg c 0
    · exact segCopy_tight hP hg c 1
    · exact segCopy_tight hP hg c 2
    · exact htj 0
  have ht1 : gx K (vertexCopy K (y ∘ f)) (y (j 1)) = 0 := by rw [hz]; exact htj 1
  obtain ⟨r, hr⟩ := tight_index_in_range K y hbad f (j 1) ht1
  fin_cases r
  · exact (hij 0).2 hr
  · exact (hij 1).2 hr
  · exact (hij 2).2 hr
  · exact absurd (j.injective hr) (by decide)

/-! ### Theorem 8 in the model -/

variable (K) in
/-- Ordered pairs of parallel sides. -/
noncomputable def parPairs : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun p => K.u p.2 = -K.u p.1

omit hG in
variable (K) in
lemma general_null_zero (T : ℝ) : PoissonPP.law (Λ K T)
    (({ω | BadExtra K (vertexCopy K) ω} ∪ {ω | BadP (Opp2 K) ω} ∪ {ω | BadP (Tri3 K) ω}) ∪
      ⋃ p : Fin m × Fin m, {ω | BadExtra K (segBase K p.1 p.2) ω}) = 0 :=
  measure_union_null (measure_union_null (measure_union_null (no_extra_tight_vertex K T)
    (opp2_null K T)) (tri3_null K T))
    (measure_iUnion_null fun p => badExtra_prob_zero K _ (measurable_segBase K p.1 p.2) T)

/-- **The probability of `E` in the truncated model, for a general polygon**: the certified
vertex-candidate probability plus the segment-candidate probabilities of the ordered pairs of
parallel sides. -/
theorem general_optFit_prob (T : ℝ) :
    PoissonPP.law (Λ K T) {ω | OptFit K T ω} =
      PoissonPP.law (Λ K T) {ω | HasVertexCandidate K T ω} +
        ∑ p ∈ parPairs K, PoissonPP.law (Λ K T) {ω | HasSegCand K p.1 p.2 T ω} := by
  set μ := PoissonPP.law (Λ K T)
  set N := ({ω | BadExtra K (vertexCopy K) ω} ∪ {ω | BadP (Opp2 K) ω} ∪
    {ω | BadP (Tri3 K) ω}) ∪ ⋃ p : Fin m × Fin m, {ω | BadExtra K (segBase K p.1 p.2) ω}
  have hN : μ N = 0 := general_null_zero K T
  set S := ⋃ p ∈ parPairs K, {ω | HasSegCand K p.1 p.2 T ω}
  have hsub : {ω | HasVertexCandidate K T ω} ∪ S ⊆ {ω | OptFit K T ω} := by
    rintro ω (h | h)
    · exact optFit_of_vertex K T ω h
    · obtain ⟨p, hp, hk⟩ := mem_iUnion₂.mp h
      exact optFit_of_seg K (hG.parPair (Finset.mem_filter.mp hp).2) T ω hk
  have hsup : {ω | OptFit K T ω} ⊆ ({ω | HasVertexCandidate K T ω} ∪ S) ∪ N := by
    intro ω h
    rcases general_classify hG T ω h with hV | ⟨k, kb, hu, hk⟩ | hO | hT
    · exact Or.inl (Or.inl hV)
    · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨(k, kb), Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hu⟩, hk⟩))
    · exact Or.inr (Or.inl (Or.inl (Or.inr hO)))
    · exact Or.inr (Or.inl (Or.inr hT))
  have hE : μ {ω | OptFit K T ω} = μ ({ω | HasVertexCandidate K T ω} ∪ S) := by
    apply le_antisymm
    · calc μ {ω | OptFit K T ω} ≤ μ (({ω | HasVertexCandidate K T ω} ∪ S) ∪ N) :=
            measure_mono hsup
        _ ≤ μ ({ω | HasVertexCandidate K T ω} ∪ S) + μ N := measure_union_le _ _
        _ = _ := by rw [hN, add_zero]
    · exact measure_mono hsub
  have hSm : ∀ p : Fin m × Fin m, MeasurableSet {ω | HasSegCand K p.1 p.2 T ω} :=
    fun p => measurableSet_HasSegCand K p.1 p.2 T
  have hdisj : (↑(parPairs K) : Set (Fin m × Fin m)).Pairwise
      (Function.onFun (AEDisjoint μ) fun p => {ω | HasSegCand K p.1 p.2 T ω}) := by
    intro p hp p' hp' hne
    have hu := (Finset.mem_filter.mp hp).2
    have hu' := (Finset.mem_filter.mp hp').2
    apply measure_mono_null _ hN
    rintro ω ⟨h, h'⟩
    by_cases h1 : p'.1 = p.1
    · exfalso
      apply hne
      have h2 : p'.2 = p.2 := hG.inj (by rw [hu, hu', h1])
      exact Prod.ext h1.symm h2.symm
    by_cases h2 : p'.1 = p.2
    · have h3 : p'.2 = p.1 := hG.inj (by rw [hu', h2, hu, neg_neg])
      have h'' : HasSegCand K p.2 p.1 T ω := by rw [← h2, ← h3]; exact h'
      exact Or.inr (mem_iUnion.mpr ⟨p, seg_rev_null_gen hG T hu ω h h''⟩)
    · exact Or.inl (Or.inl (Or.inl (seg_perp_null_gen hG T hu hu' h1 h2 ω h h')))
  have hVS : AEDisjoint μ {ω | HasVertexCandidate K T ω} S := by
    apply measure_mono_null _ hN
    rintro ω ⟨hV, hS⟩
    obtain ⟨p, hp, hk⟩ := mem_iUnion₂.mp hS
    exact Or.inl (Or.inl (Or.inl (vertex_seg_null_gen hG T (Finset.mem_filter.mp hp).2 ω hV hk)))
  rw [hE, measure_union₀ (Finset.measurableSet_biUnion _ fun p _ => hSm p).nullMeasurableSet hVS,
    measure_biUnion_finset₀ hdisj fun p _ => (hSm p).nullMeasurableSet]

/-- **Theorem 8 in the Poisson model.** For a polygon satisfying `GoodSides`, the probability
that some optimal copy fits (lines below the cutoff `n`) tends to the vertex term plus the sum
over ordered pairs of parallel sides of the segment terms. -/
theorem general_optFit_limit :
    Filter.Tendsto (fun n : ℕ => PoissonPP.law (Λ K n) {ω | OptFit K n ω}) Filter.atTop
      (nhds (spatialVertexIntegral K * coneVertexDensity K +
        ∑ p ∈ parPairs K, segDensity K p.1 p.2 * ∫⁻ v, chordWeightInf K p.1 v)) := by
  simp_rw [general_optFit_prob hG]
  exact (vertex_candidate_formula_limit K).add (tendsto_finsetSum _ fun p hp =>
    seg_candidate_limit (hG.parPair (Finset.mem_filter.mp hp).2))

omit hG in
/-- The square satisfies the hypotheses of the general classification. -/
theorem squareGood : GoodSides squareSides where
  unit j := by fin_cases j <;> simp [squareSides]
  inj := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [squareSides] <;> norm_num at h
  width i j h := by simp [squareSides]
  nondeg k := ⟨k + 1, by fin_cases k <;> simp [squareSides, cross]⟩

end Enclosing
