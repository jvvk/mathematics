import LeanProofs.TwoTri.FaceTools

/-!
# Two consecutive edges at a vertex bound a face

If `ab` and `ac` are edges of a triangulation `T`, the turn from `ab` to `ac` is counterclockwise
and less than a half turn, and no edge of `T` at `a` lies strictly between them, then `abc` is a
face of `T`.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Height above the vertex `a`, measured towards the side `bc` (zero at `a`). -/
def lev (b c a r : K × K) : K := orient b c a - orient b c r

lemma lev_lerp (b c a p q : K × K) (t : K) :
    lev b c a (lerp p q t) = (1 - t) * lev b c a p + t * lev b c a q := by
  unfold lev; rw [orient_lerp]; ring

@[simp] lemma lev_self (b c a : K × K) : lev b c a a = 0 := by simp [lev]
lemma lev_b (b c a : K × K) : lev b c a b = orient a b c := by
  simp [lev, ← orient_cyc a b c]
lemma lev_c (b c a : K × K) : lev b c a c = orient a b c := by
  simp [lev, ← orient_cyc a b c]

lemma orient_shrink1 (a b r : K × K) (κ : K) : orient a (lerp a b κ) r = κ * orient a b r := by
  unfold orient lerp; ring
lemma orient_shrink2 (a c r : K × K) (κ : K) : orient (lerp a c κ) a r = κ * orient c a r := by
  unfold orient lerp; ring
lemma orient_shrink3 (a b c r : K × K) (κ : K) :
    orient (lerp a b κ) (lerp a c κ) r = κ * (κ * orient a b c - lev b c a r) := by
  unfold lev orient lerp; ring

lemma lerp_shrink_back (a c : K × K) (κ ρ : K) :
    lerp (lerp a c κ) a ρ = lerp a c (κ * (1 - ρ)) := by
  unfold lerp; ext <;> simp <;> ring

lemma ne_pair_of_not_mem {a q q' : K × K} (b : K × K) (h1 : a ≠ q) (h2 : a ≠ q') :
    s(a, b) ≠ s(q', q) := by
  intro e
  rcases Sym2.eq_iff.mp e with ⟨e1, -⟩ | ⟨e1, -⟩
  · exact h2 e1
  · exact h1 e1

/-- The crossing argument in the emptiness half of `consec`. -/
lemma consec_empty_aux {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    (hTnc : NonCross T) {a b c q q' z : K × K} (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P)
    (hD : 0 < orient a b c) (hab : s(a, b) ∈ T) (hac : s(a, c) ∈ T)
    {κ : K} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hmin : ∀ r ∈ P, InTri a b c r → κ * orient a b c ≤ lev b c a r)
    (hq : q ∈ P) (hq' : q' ∈ P) (hqa : q ≠ a) (hq'a : q' ≠ a) (hqq : q ≠ q')
    (hgT : s(q', q) ∈ T) {μ : K} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hzμ : z = lerp q' q μ)
    (hzin : InTri a (lerp a b κ) (lerp a c κ) z) (hℓq : lev b c a q < κ * orient a b c) :
    False := by
  have hab' : a ≠ b := by rintro rfl; simp at hD
  have hac' : a ≠ c := by rintro rfl; simp at hD
  have hzℓ : lev b c a z < κ * orient a b c := by
    have := hzin.2.1; rw [orient_shrink3] at this
    nlinarith
  have hqb : q ≠ b := by rintro rfl; rw [lev_b] at hℓq; nlinarith
  have hqc : q ≠ c := by rintro rfl; rw [lev_c] at hℓq; nlinarith
  have hout : orient a (lerp a b κ) q < 0 ∨ orient (lerp a b κ) (lerp a c κ) q < 0 ∨
      orient (lerp a c κ) a q < 0 := by
    have n1 : orient a b q ≠ 0 := hP a ha b hb q hq hab' (Ne.symm hqa) (Ne.symm hqb)
    have n2 : orient c a q ≠ 0 := hP c hc a ha q hq (Ne.symm hac') (Ne.symm hqc) (Ne.symm hqa)
    by_contra hn; push Not at hn
    rw [orient_shrink1, orient_shrink2] at hn
    have p1 : 0 < orient a b q :=
      lt_of_le_of_ne (nonneg_of_mul_nonneg_right hn.1 hκ0) (Ne.symm n1)
    have p2 : 0 < orient c a q :=
      lt_of_le_of_ne (nonneg_of_mul_nonneg_right hn.2.2 hκ0) (Ne.symm n2)
    have p3 : 0 < orient b c q := by
      unfold lev at hℓq; rw [← orient_cyc a b c] at hℓq; nlinarith
    have := hmin q hq ⟨p1, p3, p2⟩
    linarith
  obtain ⟨t, ht0, ht1, hcase⟩ := exit' hzin hout
  have hmeq : lerp z q t = lerp q' q (μ + t - μ * t) := by rw [hzμ, lerp_lerp]
  have hν := (lerp_sub_mem hμ0 hμ1 ht0 ht1).2
  have hℓm : lev b c a (lerp z q t) < κ * orient a b c := by
    rw [lev_lerp]; nlinarith
  have cross_with : ∀ v ∈ P, s(a, v) ∈ T → a ≠ v → ∀ ρ : K, 0 < ρ → ρ < 1 →
      lerp z q t = lerp a v ρ → False := by
    intro v hv hvT hav ρ hρ0 hρ1 hm
    have := cross_of_common hP ha hv hq' hq hav (Ne.symm hqq)
      (ne_pair_of_not_mem v (Ne.symm hqa) (Ne.symm hq'a)) hρ0 hρ1 hν.1.le hν.2.le
      (hm.symm.trans hmeq)
    exact hTnc _ hvT _ hgT (cross_mk.mpr this)
  rcases hcase with hv | ⟨u, v, o, hrot, h0, hp1, hp2⟩
  · rcases hv with hv | hv | hv
    · have : orient q' q a = 0 := by rw [← hv, hmeq, orient_lerp_self]
      rcases hP.on_line hq' hq ha (Ne.symm hqq) this with h | h
      exacts [hq'a h.symm, hqa h.symm]
    · rw [hv, lev_lerp, lev_self, lev_b] at hℓm; nlinarith
    · rw [hv, lev_lerp, lev_self, lev_c] at hℓm; nlinarith
  · rcases hrot with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨ρ, hρ0, hρ1, hm⟩ := on_side h0 hp1 hp2
      rw [lerp_lerp_left] at hm
      exact cross_with b hb hab hab' (κ * ρ) (mul_pos hκ0 hρ0) (by nlinarith) hm
    · rw [orient_shrink3] at h0
      rcases mul_eq_zero.mp h0 with h | h
      · exact hκ0.ne' h
      · linarith
    · obtain ⟨ρ, hρ0, hρ1, hm⟩ := on_side h0 hp1 hp2
      rw [lerp_shrink_back] at hm
      exact cross_with c hc hac hac' (κ * (1 - ρ)) (mul_pos hκ0 (by linarith)) (by nlinarith) hm

/-- The triangle between two consecutive edges contains no point. -/
lemma consec_empty {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    (hT : IsTri P T) {a b c : K × K} (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P)
    (hD : 0 < orient a b c) (hab : s(a, b) ∈ T) (hac : s(a, c) ∈ T)
    (hW : ∀ y ∈ P, s(a, y) ∈ T → 0 < orient a b y → 0 < orient a y c → False) :
    ∀ q ∈ P, ¬ InTri a b c q := by
  classical
  intro q0 hq0 hq0in
  obtain ⟨x, hxS, hxmin⟩ := (P.filter (InTri a b c)).exists_min_image (lev b c a)
    ⟨q0, Finset.mem_filter.mpr ⟨hq0, hq0in⟩⟩
  obtain ⟨hxP, hxin⟩ := Finset.mem_filter.mp hxS
  obtain ⟨hxa, -, -⟩ := hxin.ne
  have hsum := orient_sum a b c x
  have hcyc : orient b c a = orient a b c := (orient_cyc a b c).symm
  have hℓx : 0 < lev b c a x := by unfold lev; rw [hcyc]; linarith [hxin.1, hxin.2.1, hxin.2.2]
  have hℓxD : lev b c a x < orient a b c := by unfold lev; rw [hcyc]; linarith [hxin.2.1]
  have hax : s(a, x) ∈ T := by
    by_contra hn
    obtain ⟨g, hg, hcr⟩ := hT.2.2 _ (mk_mem_segs.mpr ⟨ha, hxP, Ne.symm hxa⟩) hn
    induction g using Sym2.ind with
    | _ d e =>
    rw [cross_mk] at hcr
    obtain ⟨τ, σ, hτ0, hτ1, hσ0, hσ1, ez⟩ := hcr.meet
    have h1 := hcr.1
    have hda : d ≠ a := by rintro rfl; rw [orient_self13, zero_mul] at h1; exact lt_irrefl _ h1
    have hea : e ≠ a := by rintro rfl; rw [orient_self13, mul_zero] at h1; exact lt_irrefl _ h1
    have hgP := mk_mem_segs.mp (hT.1 hg)
    have hℓz : lev b c a (lerp a x τ) = τ * lev b c a x := by rw [lev_lerp, lev_self]; ring
    set κ := (τ + 1) / 2 * lev b c a x / orient a b c with hκ
    have hκ0 : 0 < κ := div_pos (by nlinarith) hD
    have hκD : κ * orient a b c = (τ + 1) / 2 * lev b c a x := div_mul_cancel₀ _ hD.ne'
    have hκ1 : κ < 1 := by rw [hκ, div_lt_one hD]; nlinarith
    have hzin : InTri a (lerp a b κ) (lerp a c κ) (lerp a x τ) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [orient_shrink1, orient_lerp]; simp only [orient_self13, mul_zero, zero_add]
        exact mul_pos hκ0 (mul_pos hτ0 hxin.1)
      · rw [orient_shrink3, hℓz, hκD]; exact mul_pos hκ0 (by nlinarith)
      · rw [orient_shrink2, orient_lerp]; simp only [orient_self23, mul_zero, zero_add]
        exact mul_pos hκ0 (mul_pos hτ0 hxin.2.2)
    have hmin : ∀ r ∈ P, InTri a b c r → κ * orient a b c ≤ lev b c a r := by
      intro r hr hrin
      have := hxmin r (Finset.mem_filter.mpr ⟨hr, hrin⟩)
      rw [hκD]; nlinarith
    have hz : lev b c a (lerp a x τ) = (1 - σ) * lev b c a d + σ * lev b c a e := by
      rw [ez, lev_lerp]
    have hzℓ : lev b c a (lerp a x τ) < κ * orient a b c := by rw [hℓz, hκD]; nlinarith
    by_cases he : lev b c a e < κ * orient a b c
    · exact consec_empty_aux hP hT.nonCross ha hb hc hD hab hac hκ0 hκ1 hmin hgP.2.1 hgP.1
        hea hda (Ne.symm hgP.2.2) hg hσ0 hσ1 ez hzin he
    · have hd : lev b c a d < κ * orient a b c := by nlinarith
      exact consec_empty_aux hP hT.nonCross ha hb hc hD hab hac hκ0 hκ1 hmin hgP.1 hgP.2.1
        hda hea hgP.2.2 (by rw [Sym2.eq_swap]; exact hg) (μ := 1 - σ) (by linarith)
        (by linarith) (by rw [ez, ← lerp_symm]) hzin hd
  exact hW x hxP hax hxin.1 (by rw [orient_cyc, orient_cyc]; exact hxin.2.2)

/-- The crossing argument for the third side in `consec`. -/
lemma consec_side_aux {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    (hTnc : NonCross T) {a b c q q' : K × K} (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P)
    (hD : 0 < orient a b c) (hab : s(a, b) ∈ T) (hac : s(a, c) ∈ T)
    (hW : ∀ y ∈ P, s(a, y) ∈ T → 0 < orient a b y → 0 < orient a y c → False)
    (hempty : ∀ r ∈ P, ¬ InTri a b c r) (hq : q ∈ P) (hq' : q' ∈ P) (hqq : q ≠ q')
    (hqb : q ≠ b) (hqc : q ≠ c) (hq'b : q' ≠ b) (hq'c : q' ≠ c) (hgT : s(q', q) ∈ T)
    (hpos : 0 < orient b c q) (hneg : orient b c q' < 0) {σ μ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hw : lerp b c σ = lerp q' q μ) : False := by
  have hab' : a ≠ b := by rintro rfl; simp at hD
  have hac' : a ≠ c := by rintro rfl; simp at hD
  have hbca : orient b c a = orient a b c := (orient_cyc a b c).symm
  have hq'a : q' ≠ a := by rintro rfl; rw [hbca] at hneg; linarith
  by_cases hqa : q = a
  · subst hqa
    have hwa : lerp b c σ = lerp q q' (1 - μ) := by rw [hw, ← lerp_symm]
    have o1 : orient q b (lerp b c σ) = σ * orient q b c := by rw [orient_lerp]; simp
    have o1' : orient q b (lerp b c σ) = (1 - μ) * orient q b q' := by
      rw [hwa, orient_lerp]; simp
    have o2 : orient q (lerp b c σ) c = (1 - σ) * orient q b c := by rw [orient_lerp_mid]; simp
    have o2' : orient q (lerp b c σ) c = (1 - μ) * orient q q' c := by
      rw [hwa, orient_lerp_mid]; simp
    exact hW q' hq' (by rw [Sym2.eq_swap]; exact hgT)
      (by nlinarith [mul_pos hσ0 hD]) (by nlinarith [mul_pos (sub_pos.mpr hσ1) hD])
  obtain ⟨t0, ht00, ht01, hzin⟩ :=
    near_side (u := b) (v := c) (o := a) (by rw [hbca]; exact hD) hσ0 hσ1 hpos
  have hzin' : InTri a b c (lerp (lerp b c σ) q t0) := hzin.rot.rot
  have hout : orient a b q < 0 ∨ orient b c q < 0 ∨ orient c a q < 0 := by
    have n1 : orient a b q ≠ 0 := hP a ha b hb q hq hab' (Ne.symm hqa) (Ne.symm hqb)
    have n3 : orient c a q ≠ 0 := hP c hc a ha q hq (Ne.symm hac') (Ne.symm hqc) (Ne.symm hqa)
    by_contra hn; push Not at hn
    exact hempty q hq ⟨lt_of_le_of_ne hn.1 (Ne.symm n1), hpos, lt_of_le_of_ne hn.2.2 (Ne.symm n3)⟩
  obtain ⟨t, ht0, ht1, hcase⟩ := exit' hzin' hout
  have hν1 := (lerp_sub_mem hμ0 hμ1 ht00 ht01).2
  have hν := (lerp_sub_mem hν1.1 hν1.2 ht0 ht1).2
  have hmeq : lerp (lerp (lerp b c σ) q t0) q t =
      lerp q' q ((μ + t0 - μ * t0) + t - (μ + t0 - μ * t0) * t) := by
    rw [hw, lerp_lerp, lerp_lerp]; congr 1; ring
  have novert : ∀ v ∈ P, v ≠ q → v ≠ q' → lerp (lerp (lerp b c σ) q t0) q t = v → False := by
    intro v hv hvq hvq' hm
    have : orient q' q v = 0 := by rw [← hm, hmeq, orient_lerp_self]
    rcases hP.on_line hq' hq hv (Ne.symm hqq) this with h | h
    exacts [hvq' h, hvq h]
  have cross_with : ∀ u ∈ P, ∀ v ∈ P, s(u, v) ∈ T → u ≠ v → u ≠ q → u ≠ q' →
      ∀ ρ : K, 0 < ρ → ρ < 1 → lerp (lerp (lerp b c σ) q t0) q t = lerp u v ρ → False := by
    intro u hu v hv huvT huv huq huq' ρ hρ0 hρ1 hm
    have := cross_of_common hP hu hv hq' hq huv (Ne.symm hqq)
      (ne_pair_of_not_mem v huq huq') hρ0 hρ1 hν.1.le hν.2.le (hm.symm.trans hmeq)
    exact hTnc _ huvT _ hgT (cross_mk.mpr this)
  rcases hcase with hv | ⟨u, v, o, hrot, h0, hp1, hp2⟩
  · rcases hv with hv | hv | hv
    · exact novert a ha (Ne.symm hqa) (Ne.symm hq'a) hv
    · exact novert b hb (Ne.symm hqb) (Ne.symm hq'b) hv
    · exact novert c hc (Ne.symm hqc) (Ne.symm hq'c) hv
  · rcases hrot with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨ρ, hρ0, hρ1, hm⟩ := on_side h0 hp1 hp2
      exact cross_with u ha v hb hab hab' (Ne.symm hqa) (Ne.symm hq'a) ρ hρ0 hρ1 hm
    · have : 0 < orient u v (lerp (lerp (lerp u v σ) q t0) q t) := by
        rw [orient_lerp]; nlinarith [hzin'.2.1]
      linarith
    · obtain ⟨ρ, hρ0, hρ1, hm⟩ := on_side h0 hp1 hp2
      exact cross_with v ha u hc hac hac' (Ne.symm hqa) (Ne.symm hq'a) (1 - ρ) (by linarith)
        (by linarith) (by rw [hm, ← lerp_symm])

/-- **Consecutive edges bound a face.** -/
theorem consec {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    (hT : IsTri P T) {a b c : K × K} (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P)
    (hD : 0 < orient a b c) (hab : s(a, b) ∈ T) (hac : s(a, c) ∈ T)
    (hW : ∀ y ∈ P, s(a, y) ∈ T → 0 < orient a b y → 0 < orient a y c → False) :
    Face P T a b c := by
  have hempty := consec_empty hP hT ha hb hc hD hab hac hW
  have hbc' : b ≠ c := by rintro rfl; simp at hD
  have hbcT : s(b, c) ∈ T := by
    by_contra hn
    obtain ⟨g, hg, hcr⟩ := hT.2.2 _ (mk_mem_segs.mpr ⟨hb, hc, hbc'⟩) hn
    induction g using Sym2.ind with
    | _ d e =>
    rw [cross_mk] at hcr
    obtain ⟨σ, τ, hσ0, hσ1, hτ0, hτ1, ew⟩ := hcr.meet
    have hgP := mk_mem_segs.mp (hT.1 hg)
    have h1 := hcr.1
    have hdb : d ≠ b ∧ d ≠ c := by
      constructor <;> rintro rfl
      · rw [orient_self13, zero_mul] at h1; exact lt_irrefl _ h1
      · rw [orient_self23, zero_mul] at h1; exact lt_irrefl _ h1
    have heb : e ≠ b ∧ e ≠ c := by
      constructor <;> rintro rfl
      · rw [orient_self13, mul_zero] at h1; exact lt_irrefl _ h1
      · rw [orient_self23, mul_zero] at h1; exact lt_irrefl _ h1
    rcases lt_or_gt_of_ne (show orient b c d ≠ 0 from fun h0 => by
        rw [h0, zero_mul] at h1; exact lt_irrefl _ h1) with h | h
    · exact consec_side_aux hP hT.nonCross ha hb hc hD hab hac hW hempty hgP.2.1 hgP.1
        (Ne.symm hgP.2.2) heb.1 heb.2 hdb.1 hdb.2 hg (by nlinarith) h hσ0 hσ1 hτ0 hτ1 ew
    · exact consec_side_aux hP hT.nonCross ha hb hc hD hab hac hW hempty hgP.1 hgP.2.1
        hgP.2.2 hdb.1 hdb.2 heb.1 heb.2 (by rw [Sym2.eq_swap]; exact hg) h (by nlinarith)
        hσ0 hσ1 (μ := 1 - τ) (by linarith) (by linarith) (by rw [ew, ← lerp_symm])
  exact ⟨ha, hb, hc, hD, hab, hbcT, by rw [Sym2.eq_swap]; exact hac, hempty⟩

end TwoTri
