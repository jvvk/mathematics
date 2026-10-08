import LeanProofs.TwoTri.Consec

/-!
# The fan lemma

Every open half-plane at a point `v` of `P` that contains a point of `P` contains an edge of a
triangulation from `v`.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The core of the fan lemma: the angularly first point `y` in the triangle `v w p` cut off by
the first edge `q₀ p` hit along `v → x₀` is joined to `v`. -/
lemma fan_core {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))}
    (hT : IsTri P T) {v x₀ p q₀ y : K × K} (hv : v ∈ P) (hx₀ : x₀ ∈ P) (hp : p ∈ P)
    (hq₀ : q₀ ∈ P) (hy : y ∈ P) {τ μ : K} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hμ0 : 0 < μ)
    (hμ1 : μ < 1) (hw : lerp v x₀ τ = lerp q₀ p μ) (hg₀ : s(q₀, p) ∈ T)
    (hfirst : ∀ q' ∈ P, ∀ q ∈ P, s(q', q) ∈ T → ∀ t ν : K, 0 < t → t < τ → 0 ≤ ν → ν ≤ 1 →
      lerp v x₀ t = lerp q' q ν → False)
    (hp_pos : 0 < orient v x₀ p) (hq₀_neg : orient v x₀ q₀ < 0)
    (hyC : y = p ∨ InTri v (lerp v x₀ τ) p y)
    (hymin : ∀ y' ∈ P, (y' = p ∨ InTri v (lerp v x₀ τ) p y') → 0 ≤ orient v y y') :
    s(v, y) ∈ T := by
  set w := lerp v x₀ τ with hwdef
  have hTnc := hT.2.1
  have hvwp : 0 < orient v w p := by rw [hwdef, orient_shrink1]; exact mul_pos hτ0 hp_pos
  have hpv : p ≠ v := by rintro rfl; simp at hp_pos
  have hpx : p ≠ x₀ := by rintro rfl; simp at hp_pos
  have hq₀v : q₀ ≠ v := by rintro rfl; simp at hq₀_neg
  have hq₀x : q₀ ≠ x₀ := by rintro rfl; simp at hq₀_neg
  have hq₀p : q₀ ≠ p := by rintro rfl; linarith
  have hvx : v ≠ x₀ := by rintro rfl; simp at hp_pos
  have hyv : y ≠ v := by
    rcases hyC with rfl | h
    · exact hpv
    · exact h.ne.1
  have hvwy : 0 < orient v w y := by
    rcases hyC with rfl | h
    · exact hvwp
    · exact h.1
  have hvyp : 0 ≤ orient v y p := hymin p hp (Or.inl rfl)
  by_contra hn
  obtain ⟨g, hg, hcr⟩ := hT.2.2 _ (mk_mem_segs.mpr ⟨hv, hy, Ne.symm hyv⟩) hn
  induction g using Sym2.ind with
  | _ d e =>
  rw [cross_mk] at hcr
  obtain ⟨s₁, s₂, hs₁0, hs₁1, hs₂0, hs₂1, ez⟩ := hcr.meet
  have hgP := mk_mem_segs.mp (hT.1 hg)
  have h1 := hcr.1
  have hd0 : orient v y d ≠ 0 := fun h0 => by rw [h0, zero_mul] at h1; exact lt_irrefl _ h1
  have he0 : orient v y e ≠ 0 := fun h0 => by rw [h0, mul_zero] at h1; exact lt_irrefl _ h1
  -- the endpoint `q` on the side of `w`
  have hwpv : 0 < orient q₀ p v := by
    have := orient_lerp_fst q₀ p p v μ
    rw [← hw, orient_self12, mul_zero, add_zero] at this
    have h2 : orient w p v = orient v w p := (orient_cyc v w p).symm
    nlinarith
  have hwpx : orient w p x₀ < 0 := by
    rw [hwdef, orient_lerp_fst, orient_self13, mul_zero, add_zero, orient_swap23]
    nlinarith
  have main : ∀ q q' : K × K, q ∈ P → q' ∈ P → q ≠ q' → s(q', q) ∈ T → orient v y q < 0 →
      orient v y q' ≠ 0 → orient q' q v * orient q' q y < 0 → ∀ ν : K, 0 < ν → ν < 1 →
      lerp v y s₁ = lerp q' q ν → False := by
    intro q q' hq hq' hqq hgT hqneg hq'0 hsep ν hν0 hν1 hz
    have hqv : q ≠ v := by rintro rfl; simp at hqneg
    have hq'v : q' ≠ v := by rintro rfl; simp at hq'0
    have hqp : q ≠ p := by rintro rfl; linarith
    -- a starting point inside the triangle `v w p`, strictly on the `w` side of `vy`
    have start : ∃ t₀ : K, 0 < t₀ ∧ t₀ < 1 ∧ InTri v w p (lerp (lerp v y s₁) q t₀) := by
      rcases hyC with rfl | hyin
      · have hq2 : 0 < orient y v q := by
          rw [orient_cyc, orient_swap23]; linarith
        obtain ⟨t₀, h0, h1, hin⟩ :=
          near_side (u := y) (v := v) (o := w) (by rw [orient_cyc]; exact hvwp)
            (σ := 1 - s₁) (by linarith) (by linarith) hq2
        rw [lerp_symm] at hin
        exact ⟨t₀, h0, h1, hin.rot⟩
      · have hz : InTri v w p (lerp v y s₁) := by
          rw [← lerp_symm]; exact hyin.lerp_vertex (Or.inl rfl) (by linarith) (by linarith)
        obtain ⟨t₀, ht₀, hc, -⟩ := exists_small (Finset.univ : Finset (Fin 4)) (∅ : Finset Unit)
          ![orient v w (lerp v y s₁), orient w p (lerp v y s₁), orient p v (lerp v y s₁), 1]
          ![orient v w q - orient v w (lerp v y s₁), orient w p q - orient w p (lerp v y s₁),
            orient p v q - orient p v (lerp v y s₁), -1] (fun _ => (1 : K)) (fun _ => 0)
          (by intro i _; fin_cases i
              exacts [hz.1, hz.2.1, hz.2.2, one_pos]) (by simp)
        have c0 := hc 0 (by simp); have c1 := hc 1 (by simp)
        have c2 := hc 2 (by simp); have c3 := hc 3 (by simp)
        simp at c0 c1 c2 c3
        refine ⟨t₀, ht₀, by linarith, ?_, ?_, ?_⟩ <;> rw [orient_lerp] <;> linarith
    obtain ⟨t₀, ht₀0, ht₀1, hzin⟩ := start
    have hz'neg : orient v y (lerp (lerp v y s₁) q t₀) < 0 := by
      rw [orient_lerp, orient_lerp_self]; nlinarith
    -- `q` is strictly beyond some side of `v w p`
    have hout : orient v w q < 0 ∨ orient w p q < 0 ∨ orient p v q < 0 := by
      by_contra hn; push Not at hn
      obtain ⟨n1, n2, n3⟩ := hn
      have hqx : q ≠ x₀ := by
        rintro rfl; linarith
      have m1 : orient v w q ≠ 0 := by
        rw [hwdef, orient_shrink1]
        exact mul_ne_zero hτ0.ne' (hP v hv x₀ hx₀ q hq hvx (Ne.symm hqv) (Ne.symm hqx))
      have m3 : orient p v q ≠ 0 := hP p hp v hv q hq hpv (Ne.symm hqp) (Ne.symm hqv)
      have m2 : orient w p q ≠ 0 := by
        intro h0
        have hl : orient q₀ p q = 0 := by
          have := orient_lerp_fst q₀ p p q μ
          rw [← hw, h0, orient_self12, mul_zero, add_zero] at this
          rcases mul_eq_zero.mp this.symm with h | h
          · linarith
          · exact h
        rcases hP.on_line hq₀ hp hq hq₀p hl with h | h
        · subst h
          have : orient v w q < 0 := by
            rw [hwdef, orient_shrink1]; exact mul_neg_of_pos_of_neg hτ0 hq₀_neg
          linarith
        · exact hqp h
      have hqC : InTri v w p q := ⟨lt_of_le_of_ne n1 (Ne.symm m1), lt_of_le_of_ne n2 (Ne.symm m2),
        lt_of_le_of_ne n3 (Ne.symm m3)⟩
      have := hymin q hq (Or.inr hqC)
      linarith
    obtain ⟨t, ht0, ht1, hcase⟩ := exit' hzin hout
    have hν1 := (lerp_sub_mem hν0 hν1 ht₀0 ht₀1).2
    have hν2 := (lerp_sub_mem hν1.1 hν1.2 ht0 ht1).2
    set m := lerp (lerp (lerp v y s₁) q t₀) q t with hmdef
    have hmeq : m = lerp q' q ((ν + t₀ - ν * t₀) + t - (ν + t₀ - ν * t₀) * t) := by
      rw [hmdef, hz, lerp_lerp, lerp_lerp]; congr 1; ring
    have hmneg : orient v y m < 0 := by rw [hmdef, orient_lerp]; nlinarith
    have hgne : s(q₀, p) ≠ s(q', q) := by
      intro e'
      rcases Sym2.eq_iff.mp e' with ⟨-, h2⟩ | ⟨h1, h2⟩
      · exact hqp h2.symm
      · rw [← h1, ← h2, orient_swap12 q₀ p v, orient_swap12 q₀ p y] at hsep
        rcases hyC with hyp | hyin
        · rw [hyp, orient_self23] at hsep; simp at hsep
        · have hpy : 0 < orient q₀ p y := by
            have := orient_lerp_fst q₀ p p y μ
            rw [← hw, orient_self12, mul_zero, add_zero] at this
            nlinarith [hyin.2.1]
          nlinarith
    have cross_with : ∀ a ∈ P, ∀ b ∈ P, s(a, b) ∈ T → a ≠ b → s(a, b) ≠ s(q', q) →
        ∀ ρ : K, 0 < ρ → ρ < 1 → m = lerp a b ρ → False := by
      intro a ha b hb habT hab hne ρ hρ0 hρ1 hm
      have := cross_of_common hP ha hb hq' hq hab (Ne.symm hqq) hne hρ0 hρ1 hν2.1.le hν2.2.le
        (hm.symm.trans hmeq)
      exact hTnc _ habT _ hgT (cross_mk.mpr this)
    rcases hcase with hvx' | ⟨u, u', o, hrot, h0, hp1, hp2⟩
    · rcases hvx' with hm | hm | hm
      · have : orient q' q v = 0 := by rw [← hm, hmeq, orient_lerp_self]
        rcases hP.on_line hq' hq hv (Ne.symm hqq) this with h | h
        exacts [hq'v h.symm, hqv h.symm]
      · exact cross_with q₀ hq₀ p hp hg₀ hq₀p hgne μ hμ0 hμ1 (hm.trans hw)
      · rw [hm] at hmneg; linarith
    · rcases hrot with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> rw [e1, e2] at h0 <;>
        rw [e2, e3] at hp1 <;> rw [e3, e1] at hp2
      · obtain ⟨ρ, hρ0, hρ1, hm⟩ := on_side h0 hp1 hp2
        rw [hwdef, lerp_lerp_left] at hm
        exact hfirst q' hq' q hq hgT (τ * ρ) _ (mul_pos hτ0 hρ0) (by nlinarith) hν2.1.le
          hν2.2.le (hm.symm.trans hmeq)
      · obtain ⟨ρ, hρ0, hρ1, hm⟩ := on_side h0 hp1 hp2
        rw [hw, lerp_lerp] at hm
        have := (lerp_sub_mem hμ0 hμ1 hρ0 hρ1).2
        exact cross_with q₀ hq₀ p hp hg₀ hq₀p hgne _ this.1 this.2 hm
      · obtain ⟨ρ, hρ0, hρ1, hm⟩ := on_side h0 hp1 hp2
        have : orient v y m = (1 - ρ) * orient v y p := by
          rw [hm, orient_lerp]; simp
        nlinarith
  rcases lt_or_gt_of_ne hd0 with h | h
  · exact main d e hgP.1 hgP.2.1 hgP.2.2 (by rw [Sym2.eq_swap]; exact hg) h he0
      (by rw [orient_swap12 d e v, orient_swap12 d e y]; nlinarith [hcr.2]) (1 - s₂)
      (by linarith) (by linarith) (by rw [ez, ← lerp_symm])
  · have : orient v y e < 0 := by nlinarith
    exact main e d hgP.2.1 hgP.1 (Ne.symm hgP.2.2) hg this hd0 hcr.2 s₂ hs₂0 hs₂1 ez

lemma div_sub_neg (A B : K) : A / (A - B) = -A / (-A - -B) := by
  rw [show -A - -B = -(A - B) by ring, neg_div_neg_eq]

/-- Where a segment crosses the line `v x`, as a parameter along `v → x`. -/
def crossP (v x : K × K) : Sym2 (K × K) → K :=
  Sym2.lift ⟨fun d e => orient d e v / (orient d e v - orient d e x), fun d e => by
    simp only; rw [orient_swap12 d e v, orient_swap12 d e x]; exact div_sub_neg _ _⟩

lemma dotd_neg (d u r : K × K) : dotd (-d) u r = -dotd d u r := by simp [dotd]; ring

@[simp] lemma dotd_self (d u : K × K) : dotd d u u = 0 := by simp [dotd]

/-- **The fan lemma.** -/
theorem fan {P : Finset (K × K)} (hP : GenPos P) {T : Finset (Sym2 (K × K))} (hT : IsTri P T)
    {v : K × K} (hv : v ∈ P) (d : K × K) (hex : ∃ x ∈ P, dotd d v x < 0) :
    ∃ w ∈ P, s(v, w) ∈ T ∧ dotd d v w < 0 := by
  classical
  obtain ⟨x₁, hx₁, hx₁neg⟩ := hex
  set Hm := P.filter (fun r => dotd d v r < 0)
  obtain ⟨x₀, hx₀H, hx₀min⟩ := ang_min (S := Hm) (u := v) (-d)
    ⟨x₁, Finset.mem_filter.mpr ⟨hx₁, hx₁neg⟩⟩
    (fun r hr => by rw [dotd_neg]; linarith [(Finset.mem_filter.mp hr).2])
  obtain ⟨hx₀, hx₀neg⟩ := Finset.mem_filter.mp hx₀H
  by_contra H
  push Not at H
  have hvx : v ≠ x₀ := by rintro rfl; simp at hx₀neg
  have hn : s(v, x₀) ∉ T := fun h => by have := H x₀ hx₀ h; linarith
  set B := T.filter (fun g => Cross s(v, x₀) g)
  have hBne : B.Nonempty := by
    obtain ⟨g, hg, hc⟩ := hT.2.2 _ (mk_mem_segs.mpr ⟨hv, hx₀, hvx⟩) hn
    exact ⟨g, Finset.mem_filter.mpr ⟨hg, hc⟩⟩
  obtain ⟨g₀, hg₀B, hg₀min⟩ := B.exists_min_image (crossP v x₀) hBne
  obtain ⟨hg₀T, hg₀c⟩ := Finset.mem_filter.mp hg₀B
  induction g₀ using Sym2.ind with
  | _ a₁ a₂ =>
  rw [cross_mk] at hg₀c
  have hgP := mk_mem_segs.mp (hT.1 hg₀T)
  obtain ⟨τ, σ, hτ0, hτ1, hσ0, hσ1, ew⟩ := hg₀c.meet
  have hden : ∀ q' q : K × K, SCross v x₀ q' q → orient q' q v - orient q' q x₀ ≠ 0 := by
    intro q' q h e0
    have h2 := h.2
    have : orient q' q v = orient q' q x₀ := by linarith
    rw [this] at h2; nlinarith [mul_self_nonneg (orient q' q x₀)]
  have hτp : τ = crossP v x₀ s(a₁, a₂) := by
    simp only [crossP, Sym2.lift_mk]
    exact param_eq (by rw [ew, orient_lerp_self]) (hden _ _ hg₀c)
  have hfirst : ∀ q' ∈ P, ∀ q ∈ P, s(q', q) ∈ T → ∀ t ν : K, 0 < t → t < τ → 0 ≤ ν → ν ≤ 1 →
      lerp v x₀ t = lerp q' q ν → False := by
    intro q' hq' q hq hgT t ν ht0 htτ hν0 hν1 e'
    have hqq := (mk_mem_segs.mp (hT.1 hgT)).2.2
    have hne : s(v, x₀) ≠ s(q', q) := fun h => hn (h ▸ hgT)
    have hx := cross_of_common hP hv hx₀ hq' hq hvx hqq hne ht0 (by linarith) hν0 hν1 e'
    have hmem : s(q', q) ∈ B := Finset.mem_filter.mpr ⟨hgT, cross_mk.mpr hx⟩
    have h1 := hg₀min _ hmem
    have h2 : t = crossP v x₀ s(q', q) := by
      simp only [crossP, Sym2.lift_mk]
      exact param_eq (by rw [e', orient_lerp_self]) (hden _ _ hx)
    rw [← hτp, ← h2] at h1; linarith
  have hw_neg : dotd d v (lerp v x₀ τ) < 0 := by
    rw [dotd_lerp, dotd_self]; nlinarith
  have hsep := hg₀c.1
  have n1 : orient v x₀ a₁ ≠ 0 := fun h0 => by rw [h0, zero_mul] at hsep; exact lt_irrefl _ hsep
  have n2 : orient v x₀ a₂ ≠ 0 := fun h0 => by rw [h0, mul_zero] at hsep; exact lt_irrefl _ hsep
  -- finish from an endpoint `p` below the line, the other endpoint `q₀`
  have finish : ∀ p q₀ : K × K, p ∈ P → q₀ ∈ P → s(q₀, p) ∈ T → dotd d v p < 0 →
      0 < orient v x₀ p → orient v x₀ q₀ < 0 → ∀ μ : K, 0 < μ → μ < 1 →
      lerp v x₀ τ = lerp q₀ p μ → False := by
    intro p q₀ hp hq₀ hgT hpneg hppos hq₀neg μ hμ0 hμ1 hw
    set w := lerp v x₀ τ with hwdef
    have hvwp : 0 < orient v w p := by rw [hwdef, orient_shrink1]; exact mul_pos hτ0 hppos
    set C := P.filter (fun y => y = p ∨ InTri v w p y)
    obtain ⟨y, hyC, hymin⟩ := ang_min (S := C) (u := v) (-(w.2 - v.2), w.1 - v.1)
      ⟨p, Finset.mem_filter.mpr ⟨hp, Or.inl rfl⟩⟩ (fun r hr => by
        rw [dotd_perp]
        rcases (Finset.mem_filter.mp hr).2 with rfl | h
        · exact hvwp
        · exact h.1)
    obtain ⟨hy, hyC'⟩ := Finset.mem_filter.mp hyC
    have hT' := fan_core hP hT hv hx₀ hp hq₀ hy hτ0 hτ1 hμ0 hμ1 hw hgT hfirst hppos hq₀neg hyC'
      (fun y' hy' h => hymin y' (Finset.mem_filter.mpr ⟨hy', h⟩))
    have hyneg : dotd d v y < 0 := by
      rcases hyC' with rfl | hin
      · exact hpneg
      · have Bd := dotd_bary d v v w p y
        rw [dotd_self, mul_zero, zero_add] at Bd
        have : orient v w p * dotd d v y < 0 := by
          rw [Bd]; nlinarith [mul_neg_of_pos_of_neg hin.2.2 hw_neg,
            mul_neg_of_pos_of_neg hin.1 hpneg]
        exact neg_of_mul_neg_right this hvwp.le
    have := H y hy hT'
    linarith
  have hsplit : dotd d v a₁ < 0 ∨ dotd d v a₂ < 0 := by
    by_contra hc; push Not at hc
    have : dotd d v (lerp v x₀ τ) = (1 - σ) * dotd d v a₁ + σ * dotd d v a₂ := by
      rw [ew, dotd_lerp]
    nlinarith
  rcases hsplit with h | h
  · have hp : 0 < orient v x₀ a₁ :=
      lt_of_le_of_ne (hx₀min a₁ (Finset.mem_filter.mpr ⟨hgP.1, h⟩)) (Ne.symm n1)
    exact finish a₁ a₂ hgP.1 hgP.2.1 (by rw [Sym2.eq_swap]; exact hg₀T) h hp (by nlinarith)
      (1 - σ) (by linarith) (by linarith) (by rw [ew, ← lerp_symm])
  · have hp : 0 < orient v x₀ a₂ :=
      lt_of_le_of_ne (hx₀min a₂ (Finset.mem_filter.mpr ⟨hgP.2.1, h⟩)) (Ne.symm n2)
    exact finish a₂ a₁ hgP.2.1 hgP.1 hg₀T h hp (by nlinarith) σ hσ0 hσ1 ew

end TwoTri
