import LeanProofs.TwoTri.Lower

/-!
# Corollary 3

If `|P| ≥ 5`, two triangulations of `P` share at least five edges, and if they share exactly five
then the hull has five edges.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The unavoidable segments of `P`. -/
noncomputable def unav (P : Finset (K × K)) : Finset (Sym2 (K × K)) := by
  classical exact (segs P).filter (Unavoidable P)

lemma mem_unav {P : Finset (K × K)} {s : Sym2 (K × K)} :
    s ∈ unav P ↔ s ∈ segs P ∧ Unavoidable P s := by
  classical simp [unav]

lemma hull_sub_unav (P : Finset (K × K)) : hullEdges P ⊆ unav P := fun s hs =>
  mem_unav.mpr ⟨(Finset.mem_filter.mp hs).1, hull_unavoidable hs⟩

lemma unav_sub_inter {P : Finset (K × K)} {A B : Finset (Sym2 (K × K))} (hA : IsTri P A)
    (hB : IsTri P B) : unav P ⊆ A ∩ B := by
  intro s hs
  obtain ⟨h1, h2⟩ := mem_unav.mp hs
  exact Finset.mem_inter.mpr ⟨h2.mem hA h1, h2.mem hB h1⟩

lemma card_add_le {H E U : Finset (Sym2 (K × K))} (hH : H ⊆ U) (hE : E ⊆ U)
    (hd : ∀ e ∈ E, e ∉ H) : H.card + E.card ≤ U.card := by
  classical
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun a ha he => hd a he ha)]
  exact Finset.card_le_card (Finset.union_subset hH hE)

lemma third {P : Finset (K × K)} (h : 3 ≤ P.card) (a b : K × K) : ∃ c ∈ P, c ≠ a ∧ c ≠ b := by
  classical
  obtain ⟨c, hc, hn⟩ := exists_other (P := P) (k := 2) (by omega) {a, b} (Finset.card_le_two)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  exact ⟨c, hc, hn⟩

lemma hullPos_not_both' {P : Finset (K × K)} (h3 : 3 ≤ P.card) {a b : K × K}
    (h1 : HullPos P a b) (h2 : HullPos P b a) : False := by
  obtain ⟨c, hc, hca, hcb⟩ := third h3 a b
  exact hullPos_not_both hc hca hcb h1 h2

lemma s_ne {α : Type*} {a b c d : α} (h1 : a ≠ c ∨ b ≠ d) (h2 : a ≠ d ∨ b ≠ c) :
    s(a, b) ≠ s(c, d) := by
  intro e
  rcases Sym2.eq_iff.mp e with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rcases h1 with h | h <;> contradiction
  · rcases h2 with h | h <;> contradiction

lemma card_three {α : Type*} [DecidableEq α] {a b c : α} (h1 : a ≠ b) (h2 : a ≠ c)
    (h3 : b ≠ c) : ({a, b, c} : Finset α).card = 3 :=
  Finset.card_eq_three.mpr ⟨a, b, c, h1, h2, h3, rfl⟩

/-- Two unordered pairs differ, from inequalities in the context. -/
macro "sne" : tactic => `(tactic| (intro e; rcases Sym2.eq_iff.mp e with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
  (first
    | exact absurd e1 ‹_›
    | exact absurd e1.symm ‹_›
    | exact absurd e2 ‹_›
    | exact absurd e2.symm ‹_›)))

/-- An unavoidable segment from an ear. -/
lemma ear_mem {P : Finset (K × K)} (hP : GenPos P) {u a b q : K × K} (hu : u ∈ P) (ha : a ∈ P)
    (hb : b ∈ P) (hq : q ∈ P) (hin : InTri u a b q) (hun : Unavoidable P s(u, q)) :
    s(u, q) ∈ unav P ∧ s(u, q) ∉ hullEdges P :=
  ⟨mem_unav.mpr ⟨mk_mem_segs.mpr ⟨hu, hq, Ne.symm hin.ne.1⟩, hun⟩,
    not_hull_of_inTri hP hu ha hb hq hin⟩

/-- With a hull of at most four edges and a point off the hull (more points than hull edges),
at least six segments are unavoidable. -/
theorem six_unavoidable {P : Finset (K × K)} (hP : GenPos P) (h4 : 4 ≤ P.card)
    (hlt : (hullEdges P).card < P.card) (hH : (hullEdges P).card ≤ 4) : 6 ≤ (unav P).card := by
  classical
  have h3 : 3 ≤ P.card := by omega
  have hne : P.Nonempty := Finset.card_pos.mp (by omega)
  have h2 : ∀ w ∈ P, 2 ≤ (P.erase w).card := fun w hw => by
    rw [Finset.card_erase_of_mem hw]; omega
  obtain ⟨u, hu, hexu⟩ := exists_exposed hne
  obtain ⟨v, x, hv, hx, hvu, hxu, huv, hxu'⟩ := hexu.neighbours hP hu (h2 u hu)
  have hvx : v ≠ x := by rintro rfl; exact hullPos_not_both' h3 huv hxu'
  obtain ⟨v', -, hv', -, hv'v, -, hvv', -⟩ :=
    (huv.exposed (Ne.symm hvu)).2.neighbours hP hv (h2 v hv)
  obtain ⟨-, x', -, hx', -, hx'x, -, hx'x'⟩ :=
    (hxu'.exposed hxu).1.neighbours hP hx (h2 x hx)
  have hv'u : v' ≠ u := by rintro rfl; exact hullPos_not_both' h3 huv hvv'
  have hx'u : x' ≠ u := by rintro rfl; exact hullPos_not_both' h3 hxu' hx'x'
  have hH_uv := hullPos_mem hu hv (Ne.symm hvu) huv
  have hH_xu := hullPos_mem hx hu hxu hxu'
  have hH_vv' := hullPos_mem hv hv' (Ne.symm hv'v) hvv'
  have hH_x'x := hullPos_mem hx' hx hx'x hx'x'
  have HU := hull_sub_unav P
  by_cases hT : v' = x
  · -- triangular hull `u v x`
    subst hT
    obtain ⟨i, hi, hin'⟩ := exists_other (P := P) (k := 3) (by omega) {u, v, v'} Finset.card_le_three
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hin'
    obtain ⟨hiu, hiv, hix⟩ := hin'
    have hin : InTri u v v' i := ⟨huv i hi hiu hiv, hvv' i hi hiv hix, hxu' i hi hix hiu⟩
    obtain ⟨q1, hq1, t1, n1⟩ := ear hv' hi huv hxu' hvu hxu hvx hin
    obtain ⟨q2, hq2, t2, n2⟩ := ear hu hi hvv' huv hv'v (Ne.symm hvu) hxu hin.rot
    obtain ⟨q3, hq3, t3, n3⟩ := ear hv hi hxu' hvv' (Ne.symm hxu) hvx (Ne.symm hvu) hin.rot.rot
    obtain ⟨m1, k1⟩ := ear_mem hP hu hv hv' hq1 t1 n1
    obtain ⟨m2, k2⟩ := ear_mem hP hv hv' hu hq2 t2 n2
    obtain ⟨m3, k3⟩ := ear_mem hP hv' hu hv hq3 t3 n3
    have c3 : ({s(u, v), s(v, v'), s(v', u)} : Finset _).card = 3 :=
      card_three (by sne) (by sne) (by sne)
    have hH3 : 3 ≤ (hullEdges P).card := by
      rw [← c3]; apply Finset.card_le_card
      intro e he; simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> assumption
    obtain ⟨-, -, a2⟩ := t2.ne
    obtain ⟨-, a3, b3⟩ := t3.ne
    have cE : ({s(u, q1), s(v, q2), s(v', q3)} : Finset _).card = 3 :=
      card_three (by sne) (by sne) (by sne)
    have := card_add_le (U := unav P) HU (E := {s(u, q1), s(v, q2), s(v', q3)})
      (by intro e he; simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl | rfl <;> assumption)
      (by intro e he; simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl | rfl <;> assumption)
    omega
  · -- quadrilateral hull `u v v' x`
    have hx'v : x' ≠ v := by
      rintro rfl
      have e1 := hx'x' v' hv' hv'v hT
      have e2 := hvv' x hx (Ne.symm hvx) (Ne.symm hT)
      rw [orient_swap23] at e2; linarith
    have hx'x'' : x' ≠ x := hx'x
    have c4 : ({s(u, v), s(x, u), s(v, v'), s(x', x)} : Finset _).card = 4 := by
      rw [Finset.card_insert_of_notMem, card_three]
      · sne
      · sne
      · sne
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨by sne, by sne, by sne⟩
    have hsub : ({s(u, v), s(x, u), s(v, v'), s(x', x)} : Finset _) ⊆ hullEdges P := by
      intro e he; simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;> assumption
    have hHeq := Finset.eq_of_subset_of_card_le hsub (by rw [c4]; exact hH)
    -- the left neighbour of `v'` closes the cycle: `v' = x'`
    obtain ⟨v'', -, hv'', -, hv''v', -, hv'v'', -⟩ :=
      (hvv'.exposed (Ne.symm hv'v)).2.neighbours hP hv' (h2 v' hv')
    have hmem := hullPos_mem hv' hv'' (Ne.symm hv''v') hv'v''
    rw [← hHeq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hEq : v' = x' := by
      rcases hmem with e | e | e | e <;> rcases Sym2.eq_iff.mp e with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact absurd e1 hv'u
      · exact absurd e1 hv'v
      · exact absurd e1 hT
      · exact absurd e1 hv'u
      · exact absurd e1 hv'v
      · subst e2; exact (hullPos_not_both' h3 hvv' hv'v'').elim
      · exact e1
      · exact absurd e1 hT
    subst hEq
    have hc4 : (hullEdges P).card = 4 := by rw [← hHeq, c4]
    obtain ⟨i, hi, hin'⟩ := exists_other (P := P) (k := 4) (by omega) {u, v, v', x}
      Finset.card_le_four
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hin'
    obtain ⟨hiu, hiv, hiv', hix⟩ := hin'
    -- one extra unavoidable segment at `u` or `v'`, through the diagonal `vx`
    have extraA : ∃ a q, (a = u ∨ a = v') ∧ s(a, q) ∈ unav P ∧ s(a, q) ∉ hullEdges P := by
      rcases lt_or_gt_of_ne (hP v hv x hx i hi hvx (Ne.symm hiv) (Ne.symm hix)) with h | h
      · have hin : InTri v' x v i := ⟨hx'x' i hi hiv' hix, by rw [orient_swap12]; linarith,
          hvv' i hi hiv hiv'⟩
        obtain ⟨q, hq, t, n⟩ := ear hv hi hx'x' hvv' (Ne.symm hx'x) (Ne.symm hv'v) hvx.symm hin
        exact ⟨v', q, Or.inr rfl, ear_mem hP hv' hx hv hq t n⟩
      · have hin : InTri u v x i := ⟨huv i hi hiu hiv, h, hxu' i hi hix hiu⟩
        obtain ⟨q, hq, t, n⟩ := ear hx hi huv hxu' hvu hxu hvx hin
        exact ⟨u, q, Or.inl rfl, ear_mem hP hu hv hx hq t n⟩
    -- one at `v` or `x`, through the diagonal `u v'`, ending away from `u` and `v'`
    have extraB : ∃ b q, (b = v ∨ b = x) ∧ q ≠ u ∧ q ≠ v' ∧ s(b, q) ∈ unav P ∧
        s(b, q) ∉ hullEdges P := by
      rcases lt_or_gt_of_ne (hP u hu v' hv' i hi (Ne.symm hv'u) (Ne.symm hiu) (Ne.symm hiv'))
        with h | h
      · have hin : InTri v v' u i := ⟨hvv' i hi hiv hiv', by rw [orient_swap12]; linarith,
          huv i hi hiu hiv⟩
        obtain ⟨q, hq, t, n⟩ := ear hu hi hvv' huv hv'v (Ne.symm hvu) hv'u hin
        exact ⟨v, q, Or.inl rfl, t.ne.2.2, t.ne.2.1, ear_mem hP hv hv' hu hq t n⟩
      · have hin : InTri x u v' i := ⟨hxu' i hi hix hiu, h, hx'x' i hi hiv' hix⟩
        obtain ⟨q, hq, t, n⟩ := ear hv' hi hxu' hx'x' (Ne.symm hxu) hx'x hv'u.symm hin
        exact ⟨x, q, Or.inr rfl, t.ne.2.1, t.ne.2.2, ear_mem hP hx hu hv' hq t n⟩
    obtain ⟨a, qa, ha, ma, ka⟩ := extraA
    obtain ⟨b, qb, hb, hqbu, hqbv', mb, kb⟩ := extraB
    have hab : a ≠ b := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      exacts [Ne.symm hvu, Ne.symm hxu, hv'v, hT]
    have haqb : a ≠ qb := by rcases ha with rfl | rfl <;> [exact Ne.symm hqbu; exact Ne.symm hqbv']
    have cE : ({s(a, qa), s(b, qb)} : Finset _).card = 2 := Finset.card_pair (by sne)
    have := card_add_le (U := unav P) HU (E := {s(a, qa), s(b, qb)})
      (by intro e he; simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl <;> assumption)
      (by intro e he; simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl <;> assumption)
    rw [← hHeq, c4] at this
    omega

/-- **Corollary 3.** If `|P| ≥ 5`, two triangulations of `P` share at least five edges, and if
they share exactly five then the hull of `P` has five edges. -/
theorem lower {P : Finset (K × K)} (hP : GenPos P) (h5 : 5 ≤ P.card)
    {A B : Finset (Sym2 (K × K))} (hA : IsTri P A) (hB : IsTri P B) :
    5 ≤ (A ∩ B).card ∧ ((A ∩ B).card = 5 → (hullEdges P).card = 5) := by
  have hU := Finset.card_le_card (unav_sub_inter hA hB)
  have hHU := Finset.card_le_card (hull_sub_unav P)
  by_cases hH : 5 ≤ (hullEdges P).card
  · exact ⟨by omega, fun h => by omega⟩
  · have := six_unavoidable hP (by omega) (by omega) (by omega)
    exact ⟨by omega, fun h => by omega⟩

end TwoTri
