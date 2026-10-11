import LeanProofs.AcuteTetra.Geom

/-!
# Acute tetrahedron (MO 498296, MSE 5083355): the deterministic theorem

For four unit vectors in a 3-dimensional real inner product space, generic in the sense that no
signed triple sum has norm exactly `1`, let `N` be the number of sign vectors `σ ∈ {±1}⁴` whose
tetrahedron `(σ_i A_i)` has four acute faces, and `Σ` the set of short signed triple sums.
Then (counting all 16 sign vectors, so each tetrahedron twice)

  `N + 4 |Σ| = 8 + Σ_σ C(deg σ, 2)`.

Halving gives the identity `N₈ = 4 - 2|Σ| + Σ C(d, 2)` over the 8 tetrahedra used in the written
proof of `P(all faces acute) = 1/12`.
-/

namespace AcuteTetra

open Finset

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma vecOf_cDrop (A : Fin 4 → V) (ε : Sign) (m : Fin 4) :
    vecOf A (cDrop ε m) = (∑ j, (sgZ (ε j) : ℝ) • A j) - (sgZ (ε m) : ℝ) • A m := by
  fin_cases m <;> simp [vecOf, cDrop, Fin.sum_univ_four] <;> abel

/-- In dimension 3, some signed triple sum is short (for generic unit vectors). -/
theorem exists_short [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 3) (A : Fin 4 → V)
    (hA : ∀ i, ‖A i‖ = 1) (hgen : ∀ e, ‖vecOf A (cE e)‖ ≠ 1) : ∃ e, Short A e := by
  by_contra hno
  push Not at hno
  -- every sum with one term dropped has norm > 1
  have hdrop : ∀ ε m, 1 < ‖vecOf A (cDrop ε m)‖ := by
    intro ε m
    obtain ⟨e, he⟩ := drop_edge ε m
    have h1 := gram_congr' A hA he
    rw [← sq_vecOf, ← sq_vecOf] at h1
    have hn : ‖vecOf A (cE e)‖ = ‖vecOf A (cDrop ε m)‖ :=
      (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
    have hns := hno e
    unfold Short at hns
    push Not at hns
    rw [← hn]
    exact lt_of_le_of_ne hns (Ne.symm (hgen e))
  -- four vectors in dimension 3 are dependent
  have hli : ¬ LinearIndependent ℝ A := fun h => by
    have := h.fintype_card_le_finrank
    rw [hdim] at this
    simp at this
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun i => |g i|) ⟨i0, Finset.mem_univ _⟩
  have hgm : g m ≠ 0 := by
    intro h0
    have := hm i0 (Finset.mem_univ _)
    simp [h0] at this
    exact hi0 this
  have hgm' : 0 < |g m| := abs_pos.2 hgm
  set ε : Sign := fun i => decide (0 ≤ g i / g m) with hε
  set B : Fin 4 → V := fun i => (sgZ (ε i) : ℝ) • A i with hB
  set μ : Fin 4 → ℝ := fun i => |g i| / |g m| with hμ
  have hnB : ∀ i, ‖B i‖ = 1 := fun i => norm_sgZ_smul A hA (ε i) i
  have hμ0 : ∀ i, 0 ≤ μ i := fun i => div_nonneg (abs_nonneg _) hgm'.le
  have hμ1 : ∀ i, μ i ≤ 1 := fun i => (div_le_one hgm').2 (hm i (Finset.mem_univ _))
  have hμm : μ m = 1 := div_self hgm'.ne'
  -- μ_i B_i = (g_i / g_m) A_i
  have hμB : ∀ i, μ i • B i = (g i / g m) • A i := by
    intro i
    simp only [hμ, hB, hε, smul_smul]
    congr 1
    rw [← abs_div]
    by_cases h : 0 ≤ g i / g m
    · simp [h, sgZ, abs_of_nonneg h]
    · push Not at h
      simp [not_le.2 h, sgZ, abs_of_neg h]
  have hsum0 : ∑ i, μ i • B i = 0 := by
    simp only [hμB, div_eq_mul_inv, mul_comm (g _), ← smul_smul, ← Finset.smul_sum, hg, smul_zero]
  -- 2 ≤ Σ μ_i, from ‖μ_m B_m‖ ≤ Σ_{i ≠ m} ‖μ_i B_i‖
  have htwo : 2 ≤ ∑ i, μ i := by
    have hsplit := Finset.add_sum_erase Finset.univ (fun i => μ i • B i) (Finset.mem_univ m)
    rw [hsum0] at hsplit
    have hnorm : ‖μ m • B m‖ ≤ ∑ i ∈ Finset.univ.erase m, ‖μ i • B i‖ := by
      rw [eq_neg_of_add_eq_zero_left hsplit, norm_neg]
      exact norm_sum_le _ _
    have hnorm' : ∀ i, ‖μ i • B i‖ = μ i := by
      intro i; rw [norm_smul, hnB, Real.norm_of_nonneg (hμ0 i), mul_one]
    simp only [hnorm'] at hnorm
    have := Finset.add_sum_erase Finset.univ μ (Finset.mem_univ m)
    rw [hμm] at hnorm this
    linarith
  -- S = Σ B_i = Σ (1 - μ_i) B_i
  set S : V := ∑ i, B i with hS
  have hS' : S = ∑ i, (1 - μ i) • B i := by
    simp only [sub_smul, one_smul, Finset.sum_sub_distrib, hsum0, sub_zero]
    rfl
  have hdropB : ∀ i, 1 < ‖S - B i‖ := by
    intro i
    have := hdrop ε i
    rwa [vecOf_cDrop] at this
  have hSne : S ≠ 0 := by
    intro h0
    have := hdropB m
    rw [h0, zero_sub, norm_neg, hnB] at this
    exact lt_irrefl _ this
  have hin : ∀ i, inner ℝ (B i) S < ‖S‖ ^ 2 / 2 := by
    intro i
    have h1 := hdropB i
    have h2 : 1 < ‖S - B i‖ ^ 2 := by nlinarith [norm_nonneg (S - B i)]
    rw [norm_sub_sq_real, hnB, real_inner_comm] at h2
    linarith
  obtain ⟨j, hj⟩ : ∃ j, μ j < 1 := by
    by_contra hall
    push Not at hall
    apply hSne
    rw [hS']
    exact Finset.sum_eq_zero fun i _ => by rw [le_antisymm (hμ1 i) (hall i), sub_self, zero_smul]
  have hSS : ‖S‖ ^ 2 = ∑ i, (1 - μ i) * inner ℝ (B i) S := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 1 [hS']
    simp only [sum_inner, real_inner_smul_left]
  have hlt : ∑ i, (1 - μ i) * inner ℝ (B i) S < ∑ i, (1 - μ i) * (‖S‖ ^ 2 / 2) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left (hin i).le (by linarith [hμ1 i])
    · exact ⟨j, Finset.mem_univ _, mul_lt_mul_of_pos_left (hin j) (by linarith)⟩
  have hrhs : ∑ i, (1 - μ i) * (‖S‖ ^ 2 / 2) = (4 - ∑ i, μ i) * (‖S‖ ^ 2 / 2) := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    simp
  have hpos : 0 < ‖S‖ ^ 2 := by positivity
  rw [← hSS, hrhs] at hlt
  nlinarith

/-- For each face, the (unique, if any) short sum. -/
noncomputable def shortChoice (A : Fin 4 → V) (l : Fin 4) : Option (Bool × Bool) := by
  classical
  exact if h : ∃ p, Short A (l, p) then some h.choose else none

lemma short_iff_choice (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) (e : Edge) :
    Short A e ↔ shortChoice A e.1 = some e.2 := by
  classical
  obtain ⟨l, p⟩ := e
  constructor
  · intro h
    have hex : ∃ p, Short A (l, p) := ⟨p, h⟩
    simp only [shortChoice, hex, dite_true, Option.some.injEq]
    exact one_per_face A hA l _ _ hex.choose_spec h
  · intro h
    simp only [shortChoice] at h
    split_ifs at h with hex
    · rw [Option.some.injEq] at h
      rw [← h]
      exact hex.choose_spec

lemma mem_shortList (c : Fin 4 → Option (Bool × Bool)) (e : Edge) :
    e ∈ shortList c ↔ c e.1 = some e.2 := by
  obtain ⟨l, p⟩ := e
  simp [shortList]

/-- The short-sum pattern of a generic configuration satisfies the three finite constraints. -/
theorem constraints_of [FiniteDimensional ℝ V] (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1)
    (hdim : Module.finrank ℝ V = 3) (hgen : ∀ e, ‖vecOf A (cE e)‖ ≠ 1) :
    constraints (shortChoice A) = true := by
  classical
  set c := shortChoice A with hc
  have hchar : ∀ e, Short A e ↔ c e.1 = some e.2 := short_iff_choice A hA
  have hmem : ∀ e, e ∈ shortList c ↔ Short A e := fun e => by rw [mem_shortList, hchar]
  simp only [constraints, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨e, he⟩ := exists_short hdim A hA hgen
    have := (hmem e).2 he
    cases hl : shortList c with
    | nil => simp [hl] at this
    | cons _ _ => simp
  · simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    intro σ _
    by_contra hall
    simp only [Bool.not_eq_false, List.all_eq_true, beq_iff_eq] at hall
    exact no_star A hA σ fun l => (hchar _).2 (hall l (List.mem_finRange l))
  · simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    intro e he f hf
    by_cases hd : disjointE e f = true
    · right
      have hef : e.1 ≠ f.1 := by
        intro h1
        have h2 : e.2 = f.2 := by
          have := (mem_shortList c e).1 he
          have := (mem_shortList c f).1 hf
          rw [h1] at *
          simp_all
        have : e = f := Prod.ext h1 h2
        subst this
        simp [not_disjoint_self] at hd
      obtain ⟨g, hg, hge, hgf⟩ := join A hA e f hef hd ((hmem e).1 he) ((hmem f).1 hf)
      simp only [adj] at hge hgf
      simp only [joined, List.any_eq_true, Bool.and_eq_true]
      exact ⟨g, (hmem g).2 hg, by simpa using hge, by simpa using hgf⟩
    · left; simpa using hd

open Classical in
/-- `σ` covers every short sum exactly when its tetrahedron has four acute faces. -/
theorem covers_eq (A : Fin 4 → V) (hA : ∀ i, ‖A i‖ = 1) (hgen : ∀ e, ‖vecOf A (cE e)‖ ≠ 1)
    (σ : Sign) : covers (shortChoice A) σ = decide (AcuteVariant A σ) := by
  have hmem : ∀ e, e ∈ shortList (shortChoice A) ↔ Short A e := fun e => by
    rw [mem_shortList, short_iff_choice A hA]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, acute_iff A hA hgen σ]
  simp only [covers, List.all_eq_true]
  exact ⟨fun h e he => h e ((hmem e).2 he), fun h e he => h e ((hmem e).1 he)⟩

open Classical in
/-- **The deterministic theorem.** -/
theorem acute_count [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 3) (A : Fin 4 → V)
    (hA : ∀ i, ‖A i‖ = 1) (hgen : ∀ e, ‖vecOf A (cE e)‖ ≠ 1) :
    ∃ c : Fin 4 → Option (Bool × Bool), (∀ e, Short A e ↔ c e.1 = some e.2) ∧
      (allSigns.filter fun σ => decide (AcuteVariant A σ)).length + 4 * (shortList c).length =
        8 + (allSigns.map fun σ => (deg c σ).choose 2).sum := by
  refine ⟨shortChoice A, short_iff_choice A hA, ?_⟩
  have hid := comb _ (constraints_of A hA hdim hgen)
  simp only [identity, beq_iff_eq] at hid
  rw [← List.filter_congr (fun σ _ => covers_eq A hA hgen σ)]
  exact hid

end AcuteTetra
