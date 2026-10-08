import EnclosingCopy.Poisson.Law

/-!
# Superposition of independent Poisson processes

If `Π₁` and `Π₂` are independent Poisson processes with finite intensities `Λ₁` and `Λ₂`, their
union is a Poisson process with intensity `Λ₁ + Λ₂`: for every configuration functional `G`,

  `E[G(Π₁ + Π₂)] = expect (Λ₁ + Λ₂) G`.

The proof expands `(Λ₁ + Λ₂)ⁿ` binomially (`lintegral_pi_add`, by induction on `n`, adding one
point at a time) and regroups the double series with `C(n, j)/n! = 1/(j! k!)`.
-/

namespace PoissonPP
open MeasureTheory Set ENNReal Finset

variable {α : Type*} [MeasurableSpace α]

/-- A configuration functional is measurable on tuples of every length. -/
def ConfMeas (G : Multiset α → ℝ≥0∞) : Prop :=
  ∀ n, Measurable fun x : Fin n → α => G (config x)

omit [MeasurableSpace α] in
lemma config_snoc {n : ℕ} (x : Fin n → α) (t : α) :
    config (Fin.snoc x t : Fin (n + 1) → α) = t ::ₘ config x := by
  simp only [config]
  rw [Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ', Multiset.cons_coe, Multiset.coe_eq_coe]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
  exact List.perm_append_singleton _ _

omit [MeasurableSpace α] in
lemma config_append {j k : ℕ} (x : Fin j → α) (y : Fin k → α) :
    config (Fin.append x y) = config x + config y := by
  simp only [config]
  rw [Fin.univ_val_map, Fin.univ_val_map, Fin.univ_val_map, List.ofFn_fin_append]
  rfl

lemma measurable_snoc {n : ℕ} :
    Measurable fun p : (Fin n → α) × α => (Fin.snoc p.1 p.2 : Fin (n + 1) → α) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Fin.snoc_last]; exact measurable_snd
  · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply i).comp measurable_fst

lemma measurable_append {j k : ℕ} :
    Measurable fun p : (Fin j → α) × (Fin k → α) => Fin.append p.1 p.2 := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left]; exact (measurable_pi_apply i).comp measurable_fst
  · simp only [Fin.append_right]; exact (measurable_pi_apply i).comp measurable_snd

lemma ConfMeas.snoc {G : Multiset α → ℝ≥0∞} (hG : ConfMeas G) (n : ℕ) :
    Measurable fun p : (Fin n → α) × α => G (p.2 ::ₘ config p.1) := by
  have := (hG (n + 1)).comp measurable_snoc
  simpa [Function.comp_def, config_snoc] using this

lemma ConfMeas.append {G : Multiset α → ℝ≥0∞} (hG : ConfMeas G) (j k : ℕ) :
    Measurable fun p : (Fin j → α) × (Fin k → α) => G (config p.1 + config p.2) := by
  have := (hG (j + k)).comp measurable_append
  simpa [Function.comp_def, config_append] using this

/-- Adding one point integrated against `μ`. -/
noncomputable def addPt (μ : Measure α) (G : Multiset α → ℝ≥0∞) (c : Multiset α) : ℝ≥0∞ :=
  ∫⁻ t, G (t ::ₘ c) ∂μ

lemma ConfMeas.addPt {G : Multiset α → ℝ≥0∞} (hG : ConfMeas G) (μ : Measure α) [SFinite μ] :
    ConfMeas (addPt μ G) := fun n =>
  (hG.snoc n).lintegral_prod_right'

/-- `∫ G(config z) dμ^{n+1} = ∫ (addPt μ G)(config z') dμⁿ`. -/
lemma lintegral_pi_succ (μ : Measure α) [SigmaFinite μ] {G : Multiset α → ℝ≥0∞}
    (hG : ConfMeas G) (n : ℕ) :
    ∫⁻ z : Fin (n + 1) → α, G (config z) ∂(Measure.pi fun _ => μ) =
      ∫⁻ z : Fin n → α, addPt μ G (config z) ∂(Measure.pi fun _ => μ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) (Fin.last n)
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) (Fin.last n)
  have hsnoc : ∀ z : Fin (n + 1) → α, z = Fin.snoc (fun i => (e z).2 i) (e z).1 := by
    intro z
    simp [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.snoc_init_self]
  have hF : Measurable fun q : α × (Fin n → α) => G (q.1 ::ₘ config q.2) :=
    (hG.snoc n).comp measurable_swap
  calc ∫⁻ z : Fin (n + 1) → α, G (config z) ∂(Measure.pi fun _ => μ)
      = ∫⁻ z : Fin (n + 1) → α, G ((e z).1 ::ₘ config (e z).2) ∂(Measure.pi fun _ => μ) := by
        refine lintegral_congr fun z => ?_
        conv_lhs => rw [hsnoc z]
        rw [config_snoc]
    _ = ∫⁻ q : α × (Fin n → α), G (q.1 ::ₘ config q.2) ∂(μ.prod (Measure.pi fun _ => μ)) :=
        he.lintegral_comp hF
    _ = _ := by
        rw [lintegral_prod_symm _ hF.aemeasurable]
        rfl

/-- `∫ G(config x + config y) dΛ₁^j dΛ₂^k`. -/
noncomputable def pairInt (Λ₁ Λ₂ : Measure α) (G : Multiset α → ℝ≥0∞) (j k : ℕ) : ℝ≥0∞ :=
  ∫⁻ x : Fin j → α, ∫⁻ y : Fin k → α, G (config x + config y)
    ∂(Measure.pi fun _ => Λ₂) ∂(Measure.pi fun _ => Λ₁)

variable (Λ₁ Λ₂ : Measure α) [IsFiniteMeasure Λ₁] [IsFiniteMeasure Λ₂]

lemma pairInt_addPt_left {G : Multiset α → ℝ≥0∞} (hG : ConfMeas G) (j k : ℕ) :
    pairInt Λ₁ Λ₂ (addPt Λ₁ G) j k = pairInt Λ₁ Λ₂ G (j + 1) k := by
  have hG' : ConfMeas fun c => ∫⁻ y : Fin k → α, G (c + config y) ∂(Measure.pi fun _ => Λ₂) :=
    fun n => (hG.append n k).lintegral_prod_right'
  have h := lintegral_pi_succ Λ₁ hG' j
  unfold pairInt
  rw [h]
  refine lintegral_congr fun x => ?_
  unfold addPt
  rw [lintegral_lintegral_swap]
  · simp only [Multiset.cons_add]
  · have hm : Measurable fun p : (Fin k → α) × α => G (p.2 ::ₘ config (Fin.append x p.1)) :=
      (hG.snoc (j + k)).comp ((measurable_append.comp
        (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    simp only [config_append] at hm
    exact hm.aemeasurable

omit [IsFiniteMeasure Λ₁] in
lemma pairInt_addPt_right {G : Multiset α → ℝ≥0∞} (hG : ConfMeas G) (j k : ℕ) :
    pairInt Λ₁ Λ₂ (addPt Λ₂ G) j k = pairInt Λ₁ Λ₂ G j (k + 1) := by
  unfold pairInt
  refine lintegral_congr fun x => ?_
  have hx : ConfMeas fun c => G (config x + c) := fun n =>
    (hG.append j n).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_pi_succ Λ₂ hx k]
  refine lintegral_congr fun y => ?_
  unfold addPt
  simp only [Multiset.add_cons]

lemma lintegral_pi_zero {f : (Fin 0 → α) → ℝ≥0∞} (hf : Measurable f) (μ : Measure α) :
    ∫⁻ z, f z ∂(Measure.pi fun _ : Fin 0 => μ) = f isEmptyElim := by
  rw [Measure.pi_of_empty, lintegral_dirac' _ hf]

omit [IsFiniteMeasure Λ₁] [IsFiniteMeasure Λ₂] in
omit [MeasurableSpace α] in
lemma config_zero (x : Fin 0 → α) : config x = 0 := by simp [config]

/-- **Binomial expansion**: `∫ G dΛⁿ` for `Λ = Λ₁ + Λ₂` splits the points between the two
intensities. -/
lemma lintegral_pi_add (n : ℕ) : ∀ G : Multiset α → ℝ≥0∞, ConfMeas G →
    ∫⁻ z : Fin n → α, G (config z) ∂(Measure.pi fun _ => Λ₁ + Λ₂) =
      ∑ p ∈ antidiagonal n, (n.choose p.1 : ℝ≥0∞) * pairInt Λ₁ Λ₂ G p.1 p.2 := by
  induction n with
  | zero =>
    intro G hG
    rw [lintegral_pi_zero (hG 0), Finset.Nat.antidiagonal_zero, sum_singleton]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, pairInt]
    rw [lintegral_pi_zero ((hG.append 0 0).lintegral_prod_right'), lintegral_pi_zero]
    · simp [config_zero]
    · exact (hG.append 0 0).comp (measurable_const.prodMk measurable_id)
  | succ n ih =>
    intro G hG
    have hadd : addPt (Λ₁ + Λ₂) G = fun c => addPt Λ₁ G c + addPt Λ₂ G c := by
      funext c; simp only [addPt]; rw [lintegral_add_measure]
    rw [lintegral_pi_succ (Λ₁ + Λ₂) hG n, hadd,
      lintegral_add_left ((hG.addPt Λ₁) n), ih _ (hG.addPt Λ₁), ih _ (hG.addPt Λ₂)]
    simp_rw [pairInt_addPt_left Λ₁ Λ₂ hG, pairInt_addPt_right Λ₁ Λ₂ hG]
    set P := pairInt Λ₁ Λ₂ G
    have hA : ∑ p ∈ antidiagonal (n + 1), (n.choose p.1 : ℝ≥0∞) * P p.1 p.2 =
        ∑ p ∈ antidiagonal n, (n.choose p.1 : ℝ≥0∞) * P p.1 (p.2 + 1) := by
      rw [Finset.Nat.sum_antidiagonal_succ']
      simp
    have hB : ∑ p ∈ antidiagonal (n + 1), (n.choose p.1 : ℝ≥0∞) * P p.1 p.2 =
        P 0 (n + 1) + ∑ p ∈ antidiagonal n, (n.choose (p.1 + 1) : ℝ≥0∞) * P (p.1 + 1) p.2 := by
      rw [Finset.Nat.sum_antidiagonal_succ]
      simp
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.choose_succ_succ, Nat.cast_add,
      add_mul, sum_add_distrib]
    rw [← hA, hB]
    ring

omit [IsFiniteMeasure Λ₁] [IsFiniteMeasure Λ₂] in
lemma w0_add [IsFiniteMeasure Λ₁] [IsFiniteMeasure Λ₂] : w0 (Λ₁ + Λ₂) = w0 Λ₁ * w0 Λ₂ := by
  unfold w0
  rw [Measure.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), neg_add,
    Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- `w/(j+k)! · C(j+k, j) = w₁/j! · w₂/k!` when `w = w₁ w₂`. -/
lemma coef_split (w₁ w₂ : ℝ≥0∞) (j k : ℕ) :
    w₁ * w₂ / ((j + k).factorial : ℝ≥0∞) * ((j + k).choose j : ℝ≥0∞) =
      w₁ / (j.factorial : ℝ≥0∞) * (w₂ / (k.factorial : ℝ≥0∞)) := by
  have hf : ((j + k).factorial : ℝ≥0∞) =
      ((j + k).choose j : ℝ≥0∞) * (j.factorial : ℝ≥0∞) * (k.factorial : ℝ≥0∞) := by
    rw [← Nat.add_choose_mul_factorial_mul_factorial j k, Nat.choose_symm_add]; push_cast; ring
  have hC : ((j + k).choose j : ℝ≥0∞) ≠ 0 := by
    have := Nat.choose_pos (Nat.le_add_right j k); exact_mod_cast this.ne'
  have hj : (j.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have hk : (k.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [hf, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (mul_ne_zero hC hj)) (Or.inl (by finiteness)),
    ENNReal.mul_inv (Or.inl hC) (Or.inl (by finiteness))]
  have hCi : ((j + k).choose j : ℝ≥0∞)⁻¹ * ((j + k).choose j : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel hC (by finiteness)
  calc w₁ * w₂ * (((j + k).choose j : ℝ≥0∞)⁻¹ * (j.factorial : ℝ≥0∞)⁻¹ * (k.factorial : ℝ≥0∞)⁻¹) *
        ((j + k).choose j : ℝ≥0∞)
      = w₁ * w₂ * ((((j + k).choose j : ℝ≥0∞)⁻¹ * ((j + k).choose j : ℝ≥0∞)) *
          (j.factorial : ℝ≥0∞)⁻¹ * (k.factorial : ℝ≥0∞)⁻¹) := by ring
    _ = _ := by rw [hCi]; ring

/-- The expectation for `Λ₁ + Λ₂` as a double series over the numbers of points of each kind. -/
theorem expect_add {G : Multiset α → ℝ≥0∞} (hG : ConfMeas G) :
    expect (Λ₁ + Λ₂) G = ∑' j, ∑' k, w0 Λ₁ / (j.factorial : ℝ≥0∞) *
      (w0 Λ₂ / (k.factorial : ℝ≥0∞)) * pairInt Λ₁ Λ₂ G j k := by
  unfold expect
  simp_rw [lintegral_pi_add Λ₁ Λ₂ _ G hG, Finset.mul_sum, w0_add]
  have hterm : ∀ n, ∀ p ∈ antidiagonal n, w0 Λ₁ * w0 Λ₂ / (n.factorial : ℝ≥0∞) *
      ((n.choose p.1 : ℝ≥0∞) * pairInt Λ₁ Λ₂ G p.1 p.2) =
      w0 Λ₁ / (p.1.factorial : ℝ≥0∞) * (w0 Λ₂ / (p.2.factorial : ℝ≥0∞)) *
        pairInt Λ₁ Λ₂ G p.1 p.2 := by
    intro n p hp
    rw [Finset.mem_antidiagonal] at hp
    subst hp
    rw [← mul_assoc, coef_split]
  rw [tsum_congr fun n => Finset.sum_congr rfl (hterm n)]
  set F : ℕ × ℕ → ℝ≥0∞ := fun p => w0 Λ₁ / (p.1.factorial : ℝ≥0∞) *
    (w0 Λ₂ / (p.2.factorial : ℝ≥0∞)) * pairInt Λ₁ Λ₂ G p.1 p.2
  change ∑' n, ∑ p ∈ antidiagonal n, F p = ∑' j, ∑' k, F (j, k)
  rw [← ENNReal.tsum_prod', ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq,
    ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  rw [← Finset.tsum_subtype]
  rfl

/-- **Superposition.** For independent Poisson processes with finite intensities `Λ₁, Λ₂`, the
union of their configurations is a Poisson process with intensity `Λ₁ + Λ₂`. -/
theorem superpose {G : Multiset α → ℝ≥0∞} (hG : ConfMeas G) :
    ∫⁻ ω₁, ∫⁻ ω₂, G (config ω₁.2 + config ω₂.2) ∂law Λ₂ ∂law Λ₁ = expect (Λ₁ + Λ₂) G := by
  have hin : ∀ ω₁ : Sample α, Measurable fun ω₂ : Sample α => G (config ω₁.2 + config ω₂.2) := by
    intro ω₁ S hS
    apply measurableSet_sample
    intro n
    exact ((hG.append ω₁.1 n).comp (measurable_const.prodMk measurable_id)) hS
  simp_rw [fun ω₁ => lintegral_law Λ₂ _ (hin ω₁)]
  have hfib : ∀ k j, Measurable fun x : Fin j → α =>
      ∫⁻ y : Fin k → α, G (config x + config y) ∂(Measure.pi fun _ => Λ₂) :=
    fun k j => (hG.append j k).lintegral_prod_right'
  have hout : Measurable fun ω₁ : Sample α => ∑' k : ℕ, w0 Λ₂ / (k.factorial : ℝ≥0∞) *
      ∫⁻ y : Fin k → α, G (config ω₁.2 + config y) ∂(Measure.pi fun _ => Λ₂) := by
    intro S hS
    apply measurableSet_sample
    intro n
    exact (Measurable.ennreal_tsum fun k => (hfib k n).const_mul _) hS
  rw [lintegral_law Λ₁ _ hout, expect_add Λ₁ Λ₂ hG]
  refine tsum_congr fun j => ?_
  rw [lintegral_tsum fun k => ((hfib k j).const_mul _).aemeasurable, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [lintegral_const_mul _ (hfib k j), pairInt]
  ring

/-! ### Labelled samples and relabelling-invariant functionals -/

omit [MeasurableSpace α] in
lemma config_comp_perm {n : ℕ} (x : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    config (x ∘ σ) = config x := by
  simp only [config]
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

omit [MeasurableSpace α] in
lemma card_config {n : ℕ} (x : Fin n → α) : Multiset.card (config x) = n := by
  simp [config]

omit [MeasurableSpace α] in
/-- Tuples with the same configuration differ by a permutation. -/
lemma exists_perm_of_config_eq {n : ℕ} {x y : Fin n → α} (h : config x = config y) :
    ∃ σ : Equiv.Perm (Fin n), y = x ∘ σ := by
  classical
  have hc : ∀ a, Fintype.card {i // y i = a} = Fintype.card {i // x i = a} := by
    intro a
    have := congrArg (Multiset.count a) h
    simp only [config, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have e1 : ∀ z : Fin n → α, (Finset.univ.filter fun i => z i = a).card =
        Multiset.card (Multiset.filter (fun i => a = z i) Finset.univ.val) := by
      intro z
      rw [Finset.card_def, Finset.filter_val]
      congr 1
      exact Multiset.filter_congr fun i _ => eq_comm
    rw [e1, e1]
    exact this.symm
  have hf : ∀ a, {i // y i = a} ≃ {i // x i = a} := fun a => Fintype.equivOfCardEq (hc a)
  exact ⟨Equiv.ofFiberEquiv hf, funext fun i => (Equiv.ofFiberEquiv_map hf i).symm⟩

/-- A functional of labelled samples that ignores the labels. -/
def PermInv (f : Sample α → ℝ≥0∞) : Prop :=
  ∀ n (x : Fin n → α) (σ : Equiv.Perm (Fin n)), f ⟨n, x ∘ σ⟩ = f ⟨n, x⟩

/-- The configuration functional of a relabelling-invariant `f`. -/
noncomputable def confFun (f : Sample α → ℝ≥0∞) (c : Multiset α) : ℝ≥0∞ := by
  classical
  exact if h : ∃ p : Sample α, config p.2 = c then f h.choose else 0

omit [MeasurableSpace α] in
lemma confFun_config {f : Sample α → ℝ≥0∞} (hf : PermInv f) {n : ℕ} (x : Fin n → α) :
    confFun f (config x) = f ⟨n, x⟩ := by
  classical
  have hex : ∃ p : Sample α, config p.2 = config x := ⟨⟨n, x⟩, rfl⟩
  simp only [confFun, dif_pos hex]
  obtain ⟨⟨m, y⟩, hy⟩ : ∃ p : Sample α, p = hex.choose ∧ True := ⟨_, rfl, trivial⟩
  have hspec := hex.choose_spec
  rw [← hy.1] at hspec ⊢
  have hm : m = n := by
    have := congrArg Multiset.card hspec
    rwa [card_config, card_config] at this
  subst hm
  obtain ⟨σ, hσ⟩ := exists_perm_of_config_eq hspec
  rw [hσ, hf]

lemma confMeas_confFun {f : Sample α → ℝ≥0∞} (hf : PermInv f) (hm : Measurable f) :
    ConfMeas (confFun f) := fun n => by
  simp_rw [confFun_config hf]
  exact hm.comp (measurable_sampleMk n)

/-- Concatenation of two labelled samples. -/
def sappend (ω₁ ω₂ : Sample α) : Sample α := ⟨ω₁.1 + ω₂.1, Fin.append ω₁.2 ω₂.2⟩

/-- **Labelled superposition.** For a measurable functional `f` ignoring labels, concatenating
independent samples with intensities `Λ₁, Λ₂` gives the law with intensity `Λ₁ + Λ₂`. -/
theorem superpose_fun {f : Sample α → ℝ≥0∞} (hinv : PermInv f) (hm : Measurable f) :
    ∫⁻ ω₁, ∫⁻ ω₂, f (sappend ω₁ ω₂) ∂law Λ₂ ∂law Λ₁ = ∫⁻ ω, f ω ∂law (Λ₁ + Λ₂) := by
  have he : ∀ ω₁ ω₂ : Sample α, f (sappend ω₁ ω₂) = confFun f (config ω₁.2 + config ω₂.2) := by
    intro ω₁ ω₂
    rw [← config_append, confFun_config hinv]
    rfl
  simp_rw [he]
  rw [superpose Λ₁ Λ₂ (confMeas_confFun hinv hm), lintegral_law _ _ hm]
  unfold expect
  simp_rw [confFun_config hinv]

end PoissonPP
