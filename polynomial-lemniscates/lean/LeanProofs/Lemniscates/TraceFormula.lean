import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The trace formula (Lemma 3)

Let `A` be a finite-dimensional commutative `ℂ`-algebra and `a b : A`. There is a multiset `S` of
points of `ℂ²` (the joint eigenvalues of multiplication by `a` and by `b`, each repeated by the
dimension of its joint generalised eigenspace) such that

* `trace (P(a, b)) = ∑_{p ∈ S} P(p)` for every `P : ℂ[X][X]` (`trace_formula`), so `#S = dim A`;
* every `p ∈ S` is a zero of every `P` with `P(a, b) = 0`;
* every algebra map `ev : A → ℂ` gives a member `(ev a, ev b)` of `S`.

For `A = ℂ[Z, W] / I` with `I` of finite codimension, `S` is the zero set of `I` with
multiplicities. This replaces the local-ring decomposition of Fulton §2.9: on a joint generalised
eigenspace `V_χ`, `P(a, b) - P(χ)` acts nilpotently, so it has trace zero there.

Bivariate convention (as in `NoCommon.lean`): the inner variable is `Z = C X`, the outer one
`W = X`; `P(z, w) = P.evalEval z w`, `P(a, b) = P.aevalAeval a b`.
-/

open Module Polynomial

namespace Lemniscates.TraceFormula

variable {A : Type*} [CommRing A] [Algebra ℂ A] [FiniteDimensional ℂ A] (a b : A)

/-- Multiplication by `a` and by `b`. -/
noncomputable def ops : Fin 2 → End ℂ A := ![Algebra.lmul ℂ A a, Algebra.lmul ℂ A b]

/-- The joint generalised eigenspace for the eigenvalue pair `χ`. -/
noncomputable def V (χ : Fin 2 → ℂ) : Submodule ℂ A := ⨅ i, (ops a b i).maxGenEigenspace (χ i)

omit [FiniteDimensional ℂ A] in
lemma lmul_comm (x y : A) : Commute (Algebra.lmul ℂ A x) (Algebra.lmul ℂ A y) := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

omit [FiniteDimensional ℂ A] in
lemma ops_comm (i j : Fin 2) : Commute (ops a b i) (ops a b j) := by
  fin_cases i <;> fin_cases j <;> exact lmul_comm _ _

lemma iSup_V : ⨆ χ, V a b χ = ⊤ :=
  End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute _
    (fun i j _ => ops_comm a b i j) (fun _ => End.iSup_maxGenEigenspace_eq_top _)

omit [FiniteDimensional ℂ A] in
lemma indep_V : iSupIndep (V a b) :=
  End.independent_iInf_maxGenEigenspace_of_forall_mapsTo _
    (fun i j φ => End.mapsTo_maxGenEigenspace_of_comm (ops_comm a b j i) φ)

lemma finite_V : {χ | V a b χ ≠ ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep (indep_V a b)

omit [FiniteDimensional ℂ A] in
/-- Each `V χ` is stable under every multiplication. -/
lemma mapsTo_V (x : A) (χ : Fin 2 → ℂ) :
    Set.MapsTo (Algebra.lmul ℂ A x) (V a b χ) (V a b χ) := by
  intro v hv
  simp only [V, SetLike.mem_coe, Submodule.mem_iInf] at hv ⊢
  intro i
  have hc : Commute (ops a b i) (Algebra.lmul ℂ A x) := by fin_cases i <;> exact lmul_comm _ _
  exact End.mapsTo_maxGenEigenspace_of_comm hc _ (hv i)

/-! ### The annihilator of `V χ` and its radical -/

/-- The annihilator of `V χ`, an ideal of `A`. -/
def ann (χ : Fin 2 → ℂ) : Ideal A where
  carrier := {u | ∀ v ∈ V a b χ, u * v = 0}
  add_mem' {u w} hu hw v hv := by rw [add_mul, hu v hv, hw v hv, add_zero]
  zero_mem' v _ := zero_mul v
  smul_mem' c u hu v hv := by rw [smul_eq_mul, mul_assoc, hu v hv, mul_zero]

omit [FiniteDimensional ℂ A] in
lemma lmul_sub_pow (x : A) (c : ℂ) (k : ℕ) (v : A) :
    ((Algebra.lmul ℂ A x - c • (1 : End ℂ A)) ^ k) v = (x - algebraMap ℂ A c) ^ k * v := by
  have : Algebra.lmul ℂ A x - c • (1 : End ℂ A) = Algebra.lmul ℂ A (x - algebraMap ℂ A c) := by
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  rw [this, ← map_pow]
  rfl

/-- `a - χ 0` and `b - χ 1` act nilpotently on `V χ`. -/
lemma gen_mem_radical (χ : Fin 2 → ℂ) (i : Fin 2) :
    ![a, b] i - algebraMap ℂ A (χ i) ∈ (ann a b χ).radical := by
  refine ⟨finrank ℂ A, fun v hv => ?_⟩
  have hv' : v ∈ (ops a b i).maxGenEigenspace (χ i) := (Submodule.mem_iInf _).mp hv i
  rw [End.maxGenEigenspace_eq_genEigenspace_finrank, End.mem_genEigenspace_nat,
    LinearMap.mem_ker] at hv'
  rw [← lmul_sub_pow]
  fin_cases i <;> exact hv'

/-- `P(a, b) - P(χ)` acts nilpotently on `V χ`. -/
lemma eval_mem_radical (χ : Fin 2 → ℂ) (P : ℂ[X][X]) :
    P.aevalAeval a b - algebraMap ℂ A (P.evalEval (χ 0) (χ 1)) ∈ (ann a b χ).radical := by
  set J := (ann a b χ).radical
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  have ha := gen_mem_radical a b χ 0
  have hb := gen_mem_radical a b χ 1
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at ha hb
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha hb
  have key : (Ideal.Quotient.mkₐ ℂ J).comp (aevalAeval a b) =
      (Algebra.ofId ℂ (A ⧸ J)).comp (aevalAeval (χ 0) (χ 1)) := by
    apply (aevalAevalEquiv ℂ (A ⧸ J)).symm.injective
    simp only [aevalAevalEquiv, Equiv.coe_fn_symm_mk, AlgHom.comp_apply, aevalAeval_X,
      aevalAeval_Y, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply]
    exact Prod.ext ha hb
  have := congrArg (fun φ => φ P) key
  simpa [coe_aevalAeval_eq_evalEval] using this

/-- On `V χ`, multiplication by `x` is `c` plus a nilpotent once `x - c` is in the radical. -/
lemma trace_restrict (χ : Fin 2 → ℂ) (x : A) (c : ℂ)
    (h : x - algebraMap ℂ A c ∈ (ann a b χ).radical) :
    LinearMap.trace ℂ (V a b χ) ((Algebra.lmul ℂ A x).restrict (mapsTo_V a b x χ)) =
      finrank ℂ (V a b χ) * c := by
  obtain ⟨k, hk⟩ := h
  set R := (Algebra.lmul ℂ A x).restrict (mapsTo_V a b x χ)
  have hsplit : R = (R - algebraMap ℂ _ c) + algebraMap ℂ _ c := by abel
  have hnil : IsNilpotent (R - algebraMap ℂ _ c) := by
    refine ⟨k, LinearMap.ext fun v => Subtype.ext ?_⟩
    have : ∀ j : ℕ, (((R - algebraMap ℂ _ c) ^ j) v : A) = (x - algebraMap ℂ A c) ^ j * v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hR : ∀ w : V a b χ, ((R w : V a b χ) : A) = x * w := fun _ => rfl
        rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Submodule.coe_sub,
          Module.algebraMap_end_apply, Submodule.coe_smul, hR, ih, Algebra.smul_def]
        ring
    rw [this]
    exact hk v v.2
  rw [hsplit, map_add, LinearMap.isNilpotent_trace_of_isNilpotent hnil |>.eq_zero, zero_add,
    Module.algebraMap_end_eq_smul_id, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

/-! ### The multiset of joint eigenvalues -/

/-- The joint eigenvalues with multiplicity. -/
noncomputable def S : Multiset (ℂ × ℂ) :=
  (finite_V a b).toFinset.val.bind fun χ => Multiset.replicate (finrank ℂ (V a b χ)) (χ 0, χ 1)

lemma sum_S (g : ℂ × ℂ → ℂ) :
    ((S a b).map g).sum = ∑ χ ∈ (finite_V a b).toFinset, finrank ℂ (V a b χ) * g (χ 0, χ 1) := by
  rw [S, Multiset.map_bind, Multiset.sum_bind]
  simp only [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
  rfl

/-- **Trace formula.** -/
theorem trace_eq (P : ℂ[X][X]) :
    LinearMap.trace ℂ A (Algebra.lmul ℂ A (P.aevalAeval a b)) =
      ((S a b).map fun p => P.evalEval p.1 p.2).sum := by
  classical
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (indep_V a b) (iSup_V a b)
  rw [LinearMap.trace_eq_sum_trace_restrict' hint (finite_V a b) (mapsTo_V a b _), sum_S]
  exact Finset.sum_congr rfl fun χ _ => trace_restrict a b χ _ _ (eval_mem_radical a b χ P)

theorem card_S : (S a b).card = finrank ℂ A := by
  have := trace_eq a b 1
  rw [map_one, map_one, LinearMap.trace_one] at this
  simpa [Multiset.map_const', Multiset.sum_replicate] using this.symm

lemma mem_S {p : ℂ × ℂ} (hp : p ∈ S a b) : ∃ χ, V a b χ ≠ ⊥ ∧ p = (χ 0, χ 1) := by
  simp only [S, Multiset.mem_bind, Finset.mem_val, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp
  obtain ⟨χ, hχ, hp⟩ := hp
  exact ⟨χ, hχ, Multiset.eq_of_mem_replicate hp⟩

/-- Members of `S` are zeros of every relation between `a` and `b`. -/
theorem eval_eq_zero_of_mem {p : ℂ × ℂ} (hp : p ∈ S a b) {P : ℂ[X][X]}
    (hP : P.aevalAeval a b = 0) : P.evalEval p.1 p.2 = 0 := by
  obtain ⟨χ, hχ, rfl⟩ := mem_S a b hp
  obtain ⟨k, hk⟩ := eval_mem_radical a b χ P
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have h1 : ((-P.evalEval (χ 0) (χ 1)) ^ k) • v = 0 := by
    rw [Algebra.smul_def, map_pow, map_neg]
    simpa [hP] using hk v hv
  rcases smul_eq_zero.mp h1 with h | h
  · exact neg_eq_zero.mp (eq_zero_of_pow_eq_zero h)
  · exact absurd h hv0
/-- Every point of the spectrum, i.e. every algebra map `A → ℂ`, is a member of `S`. -/
theorem mem_S_of_algHom (ev : A →ₐ[ℂ] ℂ) : (ev a, ev b) ∈ S a b := by
  set χ : Fin 2 → ℂ := ![ev a, ev b]
  -- `ev` kills every `V ψ` with `ψ ≠ χ`
  have kill : ∀ ψ, ψ ≠ χ → ∀ v ∈ V a b ψ, ev v = 0 := by
    intro ψ hψ v hv
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hψ
    obtain ⟨k, hk⟩ := gen_mem_radical a b ψ i
    have := congrArg ev (hk v hv)
    rw [map_mul, map_pow, map_sub, AlgHom.commutes, map_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · refine absurd (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h)) (fun h' => hi ?_)
      fin_cases i <;> simpa [χ] using h'.symm
    · exact h
  have hne : V a b χ ≠ ⊥ := by
    intro hbot
    have h1 : (1 : A) ∈ ⨆ ψ, V a b ψ := by rw [iSup_V]; trivial
    have : ev 1 = 0 := by
      refine Submodule.iSup_induction (V a b) (motive := fun x => ev x = 0) h1 ?_ (map_zero ev)
        (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
      intro ψ v hv
      by_cases hψ : ψ = χ
      · subst hψ; rw [hbot] at hv; rw [(Submodule.mem_bot ℂ).mp hv, map_zero]
      · exact kill ψ hψ v hv
    exact one_ne_zero (this ▸ (map_one ev).symm)
  simp only [S, Multiset.mem_bind, Finset.mem_val, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  refine ⟨χ, hne, Multiset.mem_replicate.mpr ⟨?_, rfl⟩⟩
  rw [Ne, Submodule.finrank_eq_zero]
  exact hne

end Lemniscates.TraceFormula
