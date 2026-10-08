import LeanProofs.Lemniscates.NoCommon
import LeanProofs.Lemniscates.Integral
import LeanProofs.Lemniscates.Fibre
import LeanProofs.Lemniscates.TraceFormula
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.FiniteType

/-!
# The deformation module (Lemma 4)

Fix `G = f'(Z) g'(W) - r` and let the level of `h = f(Z) g(W)` vary. `M = ℂ[Z, W] / (G)` is a
`ℂ[t]`-algebra via `t ↦ h`, and

* `M` is finite over `ℂ[t]`: `Z` and `W` are integral (`Integral.exists_monic`);
* `M` is torsion-free: a prime factor of `G` dividing `p(h)` would divide some `h - c`, which the
  hypothesis `hno` (Lemma 1 or 1' of `NoCommon.lean`) excludes;
* hence `M` is free (Mathlib, modules over a PID), and its fibre at `c` is
  `ℂ[Z, W] / (G, h - c)` (`Fibre.lean`).

`fibre_multiset`: for every level `c` there is a multiset `S` of common zeros of `h - c` and `G`,
of size `rank M`, containing every common zero, with `∑_{p ∈ S} φ(p) = τ_φ(c)` for one polynomial
`τ_φ` independent of `c`.
-/

open Polynomial Module

namespace Lemniscates.Deform

/-- The data of one deformation: `h = f(Z) g(W)` varies, `G = f'(Z) g'(W) - r` is fixed. -/
structure Data where
  (f g f' g' : ℂ[X])
  (r : ℂ)
  (hf : f.Monic) (hg : g.Monic) (hf' : f'.Monic) (hg' : g'.Monic)
  (hfd : 0 < f.natDegree) (hgd : 0 < g.natDegree) (hf'd : 0 < f'.natDegree)
  (hg'd : 0 < g'.natDegree)
  (cf : IsCoprime f f') (cg : IsCoprime g g')
  (hno : ∀ (c : ℂ) (H : ℂ[X][X]), Prime H → H ∣ Fp f g c → H ∣ Fp f' g' r → False)

variable (D : Data)

/-- `ℂ[Z, W] / (G)`. -/
def M : Type := ℂ[X][X] ⧸ Ideal.span {Fp D.f' D.g' D.r}

noncomputable instance : CommRing (M D) :=
  inferInstanceAs (CommRing (ℂ[X][X] ⧸ Ideal.span {Fp D.f' D.g' D.r}))

noncomputable instance : Algebra ℂ (M D) :=
  inferInstanceAs (Algebra ℂ (ℂ[X][X] ⧸ Ideal.span {Fp D.f' D.g' D.r}))

/-- The quotient map. -/
noncomputable def mk : ℂ[X][X] →ₐ[ℂ] M D := Ideal.Quotient.mkₐ ℂ _

lemma mk_surjective : Function.Surjective (mk D) := Ideal.Quotient.mkₐ_surjective ℂ _

lemma mk_G : mk D (Fp D.f' D.g' D.r) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

/-- `t ↦ h`. -/
noncomputable instance : Algebra ℂ[X] (M D) :=
  (aeval (mk D (Fp D.f D.g 0))).toRingHom.toAlgebra

lemma algebraMap_eq (p : ℂ[X]) : algebraMap ℂ[X] (M D) p = aeval (mk D (Fp D.f D.g 0)) p := rfl

instance : IsScalarTower ℂ ℂ[X] (M D) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [algebraMap_eq, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      aeval_C]

/-- Two algebra maps out of `ℂ[Z, W]` agreeing on `Z` and `W` agree. -/
lemma biv_ext {A : Type*} [CommRing A] [Algebra ℂ A] {φ ψ : ℂ[X][X] →ₐ[ℂ] A}
    (hZ : φ (C X) = ψ (C X)) (hW : φ X = ψ X) : φ = ψ := by
  rw [← (aevalAevalEquiv ℂ A).apply_symm_apply φ, ← (aevalAevalEquiv ℂ A).apply_symm_apply ψ]
  congr 1
  simp only [aevalAevalEquiv, Equiv.coe_fn_symm_mk]
  exact Prod.ext hZ hW

/-- The images of `Z` and `W`. -/
noncomputable def z : M D := mk D (C X)
noncomputable def w : M D := mk D X

lemma mk_eq (P : ℂ[X][X]) : mk D P = P.aevalAeval (z D) (w D) := by
  have : mk D = aevalAeval (z D) (w D) := biv_ext (by simp [z]) (by simp [w])
  rw [this]

lemma mk_C (p : ℂ[X]) : mk D (C p) = aeval (z D) p := by
  rw [mk_eq, aevalAeval_C]

lemma mk_map (p : ℂ[X]) : mk D (p.map C) = aeval (w D) p := by
  rw [mk_eq]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, hp, hq]
  | monomial n a => simp [← C_mul_X_pow_eq_monomial]

/-- The level element `h = f(Z) g(W)` in `M`. -/
noncomputable def hM : M D := mk D (Fp D.f D.g 0)

lemma rel₁ : aeval (z D) D.f * aeval (w D) D.g = hM D := by
  rw [hM, ← mk_C, ← mk_map, ← map_mul]
  congr 1
  simp [Fp]

lemma mk_CC (a : ℂ) : mk D (C (C a)) = algebraMap ℂ (M D) a := by
  rw [← (mk D).commutes a]; rfl

lemma rel₂ : aeval (z D) D.f' * aeval (w D) D.g' = algebraMap ℂ (M D) D.r := by
  have h := mk_G D
  rw [Fp, map_sub, map_mul, mk_C, mk_map, mk_CC, sub_eq_zero] at h
  exact h

lemma isIntegral_z : IsIntegral ℂ[X] (z D) := by
  obtain ⟨p, hp, hev⟩ := Integral.exists_monic (z D) (w D) (hM D) D.f D.g D.f' D.g' D.r D.hf
    D.hf' D.hfd D.hf'd D.hgd D.cg (rel₁ D) (rel₂ D)
  exact ⟨p, hp, hev⟩

lemma isIntegral_w : IsIntegral ℂ[X] (w D) := by
  obtain ⟨p, hp, hev⟩ := Integral.exists_monic (w D) (z D) (hM D) D.g D.f D.g' D.f' D.r D.hg
    D.hg' D.hgd D.hg'd D.hfd D.cf (by rw [mul_comm]; exact rel₁ D) (by rw [mul_comm]; exact rel₂ D)
  exact ⟨p, hp, hev⟩

/-- A `ℂ`-subalgebra containing `Z` and `W` is everything. -/
lemma mem_of_gen (T : Subalgebra ℂ (M D)) (hz : z D ∈ T) (hw : w D ∈ T) (x : M D) : x ∈ T := by
  obtain ⟨P, rfl⟩ := mk_surjective D x
  have : mk D = T.val.comp (aevalAeval (⟨z D, hz⟩ : T) ⟨w D, hw⟩) :=
    biv_ext (by simp [z]) (by simp [w])
  rw [this]
  exact (aevalAeval (⟨z D, hz⟩ : T) ⟨w D, hw⟩ P).2

instance : Algebra.IsIntegral ℂ[X] (M D) :=
  ⟨fun x => mem_of_gen D ((integralClosure ℂ[X] (M D)).restrictScalars ℂ) (isIntegral_z D)
    (isIntegral_w D) x⟩

lemma adjoin_eq_top : Algebra.adjoin ℂ[X] ({z D, w D} : Set (M D)) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hz : z D ∈ (Algebra.adjoin ℂ[X] ({z D, w D} : Set (M D))).restrictScalars ℂ :=
    (Subalgebra.mem_restrictScalars ℂ).mpr (Algebra.subset_adjoin (Set.mem_insert _ _))
  have hw : w D ∈ (Algebra.adjoin ℂ[X] ({z D, w D} : Set (M D))).restrictScalars ℂ :=
    (Subalgebra.mem_restrictScalars ℂ).mpr
      (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  exact (Subalgebra.mem_restrictScalars ℂ).mp (mem_of_gen D _ hz hw x)

instance : Algebra.FiniteType ℂ[X] (M D) :=
  ⟨Subalgebra.fg_def.mpr ⟨{z D, w D}, (Set.finite_singleton _).insert _, adjoin_eq_top D⟩⟩

instance : Module.Finite ℂ[X] (M D) := Algebra.IsIntegral.finite

lemma G_ne_zero : Fp D.f' D.g' D.r ≠ 0 := by
  intro h0
  have := (Fp_natDegree_leadingCoeff D.r D.hf'.ne_zero D.hg' D.hg'd).2
  rw [h0, leadingCoeff_zero] at this
  exact D.hf'.ne_zero this.symm

lemma aeval_Fp (c : ℂ) : aeval (Fp D.f D.g 0) (X - C c) = Fp D.f D.g c := by
  simp [Fp, Polynomial.algebraMap_apply]

instance : IsTorsionFree ℂ[X] (M D) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun p m hpm => ?_
  by_cases hp : p = 0
  · exact Or.inl hp
  right
  obtain ⟨a, rfl⟩ := mk_surjective D m
  rw [Algebra.smul_def, algebraMap_eq, Polynomial.aeval_algHom_apply (mk D) (Fp D.f D.g 0) p,
    ← map_mul] at hpm
  have hdvd : Fp D.f' D.g' D.r ∣ aeval (Fp D.f D.g 0) p * a :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hpm)
  refine Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ?_)
  refine UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors (G_ne_zero D) (fun {d} hdG hdp hd => ?_) hdvd
  -- `p(h) = lc · ∏ (h - c_j)` and a prime factor divides some `h - c_j`
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree
  rw [← hfac, map_mul, aeval_C, map_multiset_prod, Multiset.map_map] at hdp
  rcases hd.dvd_or_dvd hdp with h | h
  · exact hd.not_isUnit (isUnit_of_dvd_unit h ((leadingCoeff_ne_zero.mpr hp).isUnit.map _))
  · obtain ⟨c, -, hc⟩ := hd.exists_mem_multiset_map_dvd h
    rw [Function.comp_apply, aeval_Fp] at hc
    exact D.hno c d hd hc hdG

example : Module.Free ℂ[X] (M D) := inferInstance

/-! ### The fibre at level `c` -/

variable (c : ℂ)

/-- `ℂ[Z, W] / (G, h - c)`. -/
abbrev Q := M D ⧸ Fibre.J (S := M D) c

noncomputable instance : Module.Finite ℂ (Q D c) := Module.Finite.of_basis (Fibre.basis c)

/-- `ℂ[Z, W] → Q`. -/
noncomputable def mkQ : ℂ[X][X] →ₐ[ℂ] Q D c := (Ideal.Quotient.mkₐ ℂ _).comp (mk D)

lemma mkQ_eq (P : ℂ[X][X]) : mkQ D c P = P.aevalAeval (mkQ D c (C X)) (mkQ D c X) := by
  have : mkQ D c = aevalAeval (mkQ D c (C X)) (mkQ D c X) := biv_ext (by simp) (by simp)
  exact congrArg (· P) this

/-- The polynomial `τ_φ`: the trace of `φ` on `M` over `ℂ[t]`. -/
noncomputable def τ (φ : ℂ[X][X]) : ℂ[X] :=
  LinearMap.trace ℂ[X] (M D) (Algebra.lmul ℂ[X] (M D) (mk D φ))

lemma mk_Fp_level : mk D (Fp D.f D.g c) = algebraMap ℂ[X] (M D) (X - C c) := by
  rw [algebraMap_eq, Polynomial.aeval_algHom_apply, aeval_Fp]

lemma mkQ_Fp_level : mkQ D c (Fp D.f D.g c) = 0 := by
  rw [mkQ, AlgHom.comp_apply, mk_Fp_level, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

lemma mkQ_G : mkQ D c (Fp D.f' D.g' D.r) = 0 := by
  rw [mkQ, AlgHom.comp_apply, mk_G, map_zero]

/-- An algebra map killing a principal ideal's generator kills the ideal. -/
lemma kills {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)
    (g : A) (hg : φ g = 0) : ∀ a ∈ Ideal.span {g}, φ a = 0 := by
  intro a ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [map_mul, hg, mul_zero]

/-- Every common zero of `h - c` and `G` gives an algebra map `Q → ℂ`. -/
noncomputable def ev (zz ww : ℂ) (h₁ : (Fp D.f D.g c).evalEval zz ww = 0)
    (h₂ : (Fp D.f' D.g' D.r).evalEval zz ww = 0) : Q D c →ₐ[ℂ] ℂ :=
  let ev₀ : ℂ[X][X] →ₐ[ℂ] ℂ := aevalAeval zz ww
  let ev₁ : M D →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ _ ev₀
    (kills ev₀ _ (by rw [coe_aevalAeval_eq_evalEval]; exact h₂))
  Ideal.Quotient.liftₐ _ ev₁ (kills ev₁ _ (by
    rw [← mk_Fp_level]
    show ev₀ (Fp D.f D.g c) = 0
    rw [coe_aevalAeval_eq_evalEval]; exact h₁))

lemma ev_mkQ (zz ww : ℂ) (h₁ h₂) (P : ℂ[X][X]) :
    ev D c zz ww h₁ h₂ (mkQ D c P) = P.evalEval zz ww := by
  rw [← coe_aevalAeval_eq_evalEval]
  rfl

/-- **Lemma 4, assembled.** -/
theorem fibre_multiset : ∃ S : Multiset (ℂ × ℂ),
    S.card = finrank ℂ[X] (M D) ∧
    (∀ φ : ℂ[X][X], (S.map fun p => φ.evalEval p.1 p.2).sum = (τ D φ).eval c) ∧
    (∀ p ∈ S, (Fp D.f D.g c).evalEval p.1 p.2 = 0 ∧ (Fp D.f' D.g' D.r).evalEval p.1 p.2 = 0) ∧
    ∀ zz ww : ℂ, (Fp D.f D.g c).evalEval zz ww = 0 → (Fp D.f' D.g' D.r).evalEval zz ww = 0 →
      (zz, ww) ∈ S := by
  set a := mkQ D c (C X)
  set b := mkQ D c X
  refine ⟨TraceFormula.S a b, ?_, fun φ => ?_, fun p hp => ?_, fun zz ww h₁ h₂ => ?_⟩
  · rw [TraceFormula.card_S, Fibre.finrank_fibre]
  · rw [← TraceFormula.trace_eq, ← mkQ_eq, τ, ← Fibre.trace_fibre]
    rfl
  · exact ⟨TraceFormula.eval_eq_zero_of_mem a b hp (by rw [← mkQ_eq]; exact mkQ_Fp_level D c),
      TraceFormula.eval_eq_zero_of_mem a b hp (by rw [← mkQ_eq]; exact mkQ_G D c)⟩
  · have := TraceFormula.mem_S_of_algHom a b (ev D c zz ww h₁ h₂)
    rwa [ev_mkQ, ev_mkQ, evalEval_C, eval_X, evalEval_X] at this

end Lemniscates.Deform
