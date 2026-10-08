import LeanProofs.Lemniscates.Constancy
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Level zero (Lemma 6)

At levels `(0, 0)` the algebra `ℂ[Z, W] / (f₁(Z) g₁(W), f₂(Z) g₂(W))` splits (Chinese remainder
theorem) as `ℂ[Z, W] / (f₁, g₂) × ℂ[Z, W] / (f₂, g₁)`, and `ℂ[Z, W] / (f, g) ≅ ℂ[Z]/f ⊗ ℂ[W]/g`.
So its dimension is `n₁ m₂ + n₂ m₁` and the trace of `(Z - m)(W - m')` is
`(s₁ - n₁ m)(s₂' - m₂ m') + (s₂ - n₂ m)(s₁' - m₁ m')`, with `s = -nextCoeff` the root sums.

The comaximal ideals: `(f₁, g₂) + (f₂, g₁) ∋ u f₁ + v f₂ = 1`, and their product lies in
`(f₁ g₁, f₂ g₂)` because `f₁ f₂ = (ũ f₂) f₁ g₁ + (ṽ f₁) f₂ g₂` and `g₁ g₂ = (u g₂) f₁ g₁ + (v g₁) f₂ g₂`
for Bézout identities `u f₁ + v f₂ = 1`, `ũ g₁ + ṽ g₂ = 1`.
-/

open Polynomial Module TensorProduct

namespace Lemniscates.Level0

/-- `(Z - m)(W - m')`. -/
noncomputable def φ (m m' : ℂ) : ℂ[X][X] := C (X - C m) * (X - C (C m'))

lemma aevalAeval_map_C {A : Type*} [CommRing A] [Algebra ℂ A] (x y : A) (p : ℂ[X]) :
    (p.map C).aevalAeval x y = aeval y p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, hp, hq]
  | monomial n a => simp [← C_mul_X_pow_eq_monomial]

lemma aevalAeval_φ {A : Type*} [CommRing A] [Algebra ℂ A] (x y : A) (m m' : ℂ) :
    (φ m m').aevalAeval x y = (x - algebraMap ℂ A m) * (y - algebraMap ℂ A m') := by
  simp [φ]

lemma aeval_CX (p : ℂ[X]) : aeval (C X : ℂ[X][X]) p = C p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, C_add]
  | monomial n a => simp [← C_mul_X_pow_eq_monomial]

/-! ### One factor: `ℂ[Z, W] / (f(Z), g(W)) ≅ ℂ[Z]/f ⊗ ℂ[W]/g` -/

section Factor

variable (f g : ℂ[X])

/-- The ideal `(f(Z), g(W))`. -/
noncomputable def I : Ideal ℂ[X][X] := Ideal.span {C f, g.map C}

/-- `ℂ[Z, W] / (f, g)`, as a type synonym (keeps one instance path). -/
def RI : Type := ℂ[X][X] ⧸ I f g

noncomputable instance : CommRing (RI f g) := inferInstanceAs (CommRing (ℂ[X][X] ⧸ I f g))
noncomputable instance : Algebra ℂ (RI f g) := inferInstanceAs (Algebra ℂ (ℂ[X][X] ⧸ I f g))

/-- `ℂ[Z]/f ⊗ ℂ[W]/g`. -/
abbrev T := AdjoinRoot f ⊗[ℂ] AdjoinRoot g

noncomputable def zT : T f g := Algebra.TensorProduct.includeLeft (S := ℂ) (AdjoinRoot.root f)
noncomputable def wT : T f g := Algebra.TensorProduct.includeRight (AdjoinRoot.root g)

lemma aeval_zT : aeval (zT f g) f = 0 := by
  rw [zT, aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

lemma aeval_wT : aeval (wT f g) g = 0 := by
  rw [wT, aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

/-- `ℂ[Z, W] / (f, g) → ℂ[Z]/f ⊗ ℂ[W]/g`. -/
noncomputable def toT : RI f g →ₐ[ℂ] T f g :=
  Ideal.Quotient.liftₐ _ (aevalAeval (zT f g) (wT f g)) (by
    intro a ha
    have hle : I f g ≤ RingHom.ker (aevalAeval (zT f g) (wT f g)) := by
      rw [I, Ideal.span_le]
      rintro x (rfl | rfl)
      · rw [SetLike.mem_coe, RingHom.mem_ker]
        change aevalAeval (zT f g) (wT f g) (C f) = 0
        rw [aevalAeval_C, aeval_zT]
      · rw [SetLike.mem_coe, RingHom.mem_ker]
        change aevalAeval (zT f g) (wT f g) (g.map C) = 0
        rw [aevalAeval_map_C, aeval_wT]
    exact hle ha)

noncomputable def mkI : ℂ[X][X] →ₐ[ℂ] RI f g := Ideal.Quotient.mkₐ ℂ _

lemma mkI_C (p : ℂ[X]) : mkI f g (C p) = aeval (mkI f g (C X)) p := by
  rw [aeval_algHom_apply, aeval_CX]

lemma mkI_map (p : ℂ[X]) : mkI f g (p.map C) = aeval (mkI f g X) p := by
  rw [aeval_algHom_apply, aeval_X_left_eq_map]
  rfl

lemma mkI_Cf : mkI f g (C f) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))

lemma mkI_gmap : mkI f g (g.map C) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- `ℂ[Z]/f ⊗ ℂ[W]/g → ℂ[Z, W] / (f, g)`. -/
noncomputable def fromT : T f g →ₐ[ℂ] RI f g :=
  Algebra.TensorProduct.lift
    (AdjoinRoot.liftAlgHom f (Algebra.ofId ℂ _) (mkI f g (C X)) (by
      change aeval (mkI f g (C X)) f = 0
      rw [← mkI_C, mkI_Cf]))
    (AdjoinRoot.liftAlgHom g (Algebra.ofId ℂ _) (mkI f g X) (by
      change aeval (mkI f g X) g = 0
      rw [← mkI_map, mkI_gmap]))
    (fun _ _ => Commute.all (S := RI f g) _ _)

lemma toT_mk (P : ℂ[X][X]) : toT f g (mkI f g P) = P.aevalAeval (zT f g) (wT f g) := rfl

lemma fromT_zT : fromT f g (zT f g) = mkI f g (C X) := by
  simp [fromT, zT, Algebra.TensorProduct.lift_tmul, AdjoinRoot.liftAlgHom_root, mul_one]

lemma fromT_wT : fromT f g (wT f g) = mkI f g X := by
  simp [fromT, wT, Algebra.TensorProduct.lift_tmul, AdjoinRoot.liftAlgHom_root, one_mul]

lemma to_from : (toT f g).comp (fromT f g) = AlgHom.id ℂ (T f g) := by
  refine Algebra.TensorProduct.ext (AdjoinRoot.algHom_ext ?_) (AdjoinRoot.algHom_ext ?_)
  · change toT f g (fromT f g (zT f g)) = zT f g
    rw [fromT_zT, toT_mk, aevalAeval_X]
  · change toT f g (fromT f g (wT f g)) = wT f g
    rw [fromT_wT, toT_mk, aevalAeval_Y]

lemma mkI_surjective : Function.Surjective (mkI f g) := Ideal.Quotient.mkₐ_surjective ℂ _

lemma algHom_ext_RI {B : Type*} [CommRing B] [Algebra ℂ B] {u v : RI f g →ₐ[ℂ] B}
    (h : u.comp (mkI f g) = v.comp (mkI f g)) : u = v := by
  ext x
  obtain ⟨P, rfl⟩ := mkI_surjective f g x
  exact congrArg (· P) h

lemma from_to : (fromT f g).comp (toT f g) = AlgHom.id ℂ (RI f g) := by
  apply algHom_ext_RI
  apply Deform.biv_ext
  · change fromT f g (toT f g (mkI f g (C X))) = mkI f g (C X)
    rw [toT_mk, aevalAeval_X, fromT_zT]
  · change fromT f g (toT f g (mkI f g X)) = mkI f g X
    rw [toT_mk, aevalAeval_Y, fromT_wT]

/-- **`ℂ[Z, W] / (f, g) ≅ ℂ[Z]/f ⊗ ℂ[W]/g`.** -/
noncomputable def eT : RI f g ≃ₐ[ℂ] T f g :=
  AlgEquiv.ofAlgHom (toT f g) (fromT f g) (to_from f g) (from_to f g)

lemma finrank_adjoinRoot {f : ℂ[X]} (hf : f.Monic) : finrank ℂ (AdjoinRoot f) = f.natDegree := by
  rw [(AdjoinRoot.powerBasis hf.ne_zero).finrank, AdjoinRoot.powerBasis_dim]

/-- The trace of `root - m` on `ℂ[Z]/f` is the root sum minus `n m`. -/
lemma trace_root_sub {f : ℂ[X]} (hf : f.Monic) (hd : 0 < f.natDegree) (m : ℂ) :
    LinearMap.trace ℂ (AdjoinRoot f)
      (Algebra.lmul ℂ _ (AdjoinRoot.root f - algebraMap ℂ _ m)) =
      -f.nextCoeff - f.natDegree * m := by
  have := AdjoinRoot.nontrivial f (by rw [degree_eq_natDegree hf.ne_zero]; exact_mod_cast hd.ne')
  have := (AdjoinRoot.powerBasis hf.ne_zero).finite
  have hroot : LinearMap.trace ℂ (AdjoinRoot f) (Algebra.lmul ℂ _ (AdjoinRoot.root f)) =
      -f.nextCoeff := by
    have := PowerBasis.trace_gen_eq_nextCoeff_minpoly (AdjoinRoot.powerBasis hf.ne_zero)
    rwa [AdjoinRoot.minpoly_powerBasis_gen_of_monic hf, AdjoinRoot.powerBasis_gen] at this
  rw [map_sub, map_sub, hroot, AlgHom.commutes, Module.algebraMap_end_eq_smul_id, map_smul,
    LinearMap.trace_id, finrank_adjoinRoot hf, smul_eq_mul, mul_comm]

lemma lmul_tmul {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] (a : A)
    (b : B) : Algebra.lmul ℂ (A ⊗[ℂ] B) (a ⊗ₜ b) =
      TensorProduct.map (Algebra.lmul ℂ A a) (Algebra.lmul ℂ B b) := by
  refine TensorProduct.ext' fun x y => ?_
  simp [Algebra.coe_lmul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]

lemma eT_φ (m m' : ℂ) : eT f g (mkI f g (φ m m')) =
    (AdjoinRoot.root f - algebraMap ℂ _ m) ⊗ₜ (AdjoinRoot.root g - algebraMap ℂ _ m') := by
  change toT f g (mkI f g (φ m m')) = _
  rw [toT_mk, aevalAeval_φ, zT, wT]
  rw [← (Algebra.TensorProduct.includeLeft (S := ℂ)).commutes m,
    ← (Algebra.TensorProduct.includeRight (A := AdjoinRoot f)).commutes m', ← map_sub, ← map_sub,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- **One factor**: dimension `deg f · deg g`, trace of `(Z - m)(W - m')` a product. -/
theorem factor (hf : f.Monic) (hg : g.Monic) (hfd : 0 < f.natDegree) (hgd : 0 < g.natDegree)
    (m m' : ℂ) :
    finrank ℂ (RI f g) = f.natDegree * g.natDegree ∧
    LinearMap.trace ℂ (RI f g) (Algebra.lmul ℂ _ (mkI f g (φ m m'))) =
      (-f.nextCoeff - f.natDegree * m) * (-g.nextCoeff - g.natDegree * m') := by
  have := (AdjoinRoot.powerBasis hf.ne_zero).finite
  have := (AdjoinRoot.powerBasis hg.ne_zero).finite
  refine ⟨?_, ?_⟩
  · rw [(eT f g).toLinearEquiv.finrank_eq, Module.finrank_tensorProduct, finrank_adjoinRoot hf,
      finrank_adjoinRoot hg]
  · rw [← trace_lmul_algEquiv (eT f g), eT_φ, lmul_tmul, LinearMap.trace_tensorProduct',
      trace_root_sub hf hfd, trace_root_sub hg hgd]

end Factor

lemma Fp_zero (f g : ℂ[X]) : Fp f g 0 = C f * g.map C := by simp [Fp]

lemma lmul_prod {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] (a : A)
    (b : B) : Algebra.lmul ℂ (A × B) (a, b) =
      LinearMap.prodMap (Algebra.lmul ℂ A a) (Algebra.lmul ℂ B b) := by
  refine LinearMap.ext fun ⟨x, y⟩ => ?_
  simp [Algebra.coe_lmul_eq_mul]

lemma finite_RI (f g : ℂ[X]) (hf : f.Monic) (hg : g.Monic) : Module.Finite ℂ (RI f g) := by
  have := (AdjoinRoot.powerBasis hf.ne_zero).finite
  have := (AdjoinRoot.powerBasis hg.ne_zero).finite
  exact Module.Finite.equiv (eT f g).symm.toLinearEquiv

/-! ### Level zero: the Chinese remainder theorem -/

section CRT

variable (D : Deform.Data) (hr : D.r = 0)
include hr

/-- `Q₀ → ℂ[Z, W] / (f', g) × ℂ[Z, W] / (f, g')`, where `h = f g` and `G = f' g'`. -/
noncomputable def Ψ : Deform.Q D 0 →ₐ[ℂ] RI D.f' D.g × RI D.f D.g' :=
  Deform.liftQ D 0 ((mkI D.f' D.g).prod (mkI D.f D.g'))
    (by
      rw [Fp_zero]
      ext
      · change mkI D.f' D.g (C D.f * D.g.map C) = 0
        rw [map_mul, mkI_gmap, mul_zero]
      · change mkI D.f D.g' (C D.f * D.g.map C) = 0
        rw [map_mul, mkI_Cf, zero_mul])
    (by
      rw [hr, Fp_zero]
      ext
      · change mkI D.f' D.g (C D.f' * D.g'.map C) = 0
        rw [map_mul, mkI_Cf, zero_mul]
      · change mkI D.f D.g' (C D.f' * D.g'.map C) = 0
        rw [map_mul, mkI_gmap, mul_zero])

lemma Ψ_mkQ (P : ℂ[X][X]) : Ψ D hr (Deform.mkQ D 0 P) = (mkI D.f' D.g P, mkI D.f D.g' P) := rfl

/-- The four products generating `(f', g)(f, g')` vanish in `Q₀`. -/
lemma mkQ_products (P : ℂ[X][X]) (hP1 : P ∈ I D.f' D.g) (hP2 : P ∈ I D.f D.g') :
    Deform.mkQ D 0 P = 0 := by
  have hcop : IsCoprime (I D.f' D.g) (I D.f D.g') := by
    rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
    obtain ⟨u, v, huv⟩ := D.cf
    have h1 : C u * C D.f ∈ I D.f D.g' := Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
    have h2 : C v * C D.f' ∈ I D.f' D.g := Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
    have : C u * C D.f + C v * C D.f' = 1 := by rw [← C_mul, ← C_mul, ← C_add, huv, C_1]
    rw [← this, add_comm]
    exact Ideal.add_mem _ (Ideal.mem_sup_left h2) (Ideal.mem_sup_right h1)
  have hmem : P ∈ I D.f' D.g * I D.f D.g' := by
    rw [Ideal.mul_eq_inf_of_isCoprime hcop]; exact ⟨hP1, hP2⟩
  have hG : Deform.mkQ D 0 (C D.f' * D.g'.map C) = 0 := by
    have := Deform.mkQ_G D 0; rwa [hr, Fp_zero] at this
  have hh : Deform.mkQ D 0 (C D.f * D.g.map C) = 0 := by
    have := Deform.mkQ_Fp_level D 0; rwa [Fp_zero] at this
  have hff : Deform.mkQ D 0 (C D.f' * C D.f) = 0 := by
    obtain ⟨a, b, hab⟩ := D.cg
    have e : C D.f' * C D.f = (a.map C * C D.f') * (C D.f * D.g.map C) +
        (b.map C * C D.f) * (C D.f' * D.g'.map C) := by
      have := congrArg (Polynomial.map (C : ℂ →+* ℂ[X])) hab
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_one] at this
      linear_combination (-(C D.f' * C D.f)) * this
    rw [e, map_add, map_mul (Deform.mkQ D 0) (a.map C * C D.f'),
      map_mul (Deform.mkQ D 0) (b.map C * C D.f), hh, hG, mul_zero, mul_zero, add_zero]
  have hgg : Deform.mkQ D 0 (D.g.map C * D.g'.map C) = 0 := by
    obtain ⟨a, b, hab⟩ := D.cf
    have e : D.g.map C * D.g'.map C = (C a * D.g'.map C) * (C D.f * D.g.map C) +
        (C b * D.g.map C) * (C D.f' * D.g'.map C) := by
      have := congrArg (C : ℂ[X] →+* ℂ[X][X]) hab
      rw [C_add, C_mul, C_mul, C_1] at this
      linear_combination (-(D.g.map C * D.g'.map C)) * this
    rw [e, map_add, map_mul (Deform.mkQ D 0) (C a * D.g'.map C),
      map_mul (Deform.mkQ D 0) (C b * D.g.map C), hh, hG, mul_zero, mul_zero, add_zero]
  refine Submodule.mul_induction_on hmem (fun r hr' s hs => ?_) (fun x y hx hy => ?_)
  · obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hr'
    obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.mp hs
    have e : (a * C D.f' + b * D.g.map C) * (c * C D.f + d * D.g'.map C) =
        (a * c) * (C D.f' * C D.f) + (a * d) * (C D.f' * D.g'.map C) +
        (b * c) * (C D.f * D.g.map C) + (b * d) * (D.g.map C * D.g'.map C) := by ring
    rw [e, map_add, map_add, map_add, map_mul (Deform.mkQ D 0) (a * c),
      map_mul (Deform.mkQ D 0) (a * d), map_mul (Deform.mkQ D 0) (b * c),
      map_mul (Deform.mkQ D 0) (b * d), hff, hG, hh, hgg]
    simp
  · rw [map_add, hx, hy, add_zero]

lemma Ψ_bijective : Function.Bijective (Ψ D hr) := by
  refine ⟨fun x y hxy => ?_, fun p => ?_⟩
  · obtain ⟨P, rfl⟩ := Deform.mkQ_surjective D 0 x
    obtain ⟨P', rfl⟩ := Deform.mkQ_surjective D 0 y
    rw [Ψ_mkQ, Ψ_mkQ, Prod.mk.injEq] at hxy
    rw [← sub_eq_zero, ← map_sub]
    refine mkQ_products D hr _ ?_ ?_
    · rw [← Ideal.Quotient.eq]; exact hxy.1
    · rw [← Ideal.Quotient.eq]; exact hxy.2
  · -- the idempotent `e = u f`: `1` modulo `(f', g)`, `0` modulo `(f, g')`
    obtain ⟨u, v, huv⟩ := D.cf
    obtain ⟨P, hP⟩ := mkI_surjective D.f' D.g p.1
    obtain ⟨P', hP'⟩ := mkI_surjective D.f D.g' p.2
    obtain ⟨e, he⟩ : ∃ e : ℂ[X][X], e = C (u * D.f) := ⟨_, rfl⟩
    have he1 : mkI D.f' D.g e = 1 := by
      have : e = 1 - C v * C D.f' := by rw [he, ← C_mul, ← C_1, ← C_sub, ← huv]; ring_nf
      rw [this, map_sub, map_one, map_mul, mkI_Cf, mul_zero, sub_zero]
    have he2 : mkI D.f D.g' e = 0 := by
      rw [he, C_mul, map_mul, mkI_Cf, mul_zero]
    refine ⟨Deform.mkQ D 0 (e * P + (1 - e) * P'), ?_⟩
    rw [Ψ_mkQ]
    ext
    · simp only [map_add, map_mul, map_sub, map_one, he1, hP]; ring
    · simp only [map_add, map_mul, map_sub, map_one, he2, hP']; ring

/-- **Chinese remainder theorem at level zero.** -/
noncomputable def E : Deform.Q D 0 ≃ₐ[ℂ] RI D.f' D.g × RI D.f D.g' :=
  AlgEquiv.ofBijective (Ψ D hr) (Ψ_bijective D hr)

/-- **Lemma 6.** Dimension and trace at level `(0, 0)`. -/
theorem level0 (m m' : ℂ) :
    finrank ℂ (Deform.Q D 0) =
      D.f'.natDegree * D.g.natDegree + D.f.natDegree * D.g'.natDegree ∧
    LinearMap.trace ℂ (Deform.Q D 0) (Algebra.lmul ℂ _ (Deform.mkQ D 0 (φ m m'))) =
      (-D.f'.nextCoeff - D.f'.natDegree * m) * (-D.g.nextCoeff - D.g.natDegree * m') +
      (-D.f.nextCoeff - D.f.natDegree * m) * (-D.g'.nextCoeff - D.g'.natDegree * m') := by
  have := finite_RI D.f' D.g D.hf' D.hg
  have := finite_RI D.f D.g' D.hf D.hg'
  have h1 := factor D.f' D.g D.hf' D.hg D.hf'd D.hgd m m'
  have h2 := factor D.f D.g' D.hf D.hg' D.hfd D.hg'd m m'
  refine ⟨?_, ?_⟩
  · rw [(E D hr).toLinearEquiv.finrank_eq, Module.finrank_prod, h1.1, h2.1]
  · rw [← trace_lmul_algEquiv (E D hr)]
    change LinearMap.trace ℂ _ (Algebra.lmul ℂ _ (Ψ D hr (Deform.mkQ D 0 (φ m m')))) = _
    rw [Ψ_mkQ, lmul_prod, LinearMap.trace_prodMap', h1.2, h2.2]

end CRT

end Lemniscates.Level0
