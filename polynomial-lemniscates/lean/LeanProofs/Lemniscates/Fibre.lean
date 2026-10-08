import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Complex.Basic

/-!
# Fibres of a finite free `ℂ[t]`-algebra (Lemma 4(c), (d))

Let `S` be a commutative `ℂ[t]`-algebra (compatible with its `ℂ`-algebra structure), free of finite
rank over `ℂ[t]`. For `c ∈ ℂ` the fibre `Q_c = S / (t - c)` has

* `dim_ℂ Q_c = rank_{ℂ[t]} S` (`finrank_fibre`), and
* `trace_ℂ (x̄ on Q_c) = (trace_{ℂ[t]} (x on S))(c)` (`trace_fibre`): the trace on the fibre is a
  fixed polynomial evaluated at the level.

*Proof.* A `ℂ[t]`-basis `b` of `S` reduces to a `ℂ`-basis of `Q_c`, with coordinates
`s ↦ (b.repr s i)(c)`: these coordinates vanish on `(t - c) S`, and
`s - ∑ (b.repr s i)(c) b i = ∑ (b.repr s i - (b.repr s i)(c)) b i ∈ (t - c) S`.
-/

open Polynomial Module

namespace Lemniscates.Fibre

variable {S : Type*} [CommRing S] [Algebra ℂ[X] S] [Algebra ℂ S] [IsScalarTower ℂ ℂ[X] S]
  [Module.Free ℂ[X] S] [Module.Finite ℂ[X] S]

/-- The ideal `(t - c) S`. -/
noncomputable def J (c : ℂ) : Ideal S := Ideal.span {algebraMap ℂ[X] S (X - C c)}

/-- The basis of `S` over `ℂ[t]`. -/
noncomputable abbrev b := Module.Free.chooseBasis ℂ[X] S

/-- Coordinates at the level `c`. -/
noncomputable def coord (c : ℂ) (s : S) : Free.ChooseBasisIndex ℂ[X] S → ℂ :=
  fun i => (b.repr s i).eval c

omit [Algebra ℂ S] [IsScalarTower ℂ ℂ[X] S] [Module.Finite ℂ[X] S] in
lemma coord_add (c : ℂ) (s s' : S) : coord c (s + s') = coord c s + coord c s' := by
  ext i; simp [coord]

omit [Module.Finite ℂ[X] S] in
lemma coord_smul (c a : ℂ) (s : S) : coord c (a • s) = a • coord c s := by
  ext i
  rw [← algebraMap_smul ℂ[X] a s]
  simp [coord]

omit [Algebra ℂ S] [IsScalarTower ℂ ℂ[X] S] [Module.Finite ℂ[X] S] in
lemma coord_J (c : ℂ) {s : S} (hs : s ∈ J c) : coord c s = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  ext i
  rw [coord, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, eval_mul]
  simp

lemma coord_basis_sum (c : ℂ) (v : Free.ChooseBasisIndex ℂ[X] S → ℂ) :
    coord c (∑ i, v i • (b i : S)) = v := by
  ext j
  simp only [coord]
  have : ∑ i, v i • (b i : S) = ∑ i, (C (v i) : ℂ[X]) • (b i : S) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul ℂ[X] (v i) (b i), Polynomial.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
  rw [this, map_sum]
  simp [Finsupp.single_apply]

lemma sub_basis_sum_mem (c : ℂ) (s : S) : s - ∑ i, coord c s i • (b i : S) ∈ J c := by
  have hdvd : ∀ i, X - C c ∣ b.repr s i - C (coord c s i) := fun i => X_sub_C_dvd_sub_C_eval
  choose q hq using hdvd
  have hsum : s - ∑ i, coord c s i • (b i : S) =
      algebraMap ℂ[X] S (X - C c) * ∑ i, q i • (b i : S) := by
    rw [show s - ∑ i, coord c s i • (b i : S) =
      (∑ i, b.repr s i • (b i : S)) - ∑ i, coord c s i • (b i : S) by rw [b.sum_repr]]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul ℂ[X] (coord c s i) (b i), Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, ← sub_smul, hq i, ← Algebra.smul_def, smul_smul]
  rw [hsum]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

variable (c : ℂ)

/-- The fibre's coordinate map, as a `ℂ`-linear map out of `(ι → ℂ)`. -/
noncomputable def Ψ : (Free.ChooseBasisIndex ℂ[X] S → ℂ) →ₗ[ℂ] S ⧸ J c where
  toFun v := Ideal.Quotient.mk _ (∑ i, v i • (b i : S))
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, RingHom.id_apply]
    rw [Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def]

lemma Ψ_coord (s : S) : Ψ c (coord c s) = Ideal.Quotient.mk _ s := by
  rw [Ψ, LinearMap.coe_mk, AddHom.coe_mk, Ideal.Quotient.eq]
  have := neg_mem (sub_basis_sum_mem c s)
  rwa [neg_sub] at this

lemma Ψ_bijective : Function.Bijective (Ψ (S := S) c) := by
  refine ⟨fun v w hvw => ?_, fun q => ?_⟩
  · rw [Ψ, LinearMap.coe_mk, AddHom.coe_mk, Ideal.Quotient.eq] at hvw
    have h := coord_J c hvw
    rw [← Finset.sum_sub_distrib] at h
    simp_rw [← sub_smul] at h
    rw [coord_basis_sum] at h
    exact sub_eq_zero.mp h
  · obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨_, Ψ_coord c s⟩

/-- The induced `ℂ`-basis of the fibre. -/
noncomputable def basis : Basis (Free.ChooseBasisIndex ℂ[X] S) ℂ (S ⧸ J c) :=
  Basis.ofEquivFun (LinearEquiv.ofBijective (Ψ c) (Ψ_bijective c)).symm

lemma basis_repr (s : S) (i : Free.ChooseBasisIndex ℂ[X] S) :
    (basis c).repr (Ideal.Quotient.mk _ s) i = coord c s i := by
  have h : (LinearEquiv.ofBijective (Ψ c) (Ψ_bijective c)).symm (Ideal.Quotient.mk _ s) =
      coord c s := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, Ψ_coord]
  simp [basis, h]

lemma basis_apply (i : Free.ChooseBasisIndex ℂ[X] S) :
    basis c i = Ideal.Quotient.mk _ (b i : S) := by
  rw [basis, Basis.coe_ofEquivFun, LinearEquiv.symm_symm]
  show Ψ c (Pi.single i 1) = _
  rw [Ψ, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem finrank_fibre : finrank ℂ (S ⧸ J c) = finrank ℂ[X] S := by
  rw [finrank_eq_card_basis (basis c), finrank_eq_card_chooseBasisIndex]

theorem trace_fibre (x : S) :
    LinearMap.trace ℂ (S ⧸ J c) (Algebra.lmul ℂ _ (Ideal.Quotient.mk _ x)) =
      (LinearMap.trace ℂ[X] S (Algebra.lmul ℂ[X] S x)).eval c := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (basis c), LinearMap.trace_eq_matrix_trace ℂ[X] b,
    Matrix.trace, Matrix.trace, eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    basis_apply]
  simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  rw [← map_mul, basis_repr, coord]

end Lemniscates.Fibre
