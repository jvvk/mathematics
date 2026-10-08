import LeanProofs.Lemniscates.Deform
import LeanProofs.Lemniscates.GrowthGen
import LeanProofs.Lemniscates.Liouville

/-!
# The trace is constant in the level (Proposition 7, analytic step)

`tau_const`: if every common zero of `h - c` and `G` has `‖φ‖ ≤ A + B √‖c‖`, then the trace
polynomial `τ_φ` of `Deform.lean` is constant: `|τ_φ(c)| ≤ N (A + B √‖c‖)` and a polynomial with
square-root growth is constant (`Liouville.lean`).

Also: algebra maps out of a fibre (`liftQ`), and invariance of traces under algebra isomorphisms
(`trace_lmul_algEquiv`), used to compare the two presentations of `ℂ[Z, W] / (f₁ g₁, f₂ g₂ - r₂)`.
-/

open Polynomial Module

namespace Lemniscates.Deform

variable (D : Data)

lemma evalEval_Fp (f g : ℂ[X]) (c Z W : ℂ) : (Fp f g c).evalEval Z W = f.eval Z * g.eval W - c := by
  simp [Fp, evalEval_mul, evalEval_sub, evalEval_C, evalEval_map_C]

/-- **`τ_φ` is constant** under square-root growth. -/
theorem tau_const (φ : ℂ[X][X]) (A B : ℝ)
    (hgr : ∀ c Z W : ℂ, D.f.eval Z * D.g.eval W = c → D.f'.eval Z * D.g'.eval W = D.r →
      ‖φ.evalEval Z W‖ ≤ A + B * Real.sqrt ‖c‖) (c : ℂ) :
    (τ D φ).eval c = (τ D φ).eval 0 := by
  set N := finrank ℂ[X] (M D)
  refine Lemniscates.eq_of_sqrt_growth (f := fun c => (τ D φ).eval c)
    (Polynomial.differentiable _) (A := N * A) (B := N * B) (fun c => ?_) c 0
  obtain ⟨S, hcard, hsum, hzero, -⟩ := fibre_multiset D c
  rw [← hsum]
  have hb : ∀ p ∈ S, ‖φ.evalEval p.1 p.2‖ ≤ A + B * Real.sqrt ‖c‖ := by
    intro p hp
    obtain ⟨h₁, h₂⟩ := hzero p hp
    rw [evalEval_Fp, sub_eq_zero] at h₁ h₂
    exact hgr c p.1 p.2 h₁ h₂
  calc ‖(S.map fun p => φ.evalEval p.1 p.2).sum‖
      ≤ (S.map fun p => ‖φ.evalEval p.1 p.2‖).sum := by
        simpa [Multiset.map_map] using norm_multiset_sum_le (S.map fun p => φ.evalEval p.1 p.2)
    _ ≤ S.card • (A + B * Real.sqrt ‖c‖) := by
        have := Multiset.sum_le_card_nsmul (S.map fun p => ‖φ.evalEval p.1 p.2‖)
          (A + B * Real.sqrt ‖c‖) fun x hx => by
            obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
            exact hb p hp
        rwa [Multiset.card_map] at this
    _ = N * A + N * B * Real.sqrt ‖c‖ := by rw [hcard, nsmul_eq_mul]; ring

/-! ### Maps out of a fibre -/

variable (c : ℂ)

lemma mkQ_surjective : Function.Surjective (mkQ D c) :=
  (Ideal.Quotient.mkₐ_surjective ℂ _).comp (mk_surjective D)

/-- Lifting an algebra map that kills `h - c` and `G` to the fibre. -/
noncomputable def liftQ {B : Type*} [CommRing B] [Algebra ℂ B] (φ : ℂ[X][X] →ₐ[ℂ] B)
    (h₁ : φ (Fp D.f D.g c) = 0) (h₂ : φ (Fp D.f' D.g' D.r) = 0) : Q D c →ₐ[ℂ] B :=
  let φ₁ : M D →ₐ[ℂ] B := Ideal.Quotient.liftₐ _ φ (kills φ _ h₂)
  Ideal.Quotient.liftₐ _ φ₁ (kills φ₁ _ (by
    rw [← mk_Fp_level]
    exact h₁))

lemma liftQ_mkQ {B : Type*} [CommRing B] [Algebra ℂ B] (φ : ℂ[X][X] →ₐ[ℂ] B) (h₁ h₂)
    (P : ℂ[X][X]) : liftQ D c φ h₁ h₂ (mkQ D c P) = φ P := rfl

lemma algHom_ext_Q {B : Type*} [CommRing B] [Algebra ℂ B] {u v : Q D c →ₐ[ℂ] B}
    (h : ∀ P, u (mkQ D c P) = v (mkQ D c P)) : u = v := by
  ext x
  obtain ⟨P, rfl⟩ := mkQ_surjective D c x
  exact h P

end Lemniscates.Deform

namespace Lemniscates

/-- Traces of multiplications are invariant under algebra isomorphisms. -/
lemma trace_lmul_algEquiv {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (e : A ≃ₐ[ℂ] B) (x : A) :
    LinearMap.trace ℂ B (Algebra.lmul ℂ B (e x)) = LinearMap.trace ℂ A (Algebra.lmul ℂ A x) := by
  rw [← LinearMap.trace_conj' (Algebra.lmul ℂ A x) e.toLinearEquiv]
  congr 1
  ext y
  simp [LinearEquiv.conj_apply, Algebra.coe_lmul_eq_mul]

end Lemniscates
