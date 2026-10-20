import Mathlib

/-!
# Product trajectories (Physics SE 816017), part 4: from exponential sums to polynomials

* `exists_lattice`: finitely many real frequencies `λⱼ` are `λⱼ = e_j · ω + c` with `e_j ∈ ℕ^k` and
  `ω₁, …, ω_k` linearly independent over `ℤ` (a `ℤ`-basis of the group they generate, then a shift).
* `eval_zt`: evaluating a polynomial at the torus point `zₜ = (e^{-iω₁t}, …, e^{-iω_kt})` gives the
  exponential sum `∑_r coeff_r · e^{-i(r·ω)t}`.
* `eq_zero_of_eval_zt`: a polynomial whose exponential sum vanishes for every `t` is zero (distinct
  frequencies `r · ω` and Dedekind independence of characters).

This is Step 1' of the hand proof.
-/

namespace ProductTrajectory

open MvPolynomial Complex

variable {k : ℕ}

/-- `r · ω`. -/
def dot (ω : Fin k → ℝ) (r : Fin k →₀ ℕ) : ℝ := ∑ i, (r i : ℝ) * ω i

/-- The torus point at time `t`. -/
noncomputable def zt (ω : Fin k → ℝ) (t : ℝ) : Fin k → ℂ := fun i => exp (-(I * (ω i * t)))

theorem eval_zt_monomial (ω : Fin k → ℝ) (t : ℝ) (r : Fin k →₀ ℕ) (a : ℂ) :
    eval (zt ω t) (monomial r a) = a * exp (-(I * (dot ω r * t))) := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp only [zt, ← Complex.exp_nat_mul, ← Complex.exp_sum]
  congr 2
  simp only [dot]
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem eval_zt (ω : Fin k → ℝ) (t : ℝ) (p : MvPolynomial (Fin k) ℂ) :
    eval (zt ω t) p = ∑ r ∈ p.support, p.coeff r * exp (-(I * (dot ω r * t))) := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  simp [eval_zt_monomial]

/-- The character `t ↦ e^{-iνt}` of `(ℝ, +)`. -/
noncomputable def chi (ν : ℝ) : Multiplicative ℝ →* ℂ where
  toFun t := exp (-(I * (ν * Multiplicative.toAdd t)))
  map_one' := by simp
  map_mul' a b := by
    rw [← Complex.exp_add]
    congr 1
    simp only [toAdd_mul]
    push_cast
    ring

theorem chi_injective : Function.Injective chi := by
  intro ν ν' h
  by_contra hne
  have hd : ν - ν' ≠ 0 := sub_ne_zero.mpr hne
  have h1 := DFunLike.congr_fun h (Multiplicative.ofAdd (Real.pi / (ν - ν')))
  simp only [chi, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at h1
  push_cast at h1
  have h2 : exp (-(I * (ν * (Real.pi / (ν - ν')))) - -(I * (ν' * (Real.pi / (ν - ν'))))) = 1 := by
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  have h3 : -(I * (ν * (Real.pi / (ν - ν')))) - -(I * (ν' * (Real.pi / (ν - ν')))) =
      -(Real.pi * I) := by
    have : ((ν : ℂ) - ν') ≠ 0 := by exact_mod_cast hd
    field_simp
    ring
  rw [h3, Complex.exp_neg, Complex.exp_pi_mul_I] at h2
  norm_num at h2

theorem dot_injective (ω : Fin k → ℝ) (hω : LinearIndependent ℤ ω) :
    Function.Injective (dot ω) := by
  intro r r' h
  have hz := Fintype.linearIndependent_iff.mp hω (fun i => (r i : ℤ) - r' i) (by
    simp only [dot] at h
    simp only [zsmul_eq_mul, Int.cast_sub, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib]
    linarith)
  ext i
  have := hz i
  omega

/-- **Exponential sums vanish only for the zero polynomial.** -/
theorem eq_zero_of_eval_zt (ω : Fin k → ℝ) (hω : Function.Injective (dot ω))
    (p : MvPolynomial (Fin k) ℂ) (h : ∀ t, eval (zt ω t) p = 0) : p = 0 := by
  classical
  have li := (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp
    (fun r : Fin k →₀ ℕ => chi (dot ω r)) (chi_injective.comp hω)
  rw [linearIndependent_iff'] at li
  have hc := li p.support (fun r => p.coeff r) (by
    funext t
    have := h (Multiplicative.toAdd t)
    rw [eval_zt] at this
    simpa [chi, Finset.sum_apply, mul_comm] using this)
  ext r
  by_cases hr : r ∈ p.support
  · simpa using hc r hr
  · simpa using hr

/-- **The frequency lattice.** -/
theorem exists_lattice {J : Type*} [Fintype J] (lam : J → ℝ) :
    ∃ (k : ℕ) (ω : Fin k → ℝ) (e : J → (Fin k →₀ ℕ)) (c : ℝ),
      LinearIndependent ℤ ω ∧ ∀ j, lam j = dot ω (e j) + c := by
  classical
  set M := Submodule.span ℤ (Set.range lam)
  have : Module.Finite ℤ M := Module.Finite.span_of_finite ℤ (Set.finite_range lam)
  let b := Module.finBasis ℤ M
  let ω : Fin (Module.finrank ℤ M) → ℝ := fun i => (b i : ℝ)
  let n : J → Fin (Module.finrank ℤ M) → ℤ := fun j =>
    b.repr ⟨lam j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hn : ∀ j, lam j = ∑ i, (n j i : ℝ) * ω i := by
    intro j
    have := congrArg (fun x : M => (x : ℝ)) (b.sum_repr ⟨lam j, Submodule.subset_span ⟨j, rfl⟩⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, zsmul_eq_mul] at this
    exact this.symm
  let N : Fin (Module.finrank ℤ M) → ℤ := fun i => ∑ j, |n j i|
  have hN : ∀ j i, 0 ≤ n j i + N i := by
    intro j i
    have : |n j i| ≤ N i :=
      Finset.single_le_sum (f := fun j => |n j i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have := neg_abs_le (n j i)
    linarith
  let e : J → (Fin (Module.finrank ℤ M) →₀ ℕ) := fun j =>
    Finsupp.equivFunOnFinite.symm fun i => (n j i + N i).toNat
  refine ⟨Module.finrank ℤ M, ω, e, -∑ i, (N i : ℝ) * ω i, ?_, fun j => ?_⟩
  · exact b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  · rw [hn j]
    simp only [dot, e, Finsupp.coe_equivFunOnFinite_symm]
    have : ∀ i, (((n j i + N i).toNat : ℕ) : ℝ) = (n j i : ℝ) + N i := by
      intro i
      have h := Int.toNat_of_nonneg (hN j i)
      exact_mod_cast h
    simp only [this, add_mul, Finset.sum_add_distrib]
    ring

end ProductTrajectory
