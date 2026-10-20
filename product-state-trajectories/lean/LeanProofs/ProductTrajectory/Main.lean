import Mathlib
import LeanProofs.ProductTrajectory.Core
import LeanProofs.ProductTrajectory.Characters

/-!
# Product trajectories (Physics SE 816017), part 5: the main theorem

A state of a bipartite system, written as an `ι × κ` matrix, evolves as
`ψ(t) = ∑ⱼ e^{-iλⱼt} vⱼ` with the `vⱼ` pairwise orthogonal (Frobenius inner product). This is
what any time-independent Hamiltonian produces from any initial state (`vⱼ` = the components of
the initial state along an orthonormal eigenbasis, `λⱼ` the eigenvalues; repeats allowed).

**Theorem.** If `ψ(t)` is a product `a(t) bᵀ(t)` for every real `t`, then it is a product of two
exponential sums with pairwise orthogonal coefficient vectors:
`ψ(t) = (∑_{μ∈S} e^{-if_μ t} x_μ)(∑_{ν∈T} e^{-ig_ν t} y_ν)ᵀ` for all `t`.

Orthogonality is what makes each factor a trajectory of its own time-independent Hamiltonian,
`h_A = ∑_μ f_μ x_μ x_μ† / ‖x_μ‖²` and `h_B` likewise (spectral theorem).
-/

namespace ProductTrajectory

open MvPolynomial Complex Matrix

theorem main {ι κ J : Type*} [Fintype ι] [Fintype κ] [Fintype J]
    (lam : J → ℝ) (v : J → Matrix ι κ ℂ)
    (horth : ∀ j j', j ≠ j' → ∑ i, ∑ l, star (v j i l) * v j' i l = 0)
    (hprod : ∀ t : ℝ, ∃ (a : ι → ℂ) (b : κ → ℂ),
      ∑ j, exp (-(I * (lam j * t))) • v j = vecMulVec a b) :
    ∃ (k : ℕ) (S T : Finset (Fin k →₀ ℕ)) (x : (Fin k →₀ ℕ) → ι → ℂ) (y : (Fin k →₀ ℕ) → κ → ℂ)
      (f g : (Fin k →₀ ℕ) → ℝ),
      (∀ μ ν, μ ≠ ν → ∑ i, star (x μ i) * x ν i = 0) ∧
      (∀ μ ν, μ ≠ ν → ∑ l, star (y μ l) * y ν l = 0) ∧
      ∀ t : ℝ, ∑ j, exp (-(I * (lam j * t))) • v j =
        vecMulVec (∑ μ ∈ S, exp (-(I * (f μ * t))) • x μ)
          (∑ ν ∈ T, exp (-(I * (g ν * t))) • y ν) := by
  classical
  obtain ⟨k, ω, e, c, hω, hlam⟩ := exists_lattice lam
  have hinj := dot_injective ω hω
  -- the polynomial matrix
  let F : Matrix ι κ (MvPolynomial (Fin k) ℂ) := fun i l => ∑ j, monomial (e j) (v j i l)
  have hcoeff : ∀ i l s, (F i l).coeff s = ∑ j, if e j = s then v j i l else 0 := by
    intro i l s
    simp [F, coeff_monomial]
  have heval : ∀ t i l, eval (zt ω t) (F i l) = ∑ j, v j i l * exp (-(I * (dot ω (e j) * t))) := by
    intro t i l
    simp [F, map_sum, eval_zt_monomial]
  have hψ : ∀ (t : ℝ) i l, (∑ j, exp (-(I * (lam j * t))) • v j) i l =
      exp (-(I * (c * t))) * eval (zt ω t) (F i l) := by
    intro t i l
    rw [heval, Finset.mul_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, hlam j]
    rw [show exp (-(I * (((dot ω (e j) + c : ℝ) : ℂ) * t))) =
        exp (-(I * (c * t))) * exp (-(I * (dot ω (e j) * t))) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  -- minors vanish
  have hminor : ∀ i i' l l', F i l * F i' l' = F i l' * F i' l := by
    intro i i' l l'
    rw [← sub_eq_zero]
    refine eq_zero_of_eval_zt ω hinj _ fun t => ?_
    obtain ⟨a, b, hab⟩ := hprod t
    have h1 : ∀ i l, exp (-(I * (c * t))) * eval (zt ω t) (F i l) = a i * b l := by
      intro i l
      rw [← hψ, hab, vecMulVec_apply]
    have hE : exp (-(I * (c * t))) ≠ 0 := Complex.exp_ne_zero _
    have key : exp (-(I * (c * t))) ^ 2 *
        eval (zt ω t) (F i l * F i' l' - F i l' * F i' l) = 0 := by
      simp only [map_sub, map_mul]
      linear_combination (exp (-(I * (c * t))) * eval (zt ω t) (F i' l')) * h1 i l +
        (a i * b l) * h1 i' l' - (exp (-(I * (c * t))) * eval (zt ω t) (F i' l)) * h1 i l' -
        (a i * b l') * h1 i' l
    exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 hE)
  -- coefficient matrices are orthogonal
  have horthF : ∀ s s', s ≠ s' → ∑ i, ∑ l, star ((F i l).coeff s) * (F i l).coeff s' = 0 := by
    intro s s' hss'
    have hswap : ∀ X : ι → κ → J → J → ℂ,
        ∑ i, ∑ l, ∑ j, ∑ j', X i l j j' = ∑ j, ∑ j', ∑ i, ∑ l, X i l j j' := by
      intro X
      calc ∑ i, ∑ l, ∑ j, ∑ j', X i l j j' = ∑ i, ∑ j, ∑ l, ∑ j', X i l j j' :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ j, ∑ i, ∑ l, ∑ j', X i l j j' := Finset.sum_comm
        _ = ∑ j, ∑ i, ∑ j', ∑ l, X i l j j' :=
            Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ j, ∑ j', ∑ i, ∑ l, X i l j j' := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    simp only [hcoeff, star_sum, Finset.sum_mul_sum]
    rw [hswap]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' _ => ?_
    by_cases hj : e j = s
    · by_cases hj' : e j' = s'
      · have hne : j ≠ j' := fun h => hss' (by rw [← hj, ← hj', h])
        simpa [hj, hj'] using horth j j' hne
      · simp [hj']
    · simp [hj]
  obtain ⟨α, β, hF, hα, hβ⟩ := core F hminor horthF
  -- read off the two exponential sums
  let S : Finset (Fin k →₀ ℕ) := Finset.univ.biUnion fun i => (α i).support
  let T : Finset (Fin k →₀ ℕ) := Finset.univ.biUnion fun l => (β l).support
  have hevS : ∀ t i, eval (zt ω t) (α i) =
      ∑ μ ∈ S, (α i).coeff μ * exp (-(I * (dot ω μ * t))) := by
    intro t i
    rw [eval_zt]
    refine Finset.sum_subset (fun μ hμ => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hμ⟩) ?_
    intro μ _ hμ
    simp [MvPolynomial.notMem_support_iff.mp hμ]
  have hevT : ∀ t l, eval (zt ω t) (β l) =
      ∑ ν ∈ T, (β l).coeff ν * exp (-(I * (dot ω ν * t))) := by
    intro t l
    rw [eval_zt]
    refine Finset.sum_subset (fun ν hν => Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, hν⟩) ?_
    intro ν _ hν
    simp [MvPolynomial.notMem_support_iff.mp hν]
  refine ⟨k, S, T, fun μ i => (α i).coeff μ, fun ν l => (β l).coeff ν,
    fun μ => dot ω μ + c, fun ν => dot ω ν, hα, hβ, fun t => ?_⟩
  have hexp : ∀ μ : Fin k →₀ ℕ, exp (-(I * (((dot ω μ + c : ℝ) : ℂ) * t))) =
      exp (-(I * (c * t))) * exp (-(I * (dot ω μ * t))) := fun μ => by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  ext i l
  have hFil : F i l = α i * β l := by rw [hF, vecMulVec_apply]
  rw [hψ, vecMulVec_apply, hFil, map_mul, hevS, hevT]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hexp]
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end ProductTrajectory
