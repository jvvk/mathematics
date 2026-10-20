import Mathlib
import LeanProofs.ProductTrajectory.Characters

/-!
# Product trajectories (Physics SE 816017), part 6: constant entanglement is not enough

The Heisenberg exchange in a uniform field,
`H = (X⊗X + Y⊗Y + Z⊗Z)/2 - (Z⊗1 + 1⊗Z)/2 + 3/2`, started from
`ψ₀ = -|00⟩ + (1+i)|01⟩ + (i-1)|10⟩ + |11⟩`, has trajectory (as a `2 × 2` matrix, `z = e^{-it}`)
`M(t) = !![-z, 1 + i z²; i z² - 1, z³]`.

* `H_mulVec`: the four frequency components are eigenvectors of `H` with eigenvalues
  `0, 1, 2, 3`, and
  `M_eq_sum`: `M(t) = ∑_μ e^{-iμt} V_μ` with the `V_μ` pairwise orthogonal (`V_orth`).
* `det_M`, `normSq_M`: `det M(t) = 1` and `‖M(t)‖² = 6` for all `t`: the Schmidt coefficients
  are constant.
* `not_local`: there are no Hermitian `A, C` with `M(t) = e^{-itA} M(0) e^{-itC}` for all `t`.
-/

namespace ProductTrajectory.Heisenberg

open Complex Matrix

/-- `z = e^{-it}`. -/
noncomputable def zz (t : ℝ) : ℂ := exp (-(I * t))

/-- The trajectory in matrix form. -/
noncomputable def Mt (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-zz t, 1 + I * zz t ^ 2; I * zz t ^ 2 - 1, zz t ^ 3]

theorem zz_pow (t : ℝ) (k : ℕ) : zz t ^ k = exp (-(I * ((k : ℝ) * t))) := by
  rw [zz, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem normSq_zz (t : ℝ) : normSq (zz t) = 1 := by
  rw [zz, normSq_eq_norm_sq, norm_exp]
  simp

theorem det_M (t : ℝ) : (Mt t).det = 1 := by
  rw [Mt, det_fin_two_of]
  ring_nf
  rw [I_sq]
  ring

/-- The squared Frobenius norm is `6` at all times. -/
theorem normSq_M (t : ℝ) : ∑ i, ∑ j, normSq (Mt t i j) = 6 := by
  have hz := normSq_zz t
  have h2 : normSq (zz t ^ 2) = 1 := by rw [map_pow, hz, one_pow]
  have h3 : normSq (zz t ^ 3) = 1 := by rw [map_pow, hz, one_pow]
  have hsum : normSq (1 + I * zz t ^ 2) + normSq (I * zz t ^ 2 - 1) = 4 := by
    have := normSq_add (I * zz t ^ 2) 1
    have h' := normSq_sub (I * zz t ^ 2) 1
    rw [normSq_mul, normSq_I, h2] at this h'
    rw [add_comm (1 : ℂ)]
    simp only [map_one, one_mul] at this h'
    linarith
  simp only [Mt, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, Matrix.cons_val_zero]
  rw [normSq_neg, hz, h3]
  linarith

/-- The frequency components (eigenvectors of `H`). -/
def V : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; -1, 0]
  | 1 => !![-1, 0; 0, 0]
  | 2 => !![0, I; I, 0]
  | 3 => !![0, 0; 0, 1]

theorem M_eq_sum (t : ℝ) : Mt t = ∑ μ : Fin 4, zz t ^ (μ : ℕ) • V μ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mt, V, Fin.sum_univ_four] <;> ring

theorem V_orth (μ ν : Fin 4) (h : μ ≠ ν) : ∑ i, ∑ j, star (V μ i j) * V ν i j = 0 := by
  fin_cases μ <;> fin_cases ν <;> simp_all [V, Fin.sum_univ_two]

/-- Pauli matrices and the Hamiltonian on `Fin 2 × Fin 2` (index `(i, j)` = `|ij⟩`). -/
def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

noncomputable def Hh : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 2 : ℂ) • (kroneckerMap (· * ·) σx σx + kroneckerMap (· * ·) σy σy +
      kroneckerMap (· * ·) σz σz)
    - (1 / 2 : ℂ) • (kroneckerMap (· * ·) σz 1 + kroneckerMap (· * ·) 1 σz) + (3 / 2 : ℂ) • 1

/-- `V μ` flattened to a vector on `Fin 2 × Fin 2`. -/
def vecV (μ : Fin 4) : Fin 2 × Fin 2 → ℂ := fun p => V μ p.1 p.2

theorem H_mulVec (μ : Fin 4) : Hh *ᵥ vecV μ = (μ : ℂ) • vecV μ := by
  ext ⟨i, j⟩
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    simp [Hh, vecV, V, σx, σy, σz, mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      kroneckerMap_apply, one_apply] <;> ring_nf

/-! ### Non-locality -/

/-- A Hermitian generator evolves by `U · diag(e^{-itλ}) · U*`. -/
theorem exp_hermitian {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (t : ℝ) :
    NormedSpace.exp (-((t : ℂ) * I) • A) =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun k => exp (-(I * ((hA.eigenvalues k) * t)))) *
          star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  have hspec : A = U * diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [U, Function.comp_def] using this
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv hU
  have hunit : IsUnit U := ⟨⟨U, star U, hU', hU⟩, rfl⟩
  have harg : -((t : ℂ) * I) • A =
      U * diagonal (fun k => -((t : ℂ) * I) * ((hA.eigenvalues k : ℝ) : ℂ)) * U⁻¹ := by
    rw [hinv]
    conv_lhs => rw [hspec]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    rfl
  rw [harg, Matrix.exp_conj _ _ hunit, Matrix.exp_diagonal, Pi.exp_def, hinv,
    ← Complex.exp_eq_exp_ℂ]
  have hf : (fun i => cexp (-((t : ℂ) * I) * ((hA.eigenvalues i : ℝ) : ℂ))) =
      fun k => cexp (-(I * (((hA.eigenvalues k : ℝ) : ℂ) * (t : ℂ)))) := by
    funext k
    congr 1
    ring
  rw [hf]

/-- `det e^{-itA} = e^{-it tr A}` for Hermitian `A` (via the spectral form). -/
theorem det_exp_hermitian {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (t : ℝ) :
    (NormedSpace.exp (-((t : ℂ) * I) • A)).det =
      exp (-(I * ((∑ k, hA.eigenvalues k) * t))) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  rw [exp_hermitian hA t, det_mul, det_mul, det_diagonal, mul_right_comm, ← det_mul, hU', det_one,
    one_mul, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- Entries of `e^{-itA} M₀ e^{-itC}` are combinations of the characters at `a_k + c_l`. -/
theorem entries_local {n : Type*} [Fintype n] [DecidableEq n] {A C : Matrix n n ℂ}
    (hA : A.IsHermitian) (hC : C.IsHermitian) (M₀ : Matrix n n ℂ) :
    ∃ W : n → n → n × n → ℂ, ∀ (t : ℝ) (i j : n),
      (NormedSpace.exp (-((t : ℂ) * I) • A) * M₀ * NormedSpace.exp (-((t : ℂ) * I) • C)) i j =
        ∑ p : n × n, W i j p * exp (-(I * ((hA.eigenvalues p.1 + hC.eigenvalues p.2) * t))) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  set V : Matrix n n ℂ := (hC.eigenvectorUnitary : Matrix n n ℂ)
  set N := star U * M₀ * V
  refine ⟨fun i j p => U i p.1 * N p.1 p.2 * star V p.2 j, fun t i j => ?_⟩
  rw [exp_hermitian hA t, exp_hermitian hC t]
  have : U * diagonal (fun k => exp (-(I * ((hA.eigenvalues k) * t)))) * star U * M₀ *
      (V * diagonal (fun k => exp (-(I * ((hC.eigenvalues k) * t)))) * star V) =
      U * diagonal (fun k => exp (-(I * ((hA.eigenvalues k) * t)))) * N *
        diagonal (fun k => exp (-(I * ((hC.eigenvalues k) * t)))) * star V := by
    simp only [N, Matrix.mul_assoc]
  rw [this, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hexp : exp (-(I * (((hA.eigenvalues k : ℂ) + (hC.eigenvalues l : ℂ)) * t))) =
      exp (-(I * ((hA.eigenvalues k) * t))) * exp (-(I * ((hC.eigenvalues l) * t))) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [hexp]
  ring

/-- A combination of distinct characters with nonzero coefficients, equal to a combination of
characters indexed by `P` with frequencies `f`, uses only frequencies in `f '' P`. -/
theorem freq_mem {ι : Type*} (P : Finset ι) (f : ι → ℝ) (w : ι → ℂ) (Nν : Finset ℝ) (d : ℝ → ℂ)
    (hd : ∀ ν ∈ Nν, d ν ≠ 0)
    (h : ∀ t : ℝ, ∑ ν ∈ Nν, d ν * exp (-(I * (ν * t))) = ∑ p ∈ P, w p * exp (-(I * (f p * t)))) :
    Nν ⊆ P.image f := by
  classical
  intro ν₀ hν₀
  by_contra hout
  have li := (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp chi chi_injective
  rw [linearIndependent_iff'] at li
  set T := P.image f
  set g : ℝ → ℂ := fun s => (if s ∈ Nν then d s else 0) - ∑ p ∈ P with f p = s, w p
  have hsum : ∑ s ∈ Nν ∪ T, g s • (⇑(chi s) : Multiplicative ℝ → ℂ) = 0 := by
    funext x
    have hx := h (Multiplicative.toAdd x)
    have hR : ∑ p ∈ P, w p * exp (-(I * (f p * Multiplicative.toAdd x))) =
        ∑ s ∈ Nν ∪ T, (∑ p ∈ P with f p = s, w p) * exp (-(I * (s * Multiplicative.toAdd x))) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := Nν ∪ T)
        (fun p hp => Finset.mem_union_right _ (Finset.mem_image_of_mem f hp))]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.mp hp).2]
    have hL : ∑ ν ∈ Nν, d ν * exp (-(I * (ν * Multiplicative.toAdd x))) =
        ∑ s ∈ Nν ∪ T, (if s ∈ Nν then d s else 0) * exp (-(I * (s * Multiplicative.toAdd x))) := by
      rw [← Finset.sum_subset (Finset.subset_union_left) (fun s _ hs => by simp [hs])]
      exact Finset.sum_congr rfl fun s hs => by simp [hs]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, chi,
      MonoidHom.coe_mk, OneHom.coe_mk, g, sub_mul, Finset.sum_sub_distrib]
    rw [← hL, ← hR, hx, sub_self]
  have := li (Nν ∪ T) g hsum ν₀ (Finset.mem_union_left _ hν₀)
  have hfil : (P.filter fun p => f p = ν₀) = ∅ := by
    ext p
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro hp hfp
    exact hout (hfp ▸ Finset.mem_image_of_mem f hp)
  simp only [g, hν₀, ite_true, hfil, Finset.sum_empty, sub_zero] at this
  exact hd ν₀ hν₀ this

theorem Mt_zero : Mt 0 = !![-1, 1 + I; I - 1, 1] := by
  simp [Mt, zz]

/-- **No time-independent local generator.** -/
theorem not_local : ¬ ∃ A C : Matrix (Fin 2) (Fin 2) ℂ, A.IsHermitian ∧ C.IsHermitian ∧
    ∀ t : ℝ, Mt t = NormedSpace.exp (-((t : ℂ) * I) • A) * Mt 0 *
      NormedSpace.exp (-((t : ℂ) * I) • C) := by
  classical
  rintro ⟨A, C, hA, hC, h⟩
  set a := hA.eigenvalues
  set c := hC.eigenvalues
  -- the determinant forces tr A + tr C = 0
  have hσ : (∑ k, a k) + (∑ k, c k) = 0 := by
    apply chi_injective
    refine MonoidHom.ext fun x => ?_
    have hd := congrArg Matrix.det (h (Multiplicative.toAdd x))
    rw [det_M, det_mul, det_mul, det_M, det_exp_hermitian hA, det_exp_hermitian hC, mul_one,
      ← Complex.exp_add] at hd
    change exp (-(I * ((((∑ k, a k) + (∑ k, c k) : ℝ) : ℂ) * Multiplicative.toAdd x))) =
      exp (-(I * (((0 : ℝ) : ℂ) * Multiplicative.toAdd x)))
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, neg_zero, Complex.exp_zero]
    rw [hd]
    congr 1
    simp only [a, c]
    push_cast
    ring
  -- every entry is a combination of characters at a_k + c_l
  obtain ⟨W, hW⟩ := entries_local hA hC (Mt 0)
  set f : Fin 2 × Fin 2 → ℝ := fun p => a p.1 + c p.2
  have entry : ∀ (i j : Fin 2) (Nν : Finset ℝ) (d : ℝ → ℂ), (∀ ν ∈ Nν, d ν ≠ 0) →
      (∀ t : ℝ, Mt t i j = ∑ ν ∈ Nν, d ν * exp (-(I * (ν * t)))) → Nν ⊆ Finset.univ.image f := by
    intro i j Nν d hd hM
    refine freq_mem Finset.univ f (W i j) Nν d hd fun t => ?_
    rw [← hM t, h t, hW t i j]
    simp [f, a, c]
  have h1 : ({1} : Finset ℝ) ⊆ Finset.univ.image f :=
    entry 0 0 {1} (fun _ => -1) (by simp) fun t => by
      simp [Mt, zz]
  have h3 : ({3} : Finset ℝ) ⊆ Finset.univ.image f :=
    entry 1 1 {3} (fun _ => 1) (by simp) fun t => by
      simp [Mt, zz_pow]
  have h02 : ({0, 2} : Finset ℝ) ⊆ Finset.univ.image f :=
    entry 0 1 {0, 2} (fun ν => if ν = 0 then 1 else I)
      (by intro ν _; split_ifs <;> simp [I_ne_zero])
      fun t => by
        rw [Finset.sum_pair (by norm_num)]
        simp [Mt, zz_pow]
  -- the frequency set is symmetric under negation
  have hsym : ∀ s ∈ Finset.univ.image f, -s ∈ Finset.univ.image f := by
    intro s hs
    obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp hs
    refine Finset.mem_image.mpr ⟨⟨i.rev, j.rev⟩, Finset.mem_univ _, ?_⟩
    simp only [f]
    simp only [Fin.sum_univ_two] at hσ
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  have hsub : ({0, 1, 2, 3, -1, -2, -3} : Finset ℝ) ⊆ Finset.univ.image f := by
    intro x hx
    have m1 := h1 (Finset.mem_singleton_self 1)
    have m3 := h3 (Finset.mem_singleton_self 3)
    have m0 := h02 (by simp : (0 : ℝ) ∈ ({0, 2} : Finset ℝ))
    have m2 := h02 (by simp : (2 : ℝ) ∈ ({0, 2} : Finset ℝ))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m0
    · exact m1
    · exact m2
    · exact m3
    · exact hsym _ m1
    · exact hsym _ m2
    · exact hsym _ m3
  have hcard := Finset.card_le_card hsub
  have hT : (Finset.univ.image f).card ≤ 4 := (Finset.card_image_le).trans (by simp)
  have h7 : ({0, 1, 2, 3, -1, -2, -3} : Finset ℝ).card = 7 := by
    rw [Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num),
      Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num),
      Finset.card_insert_of_notMem (by norm_num), Finset.card_pair (by norm_num)]
  omega

end ProductTrajectory.Heisenberg
