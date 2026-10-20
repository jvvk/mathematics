import Mathlib
import LeanProofs.ProductTrajectory.ExpSums
import LeanProofs.ProductTrajectory.SO4
import LeanProofs.ProductTrajectory.Heisenberg

/-!
# Product trajectories (Physics SE 816017), part 9: two qubits that stay maximally entangled

`maxent`: let `N(t) = ∑_{s ∈ S} e^{-ist} W_s` with distinct frequencies, nonzero pairwise orthogonal
`W_s` (any Hamiltonian trajectory has this form), and suppose `N(t) N(t)ᴴ` is a multiple of the
  identity
for every `t` (the state stays maximally entangled). Then `N(t) = e^{-itA} N(0) e^{-itC}` for fixed
Hermitian `A, C`, i.e. the trajectory has a time-independent local generator.
-/

namespace ProductTrajectory.MaxEnt

open Complex Matrix ProductTrajectory.SO4

/-- Spectral form of a Hermitian `2 × 2` matrix. -/
theorem spec {A : M2} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : M2) * diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : M2) := by
  have := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  simpa [Function.comp_def] using this

/-- An eigenvector of `X ↦ A X + X C` with eigenvalue `s` evolves by the phase `e^{-ist}`. -/
theorem evolve_eigen {A C : M2} (hA : A.IsHermitian) (hC : C.IsHermitian) (X : M2) (s : ℝ)
    (hX : A * X + X * C = (s : ℂ) • X) (t : ℝ) :
    NormedSpace.exp (-((t : ℂ) * I) • A) * X * NormedSpace.exp (-((t : ℂ) * I) • C) =
      ch s t • X := by
  set U : M2 := (hA.eigenvectorUnitary : M2)
  set V : M2 := (hC.eigenvectorUnitary : M2)
  set a := hA.eigenvalues
  set c := hC.eigenvalues
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hV : star V * V = 1 := Unitary.star_mul_self_of_mem hC.eigenvectorUnitary.2
  have hV' : V * star V = 1 := Unitary.mul_star_self_of_mem hC.eigenvectorUnitary.2
  set X' := star U * X * V
  have hXback : X = U * X' * star V := by
    simp only [X', ← Matrix.mul_assoc, hU', Matrix.one_mul]
    rw [Matrix.mul_assoc, hV', Matrix.mul_one]
  -- the eigen-equation in the eigenbases
  have hdiag : diagonal (fun k => ((a k : ℝ) : ℂ)) * X' + X' * diagonal (fun l => ((c l : ℝ) : ℂ)) =
      (s : ℂ) • X' := by
    calc diagonal (fun k => ((a k : ℝ) : ℂ)) * X' + X' * diagonal (fun l => ((c l : ℝ) : ℂ))
        = star U * A * X * V + star U * X * C * V := by
          congr 1
          · conv_rhs => rw [spec hA]
            simp only [X', U, a, ← Matrix.mul_assoc, hU, Matrix.one_mul]
          · conv_rhs => rw [spec hC]
            simp only [X', V, c, Matrix.mul_assoc, hV, Matrix.mul_one]
      _ = star U * (A * X + X * C) * V := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = (s : ℂ) • X' := by
          rw [hX, Matrix.mul_smul, Matrix.smul_mul]
  have hent : ∀ k l, ((a k + c l : ℝ) : ℂ) * X' k l = (s : ℂ) * X' k l := by
    intro k l
    have := congrFun (congrFun hdiag k) l
    simp [Matrix.add_apply, diagonal_mul, mul_diagonal] at this
    push_cast
    linear_combination this
  rw [Heisenberg.exp_hermitian hA t, Heisenberg.exp_hermitian hC t]
  have hmid : diagonal (fun k => exp (-(I * ((a k) * t)))) * X' *
      diagonal (fun l => exp (-(I * ((c l) * t)))) = ch s t • X' := by
    ext k l
    simp only [mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    by_cases h0 : X' k l = 0
    · simp [h0]
    · have hs : a k + c l = s := by
        have := hent k l
        exact_mod_cast mul_right_cancel₀ h0 this
      rw [← hs, ← ch_mul]
      simp only [ch]
      ring
  calc U * diagonal (fun k => exp (-(I * ((a k) * t)))) * star U * X *
        (V * diagonal (fun l => exp (-(I * ((c l) * t)))) * star V)
      = U * (diagonal (fun k => exp (-(I * ((a k) * t)))) * X' *
          diagonal (fun l => exp (-(I * ((c l) * t))))) * star V := by
        simp only [X', Matrix.mul_assoc]
    _ = ch s t • X := by
        rw [hmid, Matrix.mul_smul, Matrix.smul_mul, ← hXback]

/-! ### Inner-product helpers -/

theorem ip_conj (X Y : M2) : star (ip X Y) = ip Y X := by
  simp only [ip, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem ip_add_left (X Y Z : M2) : ip (X + Y) Z = ip X Z + ip Y Z := by
  simp only [ip, Matrix.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem ip_smul_left (c : ℂ) (X Y : M2) : ip (c • X) Y = star c * ip X Y := by
  simp only [ip, Matrix.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem ip_self (X : M2) : ip X X = ((∑ i, ∑ j, normSq (X i j) : ℝ) : ℂ) := by
  simp only [ip, ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, ← Complex.mul_conj]; rfl

theorem ip_self_ne_zero {X : M2} (hX : X ≠ 0) : ip X X ≠ 0 := by
  rw [ip_self]
  intro h
  apply hX
  have h' : ∑ i, ∑ j, normSq (X i j) = 0 := by exact_mod_cast h
  ext i j
  have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
    fun j _ => normSq_nonneg (X i j))).mp h' i (Finset.mem_univ _)
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => normSq_nonneg (X i j))).mp hij j
    (Finset.mem_univ _)
  simpa using this

theorem star_ip_self (X : M2) : star (ip X X) = ip X X := by
  rw [ip_self]; simp

theorem tau_sum {ι : Type*} (s : Finset ι) (X : ι → M2) : tau (∑ k ∈ s, X k) = ∑ k ∈ s,
    tau (X k) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext i j; fin_cases i <;> fin_cases j <;> simp [tau]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tau_add, ih]

/-! ### The generator -/

/-- The candidate generator built from orthogonal components. -/
noncomputable def Tgen (S : Finset ℝ) (κ : ℝ) (W : ℝ → M2) (X : M2) : M2 :=
  ∑ s ∈ S, ((((s - κ / 2 : ℝ) : ℂ) * ip (W s) X) / ip (W s) (W s)) • W s

theorem Tgen_add (S : Finset ℝ) (κ : ℝ) (W : ℝ → M2) (X Y : M2) :
    Tgen S κ W (X + Y) = Tgen S κ W X + Tgen S κ W Y := by
  simp only [Tgen, ip_add_right, mul_add, add_div, add_smul, Finset.sum_add_distrib]

theorem Tgen_smul (S : Finset ℝ) (κ : ℝ) (W : ℝ → M2) (c : ℂ) (X : M2) :
    Tgen S κ W (c • X) = c • Tgen S κ W X := by
  simp only [Tgen, ip_smul_right, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  ring

theorem Tgen_sum {ι : Type*} (S : Finset ℝ) (κ : ℝ) (W : ℝ → M2) (u : Finset ι) (c : ι → ℂ)
    (X : ι → M2) : Tgen S κ W (∑ k ∈ u, c k • X k) = ∑ k ∈ u, c k • Tgen S κ W (X k) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [Tgen, ip]
  | insert a u ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Tgen_add, Tgen_smul, ih]

theorem Tgen_eig (S : Finset ℝ) (κ : ℝ) (W : ℝ → M2) (hW : ∀ s ∈ S, W s ≠ 0)
    (horth : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → ip (W s) (W s') = 0) (s₀ : ℝ) (h₀ : s₀ ∈ S) :
    Tgen S κ W (W s₀) = (((s₀ - κ / 2 : ℝ) : ℂ)) • W s₀ := by
  rw [Tgen, Finset.sum_eq_single s₀ (fun s hs hne => by rw [horth s hs s₀ h₀ hne]; simp)
    (fun h => absurd h₀ h)]
  rw [mul_div_assoc, div_self (ip_self_ne_zero (hW s₀ h₀)), mul_one]

/-- **The generator is local.** -/
theorem generator (S : Finset ℝ) (κ : ℝ) (W : ℝ → M2) (hW : ∀ s ∈ S, W s ≠ 0)
    (horth : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → ip (W s) (W s') = 0)
    (hpair : ∀ s ∈ S, κ - s ∈ S ∧ tau (W (κ - s)) = W s) :
    ∃ A C : M2, A.IsHermitian ∧ C.IsHermitian ∧
      ∀ s ∈ S, A * W s + W s * C = (((s - κ / 2 : ℝ) : ℂ)) • W s := by
  set T := Tgen S κ W
  -- matrix entries of T in the basis E
  set m : Fin 4 → Fin 4 → ℂ := fun a b => ip (E a) (T (E b))
  have hm_expand : ∀ a b, m a b = ∑ s ∈ S, (((s - κ / 2 : ℝ) : ℂ) * ip (W s) (E b) /
      ip (W s) (W s)) * ip (E a) (W s) := by
    intro a b
    simp only [m, T, Tgen, ip_sum_right, ip_smul_right]
  -- Hermitian
  have hherm : ∀ a b, m a b = star (m b a) := by
    intro a b
    rw [hm_expand, hm_expand, star_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [star_mul', star_div₀, star_mul', star_ip_self, ip_conj, ip_conj]
    simp only [Complex.star_def, conj_ofReal]
    ring
  -- purely imaginary, via the quaternion pairing s ↦ κ - s
  have himag : ∀ a b, m a b = -star (m a b) := by
    intro a b
    set term : ℝ → ℂ := fun s => (((s - κ / 2 : ℝ) : ℂ) * ip (W s) (E b) / ip (W s) (W s)) *
      ip (E a) (W s)
    have hterm : ∀ s ∈ S, term s = -star (term (κ - s)) := by
      intro s hs
      obtain ⟨-, hp⟩ := hpair s hs
      simp only [term]
      rw [← hp, ← tau_E b, ← tau_E a, ip_tau, ip_tau, ip_tau, tau_E, tau_E, star_ip_self]
      rw [star_mul', star_div₀, star_mul', star_ip_self]
      simp only [Complex.star_def, conj_ofReal]
      push_cast
      ring
    have hsum : ∑ s ∈ S, term s = ∑ s ∈ S, -star (term s) := by
      rw [Finset.sum_congr rfl hterm]
      exact Finset.sum_nbij' (fun s => κ - s) (fun s => κ - s) (fun s hs => (hpair s hs).1)
        (fun s hs => (hpair s hs).1) (fun s _ => by ring) (fun s _ => by ring) (fun s _ => rfl)
    calc m a b = ∑ s ∈ S, term s := hm_expand a b
      _ = ∑ s ∈ S, -star (term s) := hsum
      _ = -star (∑ s ∈ S, term s) := by rw [star_sum, Finset.sum_neg_distrib]
      _ = -star (m a b) := by rw [hm_expand a b]
  -- the real antisymmetric matrix ω
  set ω : Fin 4 → Fin 4 → ℝ := fun a b => (m a b).im / 2
  have hm_eq : ∀ a b, m a b / 2 = I * (ω a b : ℂ) := by
    intro a b
    have hre : (m a b).re = 0 := by
      have := congrArg Complex.re (himag a b)
      simp at this
      linarith
    apply Complex.ext <;> simp [ω, hre]
  have hanti : ∀ a b, ω a b = -ω b a := by
    intro a b
    have := congrArg Complex.im (hherm a b)
    simp only [ω, Complex.star_def, conj_im] at this ⊢
    linarith
  refine ⟨Aof ω, Cof ω, Aof_herm ω, Cof_herm ω, fun s hs => ?_⟩
  have hTX : ∀ X : M2, T X = Aof ω * X + X * Cof ω := by
    intro X
    have hb : ∀ b, T (E b) = Aof ω * E b + E b * Cof ω := by
      intro b
      rw [← split_basis ω hanti b]
      conv_lhs => rw [expand (T (E b))]
      exact Finset.sum_congr rfl fun a _ => by rw [← hm_eq]
    conv_lhs => rw [expand X]
    change Tgen S κ W _ = _
    rw [Tgen_sum]
    conv_rhs => rw [expand X]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show Tgen S κ W (E b) = Aof ω * E b + E b * Cof ω from hb b, smul_add, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [← hTX]
  exact Tgen_eig S κ W hW horth s hs

/-! ### Assembly -/

theorem ch_zero_left (s : ℝ) : ch s 0 = 1 := by simp [ch]

/-- The trajectory `N(t) = ∑ e^{-ist} W_s`. -/
noncomputable def Nt (S : Finset ℝ) (W : ℝ → M2) (t : ℝ) : M2 := ∑ s ∈ S, ch s t • W s

theorem ip_sum_left {ι : Type*} (u : Finset ι) (X : ι → M2) (Y : M2) :
    ip (∑ k ∈ u, X k) Y = ∑ k ∈ u, ip (X k) Y := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [ip]
  | insert a u ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ip_add_left, ih]

theorem star_ch_mul_ch (s t : ℝ) : star (ch s t) * ch s t = 1 := by
  rw [Complex.star_def, conj_ch, ch_mul]; simp [ch]

theorem ip_Nt (S : Finset ℝ) (W : ℝ → M2) (horth : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → ip (W s) (W s') = 0)
    (t : ℝ) : ip (Nt S W t) (Nt S W t) = ∑ s ∈ S, ip (W s) (W s) := by
  simp only [Nt, ip_sum_left, ip_sum_right, ip_smul_left, ip_smul_right]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.sum_eq_single s (fun s' hs' hne => by rw [horth s' hs' s hs hne]; simp)
    (fun h => absurd hs h)]
  linear_combination (ip (W s) (W s)) * star_ch_mul_ch s t

theorem trace_mul_conjTranspose (X : M2) : (X * Xᴴ).trace = ip X X := by
  simp only [trace, diag, Matrix.mul_apply, conjTranspose_apply, ip, Fin.sum_univ_two]
  ring

/-- Grouping a sum by frequency. -/
theorem group_sum (S F : Finset ℝ) (f : ℝ → ℝ) (c : ℝ → ℂ) (hF : ∀ s ∈ S, f s ∈ F) (t : ℝ) :
    ∑ s ∈ S, c s * ch (f s) t = ∑ ν ∈ F, (∑ s ∈ S with f s = ν, c s) * ch ν t := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := F) hF]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [(Finset.mem_filter.mp hs).2]

/-- **Two qubits that stay maximally entangled have a time-independent local generator.** -/
theorem maxent (S : Finset ℝ) (W : ℝ → M2) (hW : ∀ s ∈ S, W s ≠ 0)
    (horth : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → ip (W s) (W s') = 0)
    (hmax : ∀ t : ℝ, ∃ r : ℂ, Nt S W t * (Nt S W t)ᴴ = r • 1) :
    ∃ A C : M2, A.IsHermitian ∧ C.IsHermitian ∧ ∀ t : ℝ,
      Nt S W t = NormedSpace.exp (-((t : ℂ) * I) • A) * Nt S W 0 *
        NormedSpace.exp (-((t : ℂ) * I) • C) := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨0, 0, isHermitian_zero, isHermitian_zero, fun t => ?_⟩
    simp [Nt, hS]
  -- the norm q of the trajectory, and N N* = (q/2) 1
  set q : ℝ := ∑ s ∈ S, ∑ i, ∑ j, normSq (W s i j)
  have hipq : ∀ t, ip (Nt S W t) (Nt S W t) = (q : ℂ) := by
    intro t
    rw [ip_Nt S W horth]
    simp only [q, ofReal_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [ip_self]; push_cast; rfl
  have hq : 0 < q := by
    obtain ⟨s₀, hs₀⟩ := hS
    have h1 : (ip (W s₀) (W s₀)) ≠ 0 := ip_self_ne_zero (hW s₀ hs₀)
    rw [ip_self] at h1
    have hpos : 0 < ∑ i, ∑ j, normSq (W s₀ i j) := lt_of_le_of_ne (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => normSq_nonneg _) (fun h => h1 (by rw [← h]; simp))
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun s => ∑ i, ∑ j, normSq (W s i j))
      (fun s _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => normSq_nonneg _) hs₀)
  have hNN : ∀ t, Nt S W t * (Nt S W t)ᴴ = ((q / 2 : ℝ) : ℂ) • 1 := by
    intro t
    obtain ⟨r, hr⟩ := hmax t
    have htr := congrArg Matrix.trace hr
    rw [trace_mul_conjTranspose, hipq, trace_smul, trace_one] at htr
    simp only [Fintype.card_fin, smul_eq_mul] at htr
    rw [hr]; congr 1; push_cast; linear_combination -htr / 2
  -- |det N(t)|² = (q/2)²
  have hdet_mod : ∀ t, normSq (Nt S W t).det = (q / 2) ^ 2 := by
    intro t
    have h := congrArg Matrix.det (hNN t)
    rw [det_mul, det_conjTranspose, det_smul, det_one, Fintype.card_fin, mul_one] at h
    have : ((normSq (Nt S W t).det : ℝ) : ℂ) = (((q / 2) ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.mul_conj, ← Complex.star_def, h]; push_cast; ring
    exact_mod_cast this
  -- det N(t) as an exponential sum, grouped by frequency
  set mdet : M2 → M2 → ℂ := fun X Y => X 0 0 * Y 1 1 - X 0 1 * Y 1 0
  set D := (S ×ˢ S).image (fun p => p.1 + p.2)
  set dd : ℝ → ℂ := fun e => ∑ p ∈ (S ×ˢ S) with p.1 + p.2 = e, mdet (W p.1) (W p.2)
  have hdet_sum : ∀ t, (Nt S W t).det = ∑ e ∈ D.filter (fun e => dd e ≠ 0), dd e * ch e t := by
    intro t
    rw [Finset.sum_filter_of_ne (fun e _ h => left_ne_zero_of_mul h), det_fin_two]
    have hent : ∀ i j, Nt S W t i j = ∑ s ∈ S, ch s t * W s i j := by
      intro i j; simp [Nt, Matrix.sum_apply]
    have hL : (∑ s ∈ S, ch s t * W s 0 0) * (∑ s ∈ S, ch s t * W s 1 1) -
        (∑ s ∈ S, ch s t * W s 0 1) * (∑ s ∈ S, ch s t * W s 1 0) =
        ∑ p ∈ S ×ˢ S, mdet (W p.1) (W p.2) * ch (p.1 + p.2) t := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib, Finset.sum_product]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s' _ => ?_
      simp only [mdet, ← ch_mul]
      ring
    rw [hent, hent, hent, hent, hL]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℝ × ℝ => p.1 + p.2) (t := D)
      (fun p hp => Finset.mem_image_of_mem _ hp)]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [dd, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(Finset.mem_filter.mp hp).2]
  obtain ⟨κ, hκ⟩ : ∃ κ, D.filter (fun e => dd e ≠ 0) = {κ} := by
    refine const_modulus_single _ dd (fun e he => (Finset.mem_filter.mp he).2) ?_ ((q / 2) ^ 2)
      (fun t => by rw [← hdet_sum]; exact hdet_mod t)
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h0 := hdet_mod 0
    rw [hdet_sum, hne, Finset.sum_empty, map_zero] at h0
    nlinarith
  set δ := dd κ
  have hdetN : ∀ t, (Nt S W t).det = δ * ch κ t := by
    intro t; rw [hdet_sum, hκ, Finset.sum_singleton]
  have hδ : normSq δ = (q / 2) ^ 2 := by
    have := hdet_mod 0; rw [hdetN, ch, normSq_mul] at this
    simpa using this
  have hδ0 : δ ≠ 0 := fun h => by rw [h, map_zero] at hδ; nlinarith
  -- normalisation
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_eq_mul_self (((q / 2 : ℝ) : ℂ) / δ)
  have hw1 : normSq w = 1 := by
    have h := congrArg normSq hw
    rw [normSq_mul, normSq_div, hδ, normSq_ofReal] at h
    have hq2 : (q / 2) * (q / 2) / (q / 2) ^ 2 = 1 := by field_simp
    rw [hq2] at h
    nlinarith [normSq_nonneg w]
  have hw0 : w ≠ 0 := fun h => by rw [h, map_zero] at hw1; norm_num at hw1
  set W' : ℝ → M2 := fun s => w • W s
  have hN' : ∀ t, (w * ch (-(κ / 2)) t) • Nt S W t = ∑ s ∈ S, ch (s - κ / 2) t • W' s := by
    intro t
    simp only [Nt, Finset.smul_sum, smul_smul, W']
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [mul_comm w, mul_assoc, mul_comm w, ← mul_assoc, ch_mul, sub_eq_add_neg, add_comm]
  have htau : ∀ t, tau (∑ s ∈ S, ch (s - κ / 2) t • W' s) = ∑ s ∈ S, ch (s - κ / 2) t • W' s := by
    intro t
    rw [← hN']
    apply tau_fixed _ ((q / 2 : ℝ) : ℂ) (by exact_mod_cast (by positivity : (q / 2 : ℝ) ≠ 0))
    · rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hNN, smul_smul, smul_smul]
      congr 1
      have h1 : w * star w = 1 := by
        rw [Complex.star_def, Complex.mul_conj, hw1]; simp
      have h2 : ch (-(κ / 2)) t * star (ch (-(κ / 2)) t) = 1 := by rw [mul_comm, star_ch_mul_ch]
      rw [star_mul', mul_mul_mul_comm, h1, h2]
      ring
    · rw [det_smul, Fintype.card_fin, hdetN, mul_pow, sq w, ← hw]
      have hc : ch (-(κ / 2)) t ^ 2 * ch κ t = 1 := by
        rw [sq, ch_mul, ch_mul, show -(κ / 2) + -(κ / 2) + κ = 0 by ring, ch_zero]
      calc ((q / 2 : ℝ) : ℂ) / δ * ch (-(κ / 2)) t ^ 2 * (δ * ch κ t)
          = ((q / 2 : ℝ) : ℂ) / δ * δ * (ch (-(κ / 2)) t ^ 2 * ch κ t) := by ring
        _ = ((q / 2 : ℝ) : ℂ) := by rw [hc, mul_one, div_mul_cancel₀ _ hδ0]
  -- the quaternion pairing s ↦ κ - s
  have hpair : ∀ s ∈ S, κ - s ∈ S ∧ tau (W' (κ - s)) = W' s := by
    set F := S.image (fun s => s - κ / 2) ∪ S.image (fun s => κ / 2 - s)
    have hcoef : ∀ i j, ∀ ν ∈ F, (∑ s ∈ S with s - κ / 2 = ν, W' s i j) -
        (∑ s ∈ S with κ / 2 - s = ν, tau (W' s) i j) = 0 := by
      intro i j
      refine ch_indep F _ fun t => ?_
      have h := congrFun (congrFun (htau t) i) j
      rw [tau_sum] at h
      simp only [Matrix.sum_apply, tau_smul, Matrix.smul_apply, smul_eq_mul] at h
      have h1 := group_sum S F (fun s => s - κ / 2) (fun s => W' s i j)
        (fun s hs => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs)) t
      have h2 := group_sum S F (fun s => κ / 2 - s) (fun s => tau (W' s) i j)
        (fun s hs => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)) t
      have hconj : ∀ s, star (ch (s - κ / 2) t) = ch (κ / 2 - s) t := by
        intro s; rw [Complex.star_def, conj_ch]; congr 1; ring
      have h' : ∑ x ∈ S, tau (W' x) i j * ch (κ / 2 - x) t = ∑ x ∈ S,
          W' x i j * ch (x - κ / 2) t := by
        calc ∑ x ∈ S, tau (W' x) i j * ch (κ / 2 - x) t
            = ∑ x ∈ S, star (ch (x - κ / 2) t) * tau (W' x) i j :=
              Finset.sum_congr rfl fun x _ => by rw [mul_comm]; congr 1; exact (hconj x).symm
          _ = ∑ x ∈ S, ch (x - κ / 2) t * W' x i j := h
          _ = ∑ x ∈ S, W' x i j * ch (x - κ / 2) t :=
              Finset.sum_congr rfl fun x _ => mul_comm _ _
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [← h1, ← h2, ← h', sub_self]
    intro s₀ hs₀
    have hfib1 : (S.filter fun s => s - κ / 2 = s₀ - κ / 2) = {s₀} := by
      ext s; simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩; linarith
      · rintro rfl; exact ⟨hs₀, rfl⟩
    have hfib2 : (S.filter fun s => κ / 2 - s = s₀ - κ / 2) = S.filter (fun s => s = κ - s₀) := by
      congr 1; ext s; constructor <;> intro h <;> linarith
    have hν : s₀ - κ / 2 ∈ F := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs₀)
    have hmem : κ - s₀ ∈ S := by
      by_contra hn
      apply hW s₀ hs₀
      have : W' s₀ = 0 := by
        ext i j
        have := hcoef i j _ hν
        rw [hfib1, hfib2, Finset.filter_eq' S] at this
        simp only [hn, ↓reduceIte, Finset.sum_singleton, Finset.sum_empty, sub_zero] at this
        simpa using this
      simpa [W', hw0] using this
    refine ⟨hmem, ?_⟩
    ext i j
    have := hcoef i j _ hν
    rw [hfib1, hfib2, Finset.filter_eq' S] at this
    simp only [hmem, ↓reduceIte, Finset.sum_singleton, sub_eq_zero] at this
    exact this.symm
  -- the generator, shifted by κ/2
  have hW'0 : ∀ s ∈ S, W' s ≠ 0 := fun s hs h => hW s hs (by
    have := congrArg (fun X => w⁻¹ • X) h; simpa [W', smul_smul, inv_mul_cancel₀ hw0] using this)
  have horth' : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → ip (W' s) (W' s') = 0 := by
    intro s hs s' hs' hne; simp [W', ip_smul_left, ip_smul_right, horth s hs s' hs' hne]
  obtain ⟨A, C, hA, hC, hAC⟩ := generator S κ W' hW'0 horth' hpair
  set A'' : M2 := A + ((κ / 2 : ℝ) : ℂ) • 1
  have hA'' : A''.IsHermitian := by
    simp only [A'', IsHermitian, conjTranspose_add, conjTranspose_smul, conjTranspose_one,
      hA.eq, Complex.star_def, conj_ofReal]
  have heig : ∀ s ∈ S, A'' * W s + W s * C = (s : ℂ) • W s := by
    intro s hs
    have h' : A * W s + W s * C = (((s - κ / 2 : ℝ) : ℂ)) • W s := by
      apply smul_right_injective M2 hw0
      have h0 := hAC s hs
      simp only [W', Matrix.mul_smul, Matrix.smul_mul, ← smul_add] at h0
      change w • (A * W s + W s * C) = w • ((((s - κ / 2 : ℝ) : ℂ)) • W s)
      rw [h0]
      exact smul_comm _ _ _
    simp only [A'', Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [add_right_comm, h', ← add_smul]
    congr 1; push_cast; ring
  refine ⟨A'', C, hA'', hC, fun t => ?_⟩
  simp only [Nt, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [ch_zero_left, one_smul, evolve_eigen hA'' hC (W s) s (heig s hs) t]

end ProductTrajectory.MaxEnt
