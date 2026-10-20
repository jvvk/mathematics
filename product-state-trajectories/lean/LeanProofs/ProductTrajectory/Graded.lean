import Mathlib

/-!
# Product trajectories (Physics SE 816017), part 1: homogeneous products have homogeneous factors

Grade `MvPolynomial σ R` by an integer weight `w : σ → ℤ`. Over a domain, the top weight component
of a product is the product of the top components, and likewise at the bottom. Hence if `p * q` is
weighted homogeneous and `p, q ≠ 0`, then `p` is weighted homogeneous (top weight = bottom weight).

This is Step 4' of the hand proof: it applies to `G_α * G_β`, graded by `u_i ↦ -1, v_i ↦ +1`.
-/

namespace ProductTrajectory

open MvPolynomial Finsupp

variable {σ R : Type*} [CommRing R]

/-- In weight `a + b`, the product only sees the weight-`a` and weight-`b` components, when `a`
and `b` bound the weights of `p` and `q`. -/
theorem coeff_mul_top (w : σ → ℤ) {p q : MvPolynomial σ R} {a b : ℤ}
    (hp : ∀ d, p.coeff d ≠ 0 → weight w d ≤ a) (hq : ∀ d, q.coeff d ≠ 0 → weight w d ≤ b)
    (d : σ →₀ ℕ) (hd : weight w d = a + b) :
    (p * q).coeff d =
      (weightedHomogeneousComponent w a p * weightedHomogeneousComponent w b q).coeff d := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
  have hsum : weight w x.1 + weight w x.2 = a + b := by rw [← map_add, hx, hd]
  by_cases h1 : p.coeff x.1 = 0
  · simp [h1]
  by_cases h2 : q.coeff x.2 = 0
  · simp [h2]
  have e1 := hp _ h1
  have e2 := hq _ h2
  have f1 : weight w x.1 = a := by omega
  have f2 : weight w x.2 = b := by omega
  simp [f1, f2]

/-- A nonzero polynomial has a top weight, attained in its support. -/
theorem exists_top_weight (w : σ → ℤ) {p : MvPolynomial σ R} (hp : p ≠ 0) :
    ∃ a : ℤ, (∃ d, p.coeff d ≠ 0 ∧ weight w d = a) ∧ ∀ d, p.coeff d ≠ 0 → weight w d ≤ a := by
  obtain ⟨d₀, hd₀, hmax⟩ :=
    Finset.exists_max_image p.support (fun d => weight w d) (support_nonempty.mpr hp)
  exact ⟨weight w d₀, ⟨d₀, MvPolynomial.mem_support_iff.mp hd₀, rfl⟩,
    fun d hd => hmax d (MvPolynomial.mem_support_iff.mpr hd)⟩

/-- Top weights add when the product is homogeneous. -/
theorem top_add_top [IsDomain R] (w : σ → ℤ) {p q : MvPolynomial σ R} {m a b : ℤ}
    (h : IsWeightedHomogeneous w (p * q) m)
    (ha : ∃ d, p.coeff d ≠ 0 ∧ weight w d = a) (ha' : ∀ d, p.coeff d ≠ 0 → weight w d ≤ a)
    (hb : ∃ d, q.coeff d ≠ 0 ∧ weight w d = b) (hb' : ∀ d, q.coeff d ≠ 0 → weight w d ≤ b) :
    a + b = m := by
  classical
  set P := weightedHomogeneousComponent w a p
  set Q := weightedHomogeneousComponent w b q
  have hP : P ≠ 0 := by
    obtain ⟨d, hd, hwd⟩ := ha
    intro h0
    have := congrArg (fun f : MvPolynomial σ R => f.coeff d) h0
    simp only [P, coeff_weightedHomogeneousComponent, hwd, ite_true,
      AddMonoidAlgebra.coeff_zero] at this
    exact hd this
  have hQ : Q ≠ 0 := by
    obtain ⟨d, hd, hwd⟩ := hb
    intro h0
    have := congrArg (fun f : MvPolynomial σ R => f.coeff d) h0
    simp only [Q, coeff_weightedHomogeneousComponent, hwd, ite_true,
      AddMonoidAlgebra.coeff_zero] at this
    exact hd this
  have hPQ : P * Q ≠ 0 := mul_ne_zero hP hQ
  have hhom : IsWeightedHomogeneous w (P * Q) (a + b) :=
    (weightedHomogeneousComponent_isWeightedHomogeneous a p).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous b q)
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hPQ
  have hwd : weight w d = a + b := hhom hd
  rw [← coeff_mul_top w ha' hb' d hwd] at hd
  rw [← hwd]
  exact h hd

theorem weight_neg (w : σ → ℤ) (d : σ →₀ ℕ) : weight (-w) d = -weight w d := by
  simp [weight_apply, Finsupp.sum]

/-- **Homogeneous products have homogeneous factors** (integer weights, domain coefficients). -/
theorem isWeightedHomogeneous_of_mul [IsDomain R] (w : σ → ℤ) {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : q ≠ 0)
    {m : ℤ} (h : IsWeightedHomogeneous w (p * q) m) : ∃ a, IsWeightedHomogeneous w p a := by
  obtain ⟨a, ha, ha'⟩ := exists_top_weight w hp
  obtain ⟨b, hb, hb'⟩ := exists_top_weight w hq
  have top := top_add_top w h ha ha' hb hb'
  -- bottom weights: top weights for `-w`
  have h' : IsWeightedHomogeneous (-w) (p * q) (-m) := fun d hd => by
    rw [weight_neg, h hd]
  obtain ⟨a', ha₁, ha₁'⟩ := exists_top_weight (-w) hp
  obtain ⟨b', hb₁, hb₁'⟩ := exists_top_weight (-w) hq
  have bot := top_add_top (-w) h' ha₁ ha₁' hb₁ hb₁'
  refine ⟨a, fun d hd => le_antisymm (ha' d hd) ?_⟩
  -- weight d ≥ -a' and -a' + -b' = m = a + b with -b' ≤ b, so -a' ≥ a
  have h1 : -weight w d ≤ a' := by rw [← weight_neg]; exact ha₁' d hd
  obtain ⟨e, he, hwe⟩ := hb₁
  have h2 : -weight w e ≤ b' := by rw [← weight_neg]; exact hb₁' e he
  have h3 : weight w e ≤ b := hb' e he
  rw [weight_neg] at hwe
  omega

end ProductTrajectory
