import LeanProofs.Spans.Support

/-!
# Span-maximizing chains: Lemmas 2.1, 2.2 and 2.4

With `φ = arg Z` at an optimum:
* (2.1) every rearrangement projects onto `φ` at most as far as the optimum, and a tie forces the same `Z`;
* (2.2) `(l_i - l_j)(cos(θ_i - φ) - cos(θ_j - φ)) > 0` for `i ≠ j`: longer segments point closer to `φ`;
* (2.4) `(a_k - a_{k+1})(θ_k + θ_{k+2} - 2φ) < 0`.
-/

open Complex Finset Real
open scoped ComplexOrder

namespace Spans

variable {m : ℕ}

/-- Projection onto direction `φ`. -/
noncomputable def proj (φ : ℝ) (z : ℂ) : ℝ := (e (-φ) * z).re

lemma proj_self (z : ℂ) : proj (arg z) z = ‖z‖ := by
  unfold proj
  have : e (-arg z) * z = (‖z‖ : ℂ) := by
    nth_rewrite 2 [← norm_mul_exp_arg_mul_I z]
    rw [show e (-arg z) * ((‖z‖ : ℂ) * exp (↑(arg z) * I)) = (‖z‖ : ℂ) * (e (-arg z) * e (arg z)) by
      unfold e; ring]
    rw [← e_add, neg_add_cancel]; simp [e]
  rw [this]; simp

lemma proj_le_norm (φ : ℝ) (z : ℂ) : proj φ z ≤ ‖z‖ := by
  unfold proj
  calc (e (-φ) * z).re ≤ ‖e (-φ) * z‖ := Complex.re_le_norm _
    _ = ‖z‖ := by rw [norm_mul, norm_e, one_mul]

/-- If a projection reaches the norm of another vector that is at least as long, the two vectors coincide. -/
lemma eq_of_proj_eq {z w : ℂ} (hw : ‖w‖ ≤ ‖z‖) (h : proj (arg z) w = ‖z‖) : w = z := by
  have hn : ‖e (-arg z) * w‖ = ‖w‖ := by rw [norm_mul, norm_e, one_mul]
  have hre : (e (-arg z) * w).re = ‖e (-arg z) * w‖ := by
    apply le_antisymm (Complex.re_le_norm _)
    rw [hn]; unfold proj at h; linarith
  have h0 : 0 ≤ e (-arg z) * w := Complex.re_eq_norm.1 hre
  have hreal : e (-arg z) * w = ((‖z‖ : ℝ) : ℂ) := by
    rw [Complex.nonneg_iff] at h0
    apply Complex.ext
    · simp only [Complex.ofReal_re]; unfold proj at h; exact h
    · simp only [Complex.ofReal_im]; exact h0.2.symm
  have : w = e (arg z) * (e (-arg z) * w) := by
    rw [← mul_assoc, ← e_add, add_neg_cancel]; simp [e]
  calc w = e (arg z) * (e (-arg z) * w) := this
    _ = e (arg z) * (‖z‖ : ℂ) := by rw [hreal]
    _ = z := by unfold e; rw [mul_comm]; exact norm_mul_exp_arg_mul_I z

lemma proj_add (φ : ℝ) (z : ℂ) (c x y : ℝ) :
    proj φ (z + (c : ℂ) * (e x - e y)) = proj φ z + c * (Real.cos (x - φ) - Real.cos (y - φ)) := by
  unfold proj
  rw [mul_add, Complex.add_re]
  congr 1
  rw [show e (-φ) * ((c : ℂ) * (e x - e y)) = (c : ℂ) * (e (-φ) * e x - e (-φ) * e y) by ring,
    Complex.re_ofReal_mul, Complex.sub_re, e_mul_re, e_mul_re]

section optimum
variable {l : Fin (m + 1) → ℝ} {a : Fin m → ℝ} (h : Admissible l a) (hopt : Optimal l a)
include h hopt

/-- Lemma 2.1. -/
lemma support (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin m)) :
    proj (arg (Z l a)) (Z (l ∘ σ) (a ∘ τ)) ≤ proj (arg (Z l a)) (Z l a) := by
  rw [proj_self]; exact (proj_le_norm _ _).trans (hopt σ τ)

lemma support_eq (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin m))
    (heq : proj (arg (Z l a)) (Z (l ∘ σ) (a ∘ τ)) = proj (arg (Z l a)) (Z l a)) :
    Z (l ∘ σ) (a ∘ τ) = Z l a := by
  rw [proj_self] at heq; exact eq_of_proj_eq (hopt σ τ) heq

/-- Lemma 2.2: longer segments point strictly closer to the resultant. -/
theorem length_cmp (hm : 1 ≤ m) {i j : Fin (m + 1)} (hij : i ≠ j) :
    0 < (l i - l j) * (Real.cos (θ a i - arg (Z l a)) - Real.cos (θ a j - arg (Z l a))) := by
  set φ := arg (Z l a)
  have hsw := Z_swap_lengths l a hij
  have hle := support h hopt (Equiv.swap i j) (Equiv.refl _)
  simp only [Equiv.coe_refl, Function.comp_id] at hle
  rw [hsw, proj_add] at hle
  have hle' : 0 ≤ (l i - l j) * (Real.cos (θ a i - φ) - Real.cos (θ a j - φ)) := by nlinarith
  rcases hle'.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hz := support_eq h hopt (Equiv.swap i j) (Equiv.refl _)
    simp only [Equiv.coe_refl, Function.comp_id] at hz
    rw [hsw, proj_add] at hz
    have hz' := hz (by nlinarith)
    have hc : ((l j - l i : ℝ) : ℂ) * (e (θ a i) - e (θ a j)) = 0 := by
      have := congrArg (fun w => w - Z l a) hz'; simpa using this
    rcases mul_eq_zero.1 hc with hc | hc
    · have : l j = l i := by exact_mod_cast (sub_eq_zero.1 (by exact_mod_cast hc))
      exact hij (h.linj this.symm)
    · have he := sub_eq_zero.1 hc
      have hθ := e_inj (θ_nonneg h.apos _) (θ_lt_pi h (by omega)).le (θ_nonneg h.apos _)
        (θ_lt_pi h (by omega)).le he
      rcases lt_or_gt_of_ne (fun hv : (i : ℕ) = j => hij (Fin.ext hv)) with hv | hv
      · linarith [θ_strictMono h.apos hv (by omega : (j : ℕ) ≤ m)]
      · linarith [θ_strictMono h.apos hv (by omega : (i : ℕ) ≤ m)]

/-- Lemma 2.4: adjacent turns. -/
theorem turn_cmp (hm : 1 ≤ m) {k : ℕ} (hk : k + 1 < m) :
    (ext a k - ext a (k + 1)) * (θ a k + θ a (k + 2) - 2 * arg (Z l a)) < 0 := by
  set φ := arg (Z l a)
  have hsw := Z_swap_turns l a hk
  have hle := support h hopt (Equiv.refl _) (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩)
  simp only [Equiv.coe_refl, Function.comp_id] at hle
  rw [hsw, show (l ⟨k + 1, by omega⟩ : ℂ) = ((l ⟨k + 1, by omega⟩ : ℝ) : ℂ) from rfl, proj_add] at hle
  have hl := h.lpos ⟨k + 1, by omega⟩
  have hak : ext a k = a ⟨k, by omega⟩ := by unfold ext; rw [dif_pos (by omega)]
  have hak1 : ext a (k + 1) = a ⟨k + 1, hk⟩ := by unfold ext; rw [dif_pos hk]
  have hne : ext a k ≠ ext a (k + 1) := by
    rw [hak, hak1]; intro hc; have := h.ainj hc; simp [Fin.ext_iff] at this
  have h2 : θ a (k + 2) = θ a k + ext a k + ext a (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by ring, θ_succ, θ_succ]
  have h1 : θ a (k + 1) = θ a k + ext a k := θ_succ a k
  rw [h1] at hle
  -- the cosine difference has a sign: strictly negative
  have hcos : Real.cos (θ a k + ext a (k + 1) - φ) - Real.cos (θ a k + ext a k - φ) < 0 := by
    have hle' : Real.cos (θ a k + ext a (k + 1) - φ) - Real.cos (θ a k + ext a k - φ) ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith
    rcases hle'.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hz := support_eq h hopt (Equiv.refl _) (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩)
      simp only [Equiv.coe_refl, Function.comp_id] at hz
      rw [hsw, show (l ⟨k + 1, by omega⟩ : ℂ) = ((l ⟨k + 1, by omega⟩ : ℝ) : ℂ) from rfl, proj_add,
        h1, heq, mul_zero, add_zero] at hz
      have hz' := hz rfl
      have hc : ((l ⟨k + 1, by omega⟩ : ℝ) : ℂ) * (e (θ a k + ext a (k + 1)) - e (θ a k + ext a k)) = 0 := by
        have := congrArg (fun w => w - Z l a) hz'; simpa [h1] using this
      rcases mul_eq_zero.1 hc with hc | hc
      · exact absurd (by exact_mod_cast hc) hl.ne'
      · have he := sub_eq_zero.1 hc
        have hT := θ_le_T h.apos (i := k + 2) (by omega)
        have hx := ext_nonneg h.apos k
        have hy := ext_nonneg h.apos (k + 1)
        have hθ := θ_nonneg h.apos k
        have := e_inj (by linarith) (by linarith [h.Tlt]) (by linarith) (by linarith [h.Tlt]) he
        exact hne (by linarith)
  rw [Real.cos_sub_cos] at hcos
  -- signs: the half-sum lies in (-π, π), the half-difference in (-π/2, π/2)
  set μ := (θ a k + ext a (k + 1) - φ + (θ a k + ext a k - φ)) / 2
  set δ := (θ a k + ext a (k + 1) - φ - (θ a k + ext a k - φ)) / 2
  have hφ0 := arg_pos h hm
  have hφT := arg_lt_T h hm
  have hT := θ_le_T h.apos (i := k + 2) (by omega)
  have hx := ext_nonneg h.apos k
  have hy := ext_nonneg h.apos (k + 1)
  have hθ := θ_nonneg h.apos k
  have hμ1 : -π < μ := by simp only [μ]; linarith [h.Tlt]
  have hμ2 : μ < π := by simp only [μ]; linarith [h.Tlt]
  have hδ1 : -π < δ := by simp only [δ]; linarith [h.Tlt]
  have hδ2 : δ < π := by simp only [δ]; linarith [h.Tlt]
  have hprod : 0 < Real.sin μ * Real.sin δ := by nlinarith
  have key : 0 < μ * δ := by
    rcases lt_trichotomy μ 0 with hμ | hμ | hμ
    · have s1 := (sin_neg_iff_of_abs_lt hμ1 hμ2).2 hμ
      have s2 : Real.sin δ < 0 := by
        by_contra hc; push_neg at hc; nlinarith
      have := (sin_neg_iff_of_abs_lt hδ1 hδ2).1 s2
      nlinarith
    · rw [hμ, Real.sin_zero, zero_mul] at hprod; exact absurd hprod (lt_irrefl 0)
    · have s1 := (sin_pos_iff_of_abs_lt hμ1 hμ2).2 hμ
      have s2 : 0 < Real.sin δ := by
        by_contra hc; push_neg at hc; nlinarith
      have := (sin_pos_iff_of_abs_lt hδ1 hδ2).1 s2
      nlinarith
  simp only [μ, δ] at key
  rw [h2]
  nlinarith

end optimum

end Spans
