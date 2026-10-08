import LeanProofs.Lemniscates.CaseI

/-!
# Case II: `f₁` and `f₂` share a root

Eliminate `W`: `R(Z) = Res_W(f₁(Z) g₁(W) - r₁, f₂(Z) g₂(W) - r₂)`.

* Every common zero `(z, w)` gives `R(z) = 0` (`R_eval_eq_zero`); in particular every intersection
  point `z` of the lemniscates (with `w = z̄`) is a root of `R`.
* `R` has degree at most `n₁ m₂ + n₂ m₁`, with top coefficient `Res(g₁, g₂)` and next coefficient
  a multiple of it (`ResTop`). A shared root `ζ` of `f₁, f₂` gives the shared root `ζ̄` of `g₁, g₂`,
  so `Res(g₁, g₂) = 0` and `deg R ≤ 2 n₁ n₂ - 2` (`R_natDegree_le`).
* Hence if `R ≠ 0`, the intersection has at most `2 n₁ n₂ - 2` points (`count_of_R_ne_zero`).

The case `R = 0` (a common factor) is in `CaseIIb.lean`.
-/

open Polynomial ComplexConjugate

namespace Lemniscates.CaseII

open CaseI

/-- `R(Z) = Res_W(f₁(Z) g₁(W) - r₁, f₂(Z) g₂(W) - r₂)`. -/
noncomputable def R (f₁ f₂ g₁ g₂ : ℂ[X]) (r₁ r₂ : ℂ) : ℂ[X] :=
  (Fp f₁ g₁ r₁).resultant (Fp f₂ g₂ r₂) g₁.natDegree g₂.natDegree

lemma Fp_coeff (f g : ℂ[X]) (c : ℂ) (k : ℕ) :
    (Fp f g c).coeff k = f * C (g.coeff k) - if k = 0 then C c else 0 := by
  simp only [Fp, coeff_sub, coeff_C_mul, coeff_map, coeff_C]

lemma Fp_coeff_natDegree (f g : ℂ[X]) (c : ℂ) (k : ℕ) :
    ((Fp f g c).coeff k).natDegree ≤ f.natDegree := by
  rw [Fp_coeff]
  refine (natDegree_sub_le _ _).trans (max_le (natDegree_mul_le.trans (by simp)) ?_)
  split_ifs <;> simp

lemma Fp_coeff_top {f : ℂ[X]} (g : ℂ[X]) (c : ℂ) (hf : f.Monic) (hfd : 0 < f.natDegree) (k : ℕ) :
    ((Fp f g c).coeff k).coeff f.natDegree = g.coeff k := by
  rw [Fp_coeff, coeff_sub, coeff_mul_C, hf.coeff_natDegree, one_mul]
  split_ifs <;> simp [coeff_C, hfd.ne']

lemma Fp_coeff_subtop {f : ℂ[X]} (g : ℂ[X]) (c : ℂ) (hf : f.Monic) (hfd : 2 ≤ f.natDegree)
    (k : ℕ) : ((Fp f g c).coeff k).coeff (f.natDegree - 1) =
      f.coeff (f.natDegree - 1) * ((Fp f g c).coeff k).coeff f.natDegree := by
  rw [Fp_coeff_top g c hf (by omega), Fp_coeff, coeff_sub, coeff_mul_C]
  have : f.natDegree - 1 ≠ 0 := by omega
  split_ifs <;> simp [coeff_C, this]

lemma Fp_natDegree_le (f g : ℂ[X]) (c : ℂ) : (Fp f g c).natDegree ≤ g.natDegree := by
  refine (natDegree_sub_le _ _).trans (max_le (natDegree_mul_le.trans ?_) (by simp))
  simp

/-- Common zeros give roots of `R`. -/
theorem R_eval_eq_zero (f₁ f₂ g₁ g₂ : ℂ[X]) (r₁ r₂ : ℂ) (hm : 0 < g₁.natDegree) (z w : ℂ)
    (h₁ : f₁.eval z * g₁.eval w = r₁) (h₂ : f₂.eval z * g₂.eval w = r₂) :
    (R f₁ f₂ g₁ g₂ r₁ r₂).eval z = 0 := by
  rw [R, ← coe_evalRingHom, ← resultant_map_map]
  change ((Fp f₁ g₁ r₁).map (atZ z)).resultant ((Fp f₂ g₂ r₂).map (atZ z)) _ _ = 0
  rw [Fp_map_atZ, Fp_map_atZ]
  have hP : (C (f₁.eval z) * g₁ - C r₁).natDegree ≤ g₁.natDegree :=
    (natDegree_sub_le _ _).trans (max_le (natDegree_C_mul_le _ _) (by simp))
  have hQ : (C (f₂.eval z) * g₂ - C r₂).natDegree ≤ g₂.natDegree :=
    (natDegree_sub_le _ _).trans (max_le (natDegree_C_mul_le _ _) (by simp))
  obtain ⟨p, q, -, -, h⟩ := exists_mul_add_mul_eq_C_resultant _ _ hP hQ (Or.inl hm.ne')
  have := congrArg (eval w) h
  simp only [eval_add, eval_mul, eval_sub, eval_C, h₁, h₂, sub_self, zero_mul, add_zero] at this
  exact this.symm

/-- A shared root of `f₁, f₂` makes `Res(f̄₁, f̄₂) = 0`. -/
theorem res_conj_eq_zero {f₁ f₂ : ℂ[X]} (hm : 0 < f₁.natDegree) {ζ : ℂ} (h₁ : f₁.eval ζ = 0)
    (h₂ : f₂.eval ζ = 0) : (conjP f₁).resultant (conjP f₂) = 0 := by
  have e₁ : (conjP f₁).eval (conj ζ) = 0 := by rw [eval_conjP, Complex.conj_conj, h₁, map_zero]
  have e₂ : (conjP f₂).eval (conj ζ) = 0 := by rw [eval_conjP, Complex.conj_conj, h₂, map_zero]
  obtain ⟨p, q, -, -, h⟩ := exists_mul_add_mul_eq_C_resultant (conjP f₁) (conjP f₂) le_rfl le_rfl
    (Or.inl (by rw [conjP_natDegree]; exact hm.ne'))
  have := congrArg (eval (conj ζ)) h
  simp only [eval_add, eval_mul, e₁, e₂, zero_mul, add_zero, eval_C] at this
  exact this.symm

/-- **Degree of `R`** when `Res(g₁, g₂) = 0`. -/
theorem R_natDegree_le {f₁ f₂ g₁ g₂ : ℂ[X]} (r₁ r₂ : ℂ) (hf₁ : f₁.Monic) (hf₂ : f₂.Monic)
    (hn₁ : 2 ≤ f₁.natDegree) (hn₂ : 2 ≤ f₂.natDegree) (hm₁ : 1 ≤ g₁.natDegree)
    (hres : g₁.resultant g₂ = 0) :
    (R f₁ f₂ g₁ g₂ r₁ r₂).natDegree ≤
      g₁.natDegree * f₂.natDegree + g₂.natDegree * f₁.natDegree - 2 := by
  set N := g₁.natDegree * f₂.natDegree + g₂.natDegree * f₁.natDegree
  obtain ⟨hdeg, htop⟩ := ResTop.resultant_top (Fp f₁ g₁ r₁) (Fp f₂ g₂ r₂) g₁.natDegree
    g₂.natDegree f₁.natDegree f₂.natDegree g₁ g₂ (Fp_coeff_natDegree _ _ _)
    (Fp_coeff_natDegree _ _ _) (Fp_coeff_top g₁ r₁ hf₁ (by omega))
    (Fp_coeff_top g₂ r₂ hf₂ (by omega))
  have hsub := ResTop.resultant_subtop (Fp f₁ g₁ r₁) (Fp f₂ g₂ r₂) g₁.natDegree g₂.natDegree
    f₁.natDegree f₂.natDegree g₁ g₂ (f₁.coeff (f₁.natDegree - 1)) (f₂.coeff (f₂.natDegree - 1))
    (by omega) (by omega) (by omega) (Fp_coeff_natDegree _ _ _) (Fp_coeff_natDegree _ _ _)
    (Fp_coeff_top g₁ r₁ hf₁ (by omega)) (Fp_coeff_top g₂ r₂ hf₂ (by omega))
    (Fp_coeff_subtop g₁ r₁ hf₁ hn₁) (Fp_coeff_subtop g₂ r₂ hf₂ hn₂)
  rw [hres, mul_zero] at hsub
  rw [hres] at htop
  have hN : 2 ≤ N := by
    have : 2 ≤ g₁.natDegree * f₂.natDegree := le_trans hn₂ (Nat.le_mul_of_pos_left _ hm₁)
    omega
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  have hk' : N - 2 < k := by exact_mod_cast hk
  rcases lt_trichotomy k N with h | rfl | h
  · have : k = N - 1 := by omega
    rw [this]; exact hsub
  · exact htop
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg h)

/-- **Case II with `R ≠ 0`.** -/
theorem count_of_R_ne_zero {f₁ f₂ : ℂ[X]} {r₁ r₂ : ℝ} (hf₁ : f₁.Monic) (hf₂ : f₂.Monic)
    (hn₁ : 2 ≤ f₁.natDegree) (hn₂ : 2 ≤ f₂.natDegree) {ζ : ℂ} (hζ₁ : f₁.eval ζ = 0)
    (hζ₂ : f₂.eval ζ = 0) (hR : R f₁ f₂ (conjP f₁) (conjP f₂) r₁ r₂ ≠ 0) (F : Finset ℂ)
    (hF : ∀ z ∈ F, ‖f₁.eval z‖ ^ 2 = r₁ ∧ ‖f₂.eval z‖ ^ 2 = r₂) :
    F.card ≤ 2 * f₁.natDegree * f₂.natDegree - 2 := by
  classical
  have hdeg := R_natDegree_le (r₁ : ℂ) (r₂ : ℂ) hf₁ hf₂ hn₁ hn₂
    (by rw [conjP_natDegree]; omega) (res_conj_eq_zero (by omega) hζ₁ hζ₂)
  rw [conjP_natDegree, conjP_natDegree] at hdeg
  have hsub : F ⊆ (R f₁ f₂ (conjP f₁) (conjP f₂) r₁ r₂).roots.toFinset := by
    intro z hz
    obtain ⟨h₁, h₂⟩ := hF z hz
    rw [Multiset.mem_toFinset, mem_roots hR]
    refine R_eval_eq_zero _ _ _ _ _ _ (by rw [conjP_natDegree]; omega) z (conj z) ?_ ?_
    · rw [eval_conjP, Complex.conj_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, h₁]
    · rw [eval_conjP, Complex.conj_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, h₂]
  calc F.card ≤ (R f₁ f₂ (conjP f₁) (conjP f₂) r₁ r₂).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ (R f₁ f₂ (conjP f₁) (conjP f₂) r₁ r₂).roots.card := Multiset.toFinset_card_le _
    _ ≤ (R f₁ f₂ (conjP f₁) (conjP f₂) r₁ r₂).natDegree := card_roots' _
    _ ≤ 2 * f₁.natDegree * f₂.natDegree - 2 := by
        refine hdeg.trans (le_of_eq ?_)
        ring_nf

end Lemniscates.CaseII
