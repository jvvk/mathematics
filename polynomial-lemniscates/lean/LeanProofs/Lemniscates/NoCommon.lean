import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic

/-!
# Lemniscates (all degrees): Lemma 1, no common factor

Polynomials in `Z, W` are `ℂ[X][X]`: the outer variable is `W`, coefficients are polynomials in `Z`.
`Fp f g c = f(Z) g(W) - c`.

`no_common_prime` (Lemma 1 of PROOF.md): if `f₁, f₂` are coprime and nonconstant, `g₁, g₂` monic, coprime and
nonconstant, then for every `c` and every `r ≠ 0`, `Fp f₁ g₁ c` and `Fp f₂ g₂ r` have no common prime factor.
`no_common_prime_zero` (Lemma 1'): `Fp f₁ g₁ 0` and `Fp f₂ g₂ c` have no common prime factor for every `c`.
-/

open Polynomial

namespace Lemniscates

/-- `f(Z) g(W) - c` in `ℂ[Z][W]`. -/
noncomputable def Fp (f g : ℂ[X]) (c : ℂ) : ℂ[X][X] := C f * g.map C - C (C c)

variable {f₁ f₂ g₁ g₂ : ℂ[X]}

/-- Specialising `Z = ζ` coefficientwise. -/
noncomputable abbrev atZ (ζ : ℂ) : ℂ[X] →+* ℂ := evalRingHom ζ

lemma Fp_map_atZ (f g : ℂ[X]) (c ζ : ℂ) : (Fp f g c).map (atZ ζ) = C (f.eval ζ) * g - C c := by
  have hid : (atZ ζ).comp (C : ℂ →+* ℂ[X]) = RingHom.id ℂ := by ext; simp
  simp [Fp, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, hid]

/-- A degree-zero (in `W`) prime factor of `Fp f g c` forces a root `ζ` with `f(ζ) g(W) = c`. -/
lemma root_of_deg_zero_dvd {H : ℂ[X][X]} (hH : Prime H) (h0 : H.natDegree = 0) :
    ∃ ζ : ℂ, H.map (atZ ζ) = 0 := by
  have hHC : H = C (H.coeff 0) := eq_C_of_natDegree_eq_zero h0
  have hne : H.coeff 0 ≠ 0 := fun h => hH.ne_zero (by rw [hHC, h, C_0])
  have hnu : ¬ IsUnit (H.coeff 0) := fun h => hH.not_isUnit (by rw [hHC]; exact h.map C)
  have hdeg : 0 < (H.coeff 0).degree := by
    by_contra hd
    rw [not_lt] at hd
    rw [eq_C_of_degree_le_zero hd] at hnu hne
    exact hnu (isUnit_C.mpr (isUnit_iff_ne_zero.mpr fun h => hne (by rw [h, C_0])))
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ (ne_of_gt hdeg)
  refine ⟨ζ, ?_⟩
  rw [hHC, Polynomial.map_C]
  simpa [IsRoot.def] using hζ

/-- If `H ∣ Fp f g c` with `g` monic of positive degree and `H.map (atZ ζ) = 0`, then `f(ζ) = 0` and `c = 0`. -/
lemma vanish_of_dvd {f g : ℂ[X]} {c ζ : ℂ} (hg : g.Monic) (hgd : 0 < g.natDegree) {H : ℂ[X][X]}
    (hdvd : H ∣ Fp f g c) (hζ : H.map (atZ ζ) = 0) : f.eval ζ = 0 ∧ c = 0 := by
  have h := Polynomial.map_dvd (atZ ζ) hdvd
  rw [hζ, zero_dvd_iff, Fp_map_atZ] at h
  have htop := congrArg (fun p => p.coeff g.natDegree) h
  simp only [coeff_sub, coeff_C_mul, coeff_zero] at htop
  rw [hg.coeff_natDegree, coeff_C, ite_eq_right_iff.mpr (fun h => absurd h (Nat.pos_iff_ne_zero.mp hgd)), sub_zero, mul_one] at htop
  refine ⟨htop, ?_⟩
  have hc := congrArg (fun p => p.coeff 0) h
  simp only [coeff_sub, coeff_C_mul, coeff_C_zero, coeff_zero, htop, zero_mul, zero_sub,
    neg_eq_zero] at hc
  exact hc

/-- `Fp f g c` has `W`-degree `deg g` and leading coefficient `f`. -/
lemma Fp_natDegree_leadingCoeff {f g : ℂ[X]} (c : ℂ) (hf : f ≠ 0) (hg : g.Monic) (hgd : 0 < g.natDegree) :
    (Fp f g c).natDegree = g.natDegree ∧ (Fp f g c).leadingCoeff = f := by
  have hmap : (g.map (C : ℂ →+* ℂ[X])).Monic := hg.map C
  have hdm : (g.map (C : ℂ →+* ℂ[X])).natDegree = g.natDegree := hg.natDegree_map C
  have h1 : (C f * g.map C).natDegree = g.natDegree := by rw [natDegree_C_mul hf, hdm]
  have h1l : (C f * g.map C).leadingCoeff = f := by
    rw [leadingCoeff_mul, leadingCoeff_C, hmap.leadingCoeff, mul_one]
  have hlt : (C (C c) : ℂ[X][X]).natDegree < (C f * g.map C).natDegree := by
    rw [natDegree_C, h1]; exact hgd
  have hdeg : (C (C c) : ℂ[X][X]).degree < (C f * g.map C).degree := by
    rcases eq_or_ne (C c : ℂ[X]) 0 with h | h
    · rw [h, C_0, degree_zero]
      exact bot_lt_iff_ne_bot.mpr fun h' => by
        rw [degree_eq_bot] at h'; rw [h', natDegree_zero] at h1; omega
    · exact degree_lt_degree hlt
  unfold Fp
  exact ⟨by rw [natDegree_sub_eq_left_of_natDegree_lt hlt, h1],
    by rw [leadingCoeff_sub_of_degree_lt hdeg, h1l]⟩

/-- A prime dividing `g(W)` (constant coefficients, `g` monic) is associated with some `W - ω`, `g(ω) = 0`. -/
lemma prime_dvd_map_C_monic {g : ℂ[X]} {H : ℂ[X][X]} (hH : Prime H) (hg : g.Monic)
    (hd : H ∣ g.map C) : ∃ ω ∈ g.roots, Associated H (X - C (C ω)) := by
  have hsplit : (g.roots.map fun a => X - C a).prod = g :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hg IsAlgClosed.card_roots_eq_natDegree
  rw [← hsplit, Polynomial.map_multiset_prod, Multiset.map_map] at hd
  obtain ⟨q, hq, hHq⟩ := hH.exists_mem_multiset_dvd hd
  obtain ⟨ω, hω, rfl⟩ := Multiset.mem_map.mp hq
  refine ⟨ω, hω, ?_⟩
  simp only [Function.comp_apply, Polynomial.map_sub, map_X, Polynomial.map_C] at hHq ⊢
  -- `X - C (C ω) = H * Q` with `deg H = 1`, so `Q` is a unit
  obtain ⟨Q, hQ⟩ := hHq
  have hne : (X - C (C ω) : ℂ[X][X]) ≠ 0 := X_sub_C_ne_zero _
  have hH0 : H ≠ 0 := hH.ne_zero
  have hQ0 : Q ≠ 0 := fun h => hne (by rw [hQ, h, mul_zero])
  have hdeg := congrArg natDegree hQ
  rw [natDegree_X_sub_C, natDegree_mul hH0 hQ0] at hdeg
  have hHd : H.natDegree ≠ 0 := by
    intro h0
    obtain ⟨ζ, hζ⟩ := root_of_deg_zero_dvd hH h0
    have := congrArg (Polynomial.map (atZ ζ)) hQ
    rw [Polynomial.map_mul, hζ, zero_mul, Polynomial.map_sub, map_X, Polynomial.map_C] at this
    exact X_sub_C_ne_zero _ this
  have hQd : Q.natDegree = 0 := by omega
  have hlc := congrArg leadingCoeff hQ
  rw [leadingCoeff_X_sub_C, leadingCoeff_mul, eq_C_of_natDegree_eq_zero hQd, leadingCoeff_C] at hlc
  have hu : IsUnit (Q.coeff 0) := IsUnit.of_mul_eq_one_right H.leadingCoeff hlc.symm
  rw [eq_C_of_natDegree_eq_zero hQd] at hQ
  exact ⟨(isUnit_C.mpr hu).unit, hQ.symm⟩

/-- If `W - ω` (up to a unit) divides `f(Z) g(W) - c` with `f` nonconstant, then `g(ω) = 0`. -/
lemma eval_g_of_linear_dvd {f g : ℂ[X]} {c ω : ℂ} (hf : 0 < f.natDegree) {H : ℂ[X][X]}
    (hHω : Associated H (X - C (C ω))) (hdvd : H ∣ Fp f g c) : g.eval ω = 0 := by
  have hroot : (Fp f g c).IsRoot (C ω) := (dvd_iff_isRoot).mp (hHω.dvd_iff_dvd_left.mp hdvd)
  rw [IsRoot.def, Fp, eval_sub, eval_mul, eval_C, eval_C, eval_map, eval₂_at_apply] at hroot
  have htop := congrArg (fun p => p.coeff f.natDegree) hroot
  simp only [coeff_sub, coeff_mul_C, coeff_C, if_neg (Nat.pos_iff_ne_zero.mp hf), sub_zero,
    coeff_zero] at htop
  rcases mul_eq_zero.mp htop with h | h
  · exact absurd h (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hf))
  · exact h

section hyps
variable (hf₁ : 0 < f₁.natDegree) (hf₂ : 0 < f₂.natDegree) (hf : IsCoprime f₁ f₂)
  (hg₁ : g₁.Monic) (hg₂ : g₂.Monic) (hg₁d : 0 < g₁.natDegree) (hg₂d : 0 < g₂.natDegree)
  (hg : IsCoprime g₁ g₂)
include hf₁ hf₂ hf hg₁ hg₂ hg₁d hg₂d hg

/-- **Lemma 1'.** `f₁(Z) g₁(W)` and `f₂(Z) g₂(W) - c` have no common prime factor. -/
theorem no_common_prime_zero (c : ℂ) {H : ℂ[X][X]} (hH : Prime H) (h₁ : H ∣ Fp f₁ g₁ 0)
    (h₂ : H ∣ Fp f₂ g₂ c) : False := by
  have hF : Fp f₁ g₁ 0 = C f₁ * g₁.map C := by simp [Fp]
  rw [hF] at h₁
  rcases hH.dvd_or_dvd h₁ with hd | hd
  · -- `H ∣ f₁(Z)`: `H` has `W`-degree zero, so it vanishes at some `Z = ζ` with `f₁(ζ) = 0`
    have hf₁0 : f₁ ≠ 0 := ne_zero_of_natDegree_gt hf₁
    have h0 : H.natDegree = 0 := by
      have hC : (C f₁ : ℂ[X][X]) ≠ 0 := C_ne_zero.mpr hf₁0
      have := natDegree_le_of_dvd hd hC
      rwa [natDegree_C, Nat.le_zero] at this
    obtain ⟨ζ, hζ⟩ := root_of_deg_zero_dvd hH h0
    obtain ⟨hf₂ζ, -⟩ := vanish_of_dvd hg₂ hg₂d h₂ hζ
    -- and `H = C h₀` with `h₀(ζ) = 0`, `h₀ ∣ f₁`
    have hHC : H = C (H.coeff 0) := eq_C_of_natDegree_eq_zero h0
    have hh0 : (H.coeff 0).eval ζ = 0 := by
      have := congrArg (fun p => p.coeff 0) hζ
      simp only [coeff_map, coeff_zero] at this
      exact this
    have hdiv : H.coeff 0 ∣ f₁ := by
      have hd' := hd
      rw [hHC] at hd'
      simpa using (C_dvd_iff_dvd_coeff _ _).mp hd' 0
    have hf₁ζ : f₁.eval ζ = 0 := by
      obtain ⟨q, hq⟩ := hdiv; rw [hq, eval_mul, hh0, zero_mul]
    obtain ⟨u, v, huv⟩ := hf
    have := congrArg (eval ζ) huv
    simp [hf₁ζ, hf₂ζ] at this
  · -- `H ∣ g₁(W)`: `H` is associated with some `W - ω`, `g₁(ω) = 0`
    obtain ⟨ω, hωr, hHω⟩ := prime_dvd_map_C_monic hH hg₁ hd
    have hω₁ : g₁.eval ω = 0 := (mem_roots hg₁.ne_zero).mp hωr
    have hω₂ := eval_g_of_linear_dvd hf₂ hHω h₂
    obtain ⟨u, v, huv⟩ := hg
    have := congrArg (eval ω) huv
    simp [hω₁, hω₂] at this

/-- **Lemma 1.** For every `c` and every `r ≠ 0`, `f₁(Z) g₁(W) - c` and `f₂(Z) g₂(W) - r` have no common
prime factor. -/
theorem no_common_prime (c : ℂ) {r : ℂ} (hr : r ≠ 0) {H : ℂ[X][X]} (hH : Prime H)
    (h₁ : H ∣ Fp f₁ g₁ c) (h₂ : H ∣ Fp f₂ g₂ r) : False := by
  by_cases hc : c = 0
  · subst hc
    exact no_common_prime_zero hf₁ hf₂ hf hg₁ hg₂ hg₁d hg₂d hg r hH h₁ h₂
  have hf₁0 : f₁ ≠ 0 := ne_zero_of_natDegree_gt hf₁
  have hf₂0 : f₂ ≠ 0 := ne_zero_of_natDegree_gt hf₂
  by_cases h0 : H.natDegree = 0
  · obtain ⟨ζ, hζ⟩ := root_of_deg_zero_dvd hH h0
    exact hr (vanish_of_dvd hg₂ hg₂d h₂ hζ).2
  -- the leading coefficient of `H` divides `f₁` and `f₂`, so it is a nonzero constant
  have lc_dvd : ∀ {f g : ℂ[X]} {e : ℂ}, f ≠ 0 → g.Monic → 0 < g.natDegree → H ∣ Fp f g e →
      H.leadingCoeff ∣ f := by
    intro f g e hf0 hg hgd hdvd
    obtain ⟨Q, hQ⟩ := hdvd
    have := congrArg leadingCoeff hQ
    rw [(Fp_natDegree_leadingCoeff e hf0 hg hgd).2, leadingCoeff_mul] at this
    exact ⟨Q.leadingCoeff, this⟩
  have hu : IsUnit H.leadingCoeff :=
    hf.isUnit_of_dvd' (lc_dvd hf₁0 hg₁ hg₁d h₁) (lc_dvd hf₂0 hg₂ hg₂d h₂)
  obtain ⟨u, huu, hCu⟩ := Polynomial.isUnit_iff.mp hu
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root f₁ (by
    rw [degree_eq_natDegree hf₁0]; exact_mod_cast (Nat.pos_iff_ne_zero.mp hf₁))
  have hlcζ : atZ ζ H.leadingCoeff ≠ 0 := by
    rw [← hCu]; simpa using huu.ne_zero
  have hdeg : (H.map (atZ ζ)).natDegree = H.natDegree := natDegree_map_of_leadingCoeff_ne_zero _ hlcζ
  have hdvd := Polynomial.map_dvd (atZ ζ) h₁
  rw [Fp_map_atZ, show f₁.eval ζ = 0 from hζ, C_0, zero_mul, zero_sub] at hdvd
  have hle := natDegree_le_of_dvd hdvd (by simpa using hc)
  rw [hdeg, natDegree_neg, natDegree_C] at hle
  exact h0 (Nat.le_zero.mp hle)

end hyps

end Lemniscates
