import LeanProofs.Lemniscates.Level0
import LeanProofs.Lemniscates.Pairing

/-!
# Case I: the trace identity (Proposition 7)

For monic `f₁, f₂` (coprime) and `g₁, g₂` (coprime), all of degree at least 2, and levels
`r₁` and `r₂ ≠ 0`, the solutions of `f₁(Z) g₁(W) = r₁`, `f₂(Z) g₂(W) = r₂`, counted with
multiplicity, form a multiset `S` of size `n₁ m₂ + n₂ m₁` with
`∑_{p ∈ S} (Z_p - m)(W_p - m') = (s₁ - n₁ m)(s₂' - m₂ m') + (s₂ - n₂ m)(s₁' - m₁ m')`
(`trace_identity`), where `s = -nextCoeff` are root sums.

The chain: `S` is the multiset of the fibre at `r₁` of the first deformation (`t ↦ f₁ g₁`, fixed
`f₂ g₂ = r₂`). Its `φ`-sum is `τ₁(r₁) = τ₁(0)` (growth), the trace on `ℂ[Z,W]/(f₁ g₁, f₂ g₂ - r₂)`.
Read through the second deformation (`t ↦ f₂ g₂`, fixed `f₁ g₁ = 0`) this is `τ₂(r₂) = τ₂(0)`,
the trace at level `(0, 0)` computed in `Level0.lean`. Dimensions follow the same chain.
-/

open Polynomial Module

namespace Lemniscates.CaseI

open Deform

/-- The hypotheses of Case I. -/
structure Hyp (f₁ f₂ g₁ g₂ : ℂ[X]) : Prop where
  (hf₁ : f₁.Monic) (hf₂ : f₂.Monic) (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
  (hn₁ : 2 ≤ f₁.natDegree) (hn₂ : 2 ≤ f₂.natDegree) (hm₁ : 2 ≤ g₁.natDegree)
  (hm₂ : 2 ≤ g₂.natDegree)
  (cf : IsCoprime f₁ f₂) (cg : IsCoprime g₁ g₂)

variable {f₁ f₂ g₁ g₂ : ℂ[X]} (H : Hyp f₁ f₂ g₁ g₂)

/-- First deformation: `t ↦ f₁ g₁`, fixed `f₂ g₂ = r₂`. -/
def D₁ (r₂ : ℂ) (hr₂ : r₂ ≠ 0) : Data where
  f := f₁
  g := g₁
  f' := f₂
  g' := g₂
  r := r₂
  hf := H.hf₁
  hg := H.hg₁
  hf' := H.hf₂
  hg' := H.hg₂
  hfd := by have := H.hn₁; omega
  hgd := by have := H.hm₁; omega
  hf'd := by have := H.hn₂; omega
  hg'd := by have := H.hm₂; omega
  cf := H.cf
  cg := H.cg
  hno c P hP h₁ h₂ := no_common_prime (by have := H.hn₁; omega) (by have := H.hn₂; omega) H.cf
    H.hg₁ H.hg₂ (by have := H.hm₁; omega) (by have := H.hm₂; omega) H.cg c hr₂ hP h₁ h₂

/-- Second deformation: `t ↦ f₂ g₂`, fixed `f₁ g₁ = 0`. -/
def D₂ : Data where
  f := f₂
  g := g₂
  f' := f₁
  g' := g₁
  r := 0
  hf := H.hf₂
  hg := H.hg₂
  hf' := H.hf₁
  hg' := H.hg₁
  hfd := by have := H.hn₂; omega
  hgd := by have := H.hm₂; omega
  hf'd := by have := H.hn₁; omega
  hg'd := by have := H.hm₁; omega
  cf := H.cf.symm
  cg := H.cg.symm
  hno c P hP h₁ h₂ := no_common_prime_zero (by have := H.hn₁; omega) (by have := H.hn₂; omega)
    H.cf H.hg₁ H.hg₂ (by have := H.hm₁; omega) (by have := H.hm₂; omega) H.cg c hP h₂ h₁

lemma trace_mkQ (D : Data) (c : ℂ) (P : ℂ[X][X]) :
    LinearMap.trace ℂ (Q D c) (Algebra.lmul ℂ _ (mkQ D c P)) = (τ D P).eval c :=
  Fibre.trace_fibre c (mk D P)

/-- The two presentations of `ℂ[Z, W] / (f₁ g₁, f₂ g₂ - r₂)`. -/
noncomputable def isoQ (r₂ : ℂ) (hr₂ : r₂ ≠ 0) : Q (D₁ H r₂ hr₂) 0 ≃ₐ[ℂ] Q (D₂ H) r₂ :=
  AlgEquiv.ofAlgHom
    (liftQ (D₁ H r₂ hr₂) 0 (mkQ (D₂ H) r₂) (mkQ_G (D₂ H) r₂) (mkQ_Fp_level (D₂ H) r₂))
    (liftQ (D₂ H) r₂ (mkQ (D₁ H r₂ hr₂) 0) (mkQ_G (D₁ H r₂ hr₂) 0)
      (mkQ_Fp_level (D₁ H r₂ hr₂) 0))
    (algHom_ext_Q _ _ fun _ => rfl) (algHom_ext_Q _ _ fun _ => rfl)

lemma evalEval_φ (m m' Z W : ℂ) : (Level0.φ m m').evalEval Z W = (Z - m) * (W - m') := by
  simp [Level0.φ, evalEval_mul, evalEval_sub, evalEval_C, evalEval_X]

include H in
/-- **Proposition 7 (trace identity).** -/
theorem trace_identity (r₁ r₂ : ℂ) (hr₂ : r₂ ≠ 0) (m m' : ℂ) :
    ∃ S : Multiset (ℂ × ℂ),
      S.card = f₁.natDegree * g₂.natDegree + f₂.natDegree * g₁.natDegree ∧
      (S.map fun p => (p.1 - m) * (p.2 - m')).sum =
        (-f₁.nextCoeff - f₁.natDegree * m) * (-g₂.nextCoeff - g₂.natDegree * m') +
        (-f₂.nextCoeff - f₂.natDegree * m) * (-g₁.nextCoeff - g₁.natDegree * m') ∧
      (∀ p ∈ S, f₁.eval p.1 * g₁.eval p.2 = r₁ ∧ f₂.eval p.1 * g₂.eval p.2 = r₂) ∧
      ∀ Z W : ℂ, f₁.eval Z * g₁.eval W = r₁ → f₂.eval Z * g₂.eval W = r₂ → (Z, W) ∈ S := by
  set D₁' := D₁ H r₂ hr₂
  set D₂' := D₂ H
  set φ := Level0.φ m m'
  obtain ⟨S, hcard, hsum, hz, hall⟩ := fibre_multiset D₁' r₁
  -- `τ₁` and `τ₂` are constant
  obtain ⟨A, B, hAB⟩ := GrowthGen.growth_level f₁ g₁ f₂ g₂ r₂ H.hf₁ H.hg₁ H.hf₂ H.hg₂ H.hn₁ H.hm₁
    (by have := H.hn₂; omega) (by have := H.hm₂; omega) H.cf.symm H.cg.symm m m'
  have hc₁ := tau_const D₁' φ A B
    (fun c Z W h₁ h₂ => by rw [evalEval_φ]; exact hAB c Z W h₁ h₂) r₁
  obtain ⟨A', B', hAB'⟩ := GrowthGen.growth_zero f₁ g₁ f₂ g₂ H.hf₁ H.hg₁ H.hf₂ H.hg₂
    (by have := H.hn₁; omega) (by have := H.hm₁; omega) H.hn₂ H.hm₂ H.cf H.cg m m'
  have hc₂ := tau_const D₂' φ A' B'
    (fun d Z W h₁ h₂ => by rw [evalEval_φ]; exact hAB' d Z W h₂ h₁) r₂
  -- the two presentations at level `(0, r₂)`
  have hmid : (τ D₁' φ).eval 0 = (τ D₂' φ).eval r₂ := by
    rw [← trace_mkQ, ← trace_mkQ, ← trace_lmul_algEquiv (isoQ H r₂ hr₂)]
    rfl
  have hrank : finrank ℂ[X] (M D₁') = finrank ℂ[X] (M D₂') := by
    rw [← Fibre.finrank_fibre (S := M D₁') 0, ← Fibre.finrank_fibre (S := M D₂') r₂]
    exact (isoQ H r₂ hr₂).toLinearEquiv.finrank_eq
  obtain ⟨hdim, htr⟩ := Level0.level0 D₂' rfl m m'
  refine ⟨S, ?_, ?_, fun p hp => ?_, fun Z W h₁ h₂ => ?_⟩
  · rw [hcard, hrank, ← Fibre.finrank_fibre (S := M D₂') 0]
    exact hdim
  · have := hsum φ
    rw [show (fun p : ℂ × ℂ => φ.evalEval p.1 p.2) = fun p => (p.1 - m) * (p.2 - m') from
      funext fun p => evalEval_φ m m' p.1 p.2] at this
    rw [this, hc₁, hmid, hc₂, ← trace_mkQ]
    exact htr
  · obtain ⟨h₁, h₂⟩ := hz p hp
    rw [evalEval_Fp, sub_eq_zero] at h₁ h₂
    exact ⟨h₁, h₂⟩
  · exact hall Z W (by rw [evalEval_Fp, sub_eq_zero]; exact h₁)
      (by rw [evalEval_Fp, sub_eq_zero]; exact h₂)

/-! ### Lemniscates: `g = f̄` and the count -/

open ComplexConjugate

/-- Conjugate coefficients. -/
noncomputable def conjP (f : ℂ[X]) : ℂ[X] := f.map (starRingEnd ℂ)

lemma eval_conjP (f : ℂ[X]) (w : ℂ) : (conjP f).eval w = conj (f.eval (conj w)) := by
  rw [conjP, eval_map, ← eval₂_at_apply, Complex.conj_conj]

lemma eval_conj (f : ℂ[X]) (w : ℂ) : f.eval (conj w) = conj ((conjP f).eval w) := by
  rw [eval_conjP, Complex.conj_conj]

lemma conjP_monic {f : ℂ[X]} (hf : f.Monic) : (conjP f).Monic := hf.map _

lemma conjP_natDegree (f : ℂ[X]) : (conjP f).natDegree = f.natDegree :=
  natDegree_map _

lemma conjP_nextCoeff (f : ℂ[X]) : (conjP f).nextCoeff = conj f.nextCoeff :=
  nextCoeff_map_eq _ _

lemma conjP_coprime {f₁ f₂ : ℂ[X]} (h : IsCoprime f₁ f₂) : IsCoprime (conjP f₁) (conjP f₂) :=
  h.map (mapRingHom (starRingEnd ℂ))

/-- **Case I.** Lemniscates `‖f₁‖² = r₁`, `‖f₂‖² = r₂` of coprime monic polynomials of degrees
`n₁, n₂ ≥ 2` meet in at most `2 n₁ n₂ - 2` points. -/
theorem caseI {f₁ f₂ : ℂ[X]} (hf₁ : f₁.Monic) (hf₂ : f₂.Monic) (hn₁ : 2 ≤ f₁.natDegree)
    (hn₂ : 2 ≤ f₂.natDegree) (cf : IsCoprime f₁ f₂) {r₁ r₂ : ℝ} (hr₂ : r₂ ≠ 0) (F : Finset ℂ)
    (hF : ∀ z ∈ F, ‖f₁.eval z‖ ^ 2 = r₁ ∧ ‖f₂.eval z‖ ^ 2 = r₂) :
    F.card ≤ 2 * f₁.natDegree * f₂.natDegree - 2 := by
  set n₁ := f₁.natDegree
  set n₂ := f₂.natDegree
  have H : Hyp f₁ f₂ (conjP f₁) (conjP f₂) :=
    ⟨hf₁, hf₂, conjP_monic hf₁, conjP_monic hf₂, hn₁, hn₂, by rw [conjP_natDegree]; exact hn₁,
      by rw [conjP_natDegree]; exact hn₂, cf, conjP_coprime cf⟩
  -- centroids and their midpoint
  set c₁ : ℂ := -f₁.nextCoeff / n₁
  set c₂ : ℂ := -f₂.nextCoeff / n₂
  set m : ℂ := (c₁ + c₂) / 2
  have hn₁0 : (n₁ : ℂ) ≠ 0 := by exact_mod_cast (show n₁ ≠ 0 by omega)
  have hn₂0 : (n₂ : ℂ) ≠ 0 := by exact_mod_cast (show n₂ ≠ 0 by omega)
  have hs₁ : -f₁.nextCoeff = n₁ * c₁ := by rw [mul_div_cancel₀ _ hn₁0]
  have hs₂ : -f₂.nextCoeff = n₂ * c₂ := by rw [mul_div_cancel₀ _ hn₂0]
  obtain ⟨S, hcard, hsum, hz, hall⟩ :=
    trace_identity H (r₁ : ℂ) (r₂ : ℂ) (by exact_mod_cast hr₂) m (conj m)
  -- the variance is `-(n₁ n₂ / 2) |c₁ - c₂|²`
  set v : ℝ := -(n₁ * n₂ / 2) * Complex.normSq (c₁ - c₂)
  have hv : v ≤ 0 := by
    have := Complex.normSq_nonneg (c₁ - c₂)
    have : (0 : ℝ) ≤ n₁ * n₂ / 2 := by positivity
    simp only [v]; nlinarith
  have hvar : (S.map (φ m)).sum = (v : ℂ) := by
    have e : (S.map (φ m)) = S.map fun p => (p.1 - m) * (p.2 - conj m) := rfl
    rw [e, hsum, conjP_nextCoeff, conjP_nextCoeff, conjP_natDegree, conjP_natDegree]
    have hc : (c₁ - c₂) * (conj c₁ - conj c₂) = (Complex.normSq (c₁ - c₂) : ℂ) := by
      rw [← Complex.mul_conj, map_sub]
    have h1 : -conj f₁.nextCoeff = n₁ * conj c₁ := by
      rw [← map_neg, hs₁, map_mul, Complex.conj_natCast]
    have h2 : -conj f₂.nextCoeff = n₂ * conj c₂ := by
      rw [← map_neg, hs₂, map_mul, Complex.conj_natCast]
    rw [hs₁, hs₂, h1, h2]
    simp only [v, m, map_div₀, map_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_ofNat]
    rw [Complex.conj_ofNat]
    linear_combination (-(n₁ : ℂ) * n₂ / 2) * hc
  -- `σ` permutes the solutions; real points are solutions
  have hσ : ∀ p ∈ S, σ p ∈ S := by
    intro p hp
    obtain ⟨h₁, h₂⟩ := hz p hp
    refine hall _ _ ?_ ?_
    · rw [eval_conj f₁ p.2, eval_conjP f₁ (conj p.1), Complex.conj_conj, ← map_mul, mul_comm, h₁,
        Complex.conj_ofReal]
    · rw [eval_conj f₂ p.2, eval_conjP f₂ (conj p.1), Complex.conj_conj, ← map_mul, mul_comm, h₂,
        Complex.conj_ofReal]
  have hreal : ∀ z ∈ F, (z, conj z) ∈ S := by
    intro z hz'
    obtain ⟨h₁, h₂⟩ := hF z hz'
    refine hall z (conj z) ?_ ?_
    · rw [eval_conjP, Complex.conj_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, h₁]
    · rw [eval_conjP, Complex.conj_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, h₂]
  have hN : S.card = 2 * n₁ * n₂ := by
    rw [hcard, conjP_natDegree, conjP_natDegree]; ring
  have h3 : 3 ≤ 2 * n₁ * n₂ := by nlinarith
  exact real_card_le m S hN h3 hσ hv hvar F hreal

end Lemniscates.CaseI
