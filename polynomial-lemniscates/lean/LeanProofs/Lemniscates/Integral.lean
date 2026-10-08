import LeanProofs.Lemniscates.ResTop
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Complex.Basic

/-!
# Integrality over the level (Lemma 4(a))

Let `B` be a commutative `ℂ`-algebra with elements `x, y, h` such that
`f(x) g(y) = h` and `f'(x) g'(y) = r`, where `f, f'` are monic of positive degree and `g, g'` are
coprime of positive degree. Then `x` is a root of a monic polynomial over `ℂ[t]`, with `t ↦ h`
(`exists_monic`).

*Proof.* In `ℂ[t][Z][W]` put `P = f(Z) g(W) - t` and `Q = f'(Z) g'(W) - r`. The resultant
`R = Res_W(P, Q) ∈ ℂ[t][Z]` lies in `(P, Q)` (Mathlib `exists_mul_add_mul_eq_C_resultant`), so it
vanishes at `Z = x, t = h`. By `ResTop.resultant_top`, `R` has `Z`-degree `deg g · deg f' +
deg g' · deg f` and top coefficient `Res(g, g') ≠ 0`; divide by it.

Applied with `(x, y) = (Z, W)` and with `(x, y) = (W, Z)` (roles of `f` and `g` swapped).
-/

open Polynomial

namespace Lemniscates.Integral

variable {B : Type*} [CommRing B] [Algebra ℂ B]

/-- `P = f(Z) g(W) - c` in `ℂ[t][Z][W]`, with `c ∈ ℂ[t]`. -/
noncomputable def lift (f g : ℂ[X]) (c : ℂ[X]) : ℂ[X][X][X] :=
  C (f.map C) * g.map (C.comp C) - C (C c)

lemma lift_coeff (f g : ℂ[X]) (c : ℂ[X]) (k : ℕ) :
    (lift f g c).coeff k = f.map C * C (C (g.coeff k)) - if k = 0 then C c else 0 := by
  simp only [lift, coeff_sub, coeff_C_mul, coeff_map, RingHom.comp_apply, coeff_C]

lemma lift_coeff_natDegree (f g : ℂ[X]) (c : ℂ[X]) (k : ℕ) :
    ((lift f g c).coeff k).natDegree ≤ f.natDegree := by
  rw [lift_coeff]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact natDegree_mul_le.trans (by simp)
  · split_ifs <;> simp

lemma lift_coeff_top (f g : ℂ[X]) (c : ℂ[X]) (hf : f.Monic) (hfd : 0 < f.natDegree) (k : ℕ) :
    ((lift f g c).coeff k).coeff f.natDegree = (g.map C).coeff k := by
  rw [lift_coeff, coeff_sub, coeff_mul_C, coeff_map, hf.coeff_natDegree, map_one, one_mul,
    coeff_map]
  split_ifs
  · simp [coeff_C, hfd.ne']
  · rw [coeff_zero, sub_zero]

lemma lift_natDegree (f g : ℂ[X]) (c : ℂ[X]) : (lift f g c).natDegree ≤ g.natDegree := by
  refine (natDegree_sub_le _ _).trans (max_le (natDegree_mul_le.trans ?_) (by simp))
  simp

/-- The evaluation `t ↦ h`, `Z ↦ x`, `W ↦ y`. -/
noncomputable def ψ (x y h : B) : ℂ[X][X][X] →+* B :=
  eval₂RingHom (eval₂RingHom (aeval h).toRingHom x) y

lemma ψ_C (x y h : B) (a : ℂ[X][X]) :
    ψ x y h (C a) = a.eval₂ (aeval h).toRingHom x := by
  simp [ψ]

lemma ψ_lift (x y h : B) (f g : ℂ[X]) (c : ℂ[X]) :
    ψ x y h (lift f g c) = aeval x f * aeval y g - aeval h c := by
  have h1 : ∀ a : ℂ, (eval₂RingHom (aeval h).toRingHom x) (C (C a)) = algebraMap ℂ B a := by
    intro a; simp
  have h0 : (aeval h).toRingHom.comp C = algebraMap ℂ B := RingHom.ext fun a => by simp
  have h1' : (eval₂RingHom (aeval h).toRingHom x).comp (C.comp C) = algebraMap ℂ B :=
    RingHom.ext h1
  simp only [ψ, lift, coe_eval₂RingHom, eval₂_sub, eval₂_mul, eval₂_C, eval₂_map, h0, h1',
    ← aeval_def]
  simp

theorem exists_monic (x y h : B) (f g f' g' : ℂ[X]) (r : ℂ) (hf : f.Monic) (hf' : f'.Monic)
    (hfd : 0 < f.natDegree) (hfd' : 0 < f'.natDegree) (hgd : 0 < g.natDegree)
    (hg : IsCoprime g g')
    (h₁ : aeval x f * aeval y g = h) (h₂ : aeval x f' * aeval y g' = algebraMap ℂ B r) :
    ∃ p : ℂ[X][X], p.Monic ∧ p.eval₂ (aeval h).toRingHom x = 0 := by
  set P := lift f g X
  set Q := lift f' g' (C r)
  set m := g.natDegree
  set n := g'.natDegree
  -- the resultant lies in `(P, Q)`, so it vanishes at `(x, y, h)`
  obtain ⟨u, v, -, -, huv⟩ := exists_mul_add_mul_eq_C_resultant P Q (m := m) (n := n)
    (lift_natDegree _ _ _) (lift_natDegree _ _ _) (Or.inl hgd.ne')
  have hP : ψ x y h P = 0 := by rw [ψ_lift, aeval_X, h₁, sub_self]
  have hQ : ψ x y h Q = 0 := by rw [ψ_lift, aeval_C, h₂, sub_self]
  have hR : (P.resultant Q m n).eval₂ (aeval h).toRingHom x = 0 := by
    have := congrArg (ψ x y h) huv
    rwa [map_add, map_mul, map_mul, hP, hQ, zero_mul, zero_mul, add_zero, ψ_C, eq_comm] at this
  -- its top coefficient is `Res(g, g') ≠ 0`
  obtain ⟨hdeg, htop⟩ := ResTop.resultant_top P Q m n f.natDegree f'.natDegree (g.map C)
    (g'.map C) (lift_coeff_natDegree _ _ _) (lift_coeff_natDegree _ _ _)
    (lift_coeff_top _ _ _ hf hfd) (lift_coeff_top _ _ _ hf' hfd')
  have hres : (g.map C).resultant (g'.map C) m n = C (g.resultant g') := by
    rw [resultant_map_map]
  have hne : g.resultant g' ≠ 0 := resultant_ne_zero g g' hg
  set R := P.resultant Q m n
  set N := m * f'.natDegree + n * f.natDegree
  have hcoeff : R.coeff N = C (g.resultant g') := htop.trans hres
  have hN : R.natDegree = N :=
    natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hcoeff]; exact C_ne_zero.mpr hne)
  have hlc : R.leadingCoeff = C (g.resultant g') := by rw [leadingCoeff, hN, hcoeff]
  refine ⟨C (C (g.resultant g')⁻¹) * R, ?_, ?_⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, hlc, ← C_mul, inv_mul_cancel₀ hne, C_1]
  · rw [eval₂_mul, hR, mul_zero]

end Lemniscates.Integral
