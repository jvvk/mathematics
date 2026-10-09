import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod

/-!
# Irreducibility of the factors in MathOverflow 489315

The field-norm argument and quadratic-composition criterion are proved below.
Their application over `ZMod 5` proves irreducibility of both explicit factors
at every level, followed by descent to integer and rational polynomials.

The final `stanley_*` declarations use the original indexing. Internal `f n`
represents the question's `f_{n+1}`; internal `A n`, `B n` are its factors at n+3.
The Sylow-group interpretation and leading-coefficient agreement are outside
this formalization.
-/

noncomputable section
open Polynomial

namespace StanleySylow

theorem norm_sub_eval {K L : Type*} [Field K] [Field L] [Algebra K L]
    (pb : PowerBasis K L) (v : K) (he : Even pb.dim) :
    Algebra.norm K (pb.gen - algebraMap K L v) = (minpoly K pb.gen).eval v := by
  let y := pb.gen - algebraMap K L v
  have hy : IsIntegral K y := pb.isIntegral_gen.sub (isIntegral_algebraMap)
  have ht : Algebra.adjoin K ({y} : Set L) = ⊤ := by
    apply pb.adjoin_eq_top_of_gen_mem_adjoin
    have hm : y ∈ Algebra.adjoin K ({y} : Set L) :=
      Algebra.subset_adjoin (Set.mem_singleton y)
    have ha := (Algebra.adjoin K ({y} : Set L)).algebraMap_mem v
    convert (Algebra.adjoin K ({y} : Set L)).add_mem hm ha using 1
    dsimp [y]
    ring
  let pb' := PowerBasis.ofAdjoinEqTop hy ht
  have hd : pb'.dim = pb.dim := by
    simp only [pb', PowerBasis.ofAdjoinEqTop_dim, y, minpoly.sub_algebraMap,
      natDegree_comp, natDegree_X_add_C, mul_one, pb.natDegree_minpoly]
  have hn := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb'
  simpa only [pb', PowerBasis.ofAdjoinEqTop_gen, hd, he.neg_one_pow, one_mul,
    y, minpoly.sub_algebraMap, coeff_zero_eq_eval_zero, eval_comp,
    eval_add, eval_X, eval_C, zero_add] using hn

def quad {R : Type*} [Ring R] (b c : R) : R[X] := X^2 + C b * X + C c

theorem quad_monic {R : Type*} [Ring R] (b c : R) : (quad b c).Monic := by
  unfold quad
  monicity!

theorem quad_natDegree {K : Type*} [CommRing K] [Nontrivial K] (b c : K) :
    (quad b c).natDegree = 2 := by
  unfold quad
  compute_degree!

theorem monic_comp_quad {K : Type*} [Field K] (htwo : (2 : K) ≠ 0)
    {G : K[X]} (hm : G.Monic) (hi : Irreducible G) (he : Even G.natDegree)
    (b c : K) (hn : ¬ IsSquare (G.eval (c - b^2/4))) :
    Irreducible (G.comp (quad b c)) := by
  apply Polynomial.irreducible_comp hm (quad_monic b c) hi
  intro E _ _ x hx
  have hxint : IsIntegral K x := by
    apply (minpoly.ne_zero_iff).mp
    rw [hx]
    exact hm.ne_zero
  let pb := IntermediateField.adjoin.powerBasis hxint
  have hmp : minpoly K pb.gen = G := by
    simp only [pb, IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.minpoly_gen, hx]
  have hdim : Even pb.dim := by
    simpa only [pb, IntermediateField.adjoin.powerBasis_dim, hx] using he
  have hnorm := norm_sub_eval pb (c-b^2/4) hdim
  rw [hmp] at hnorm
  have hns : ¬ IsSquare (pb.gen - algebraMap K _ (c-b^2/4)) := by
    intro hs
    exact hn (hnorm ▸ hs.map (Algebra.norm K))
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (map (algebraMap K ↥(IntermediateField.adjoin K {x})) (quad b c) -
      C (IntermediateField.AdjoinSimple.gen K x)).natDegree = 2 := by
      have hpoly : map (algebraMap K ↥(IntermediateField.adjoin K {x})) (quad b c) -
          C (IntermediateField.AdjoinSimple.gen K x) =
          quad (algebraMap K _ b)
            (algebraMap K _ c - IntermediateField.AdjoinSimple.gen K x) := by
        simp only [quad, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
          Polynomial.map_X, Polynomial.map_C, C_sub]
        ring
      rw [hpoly, quad_natDegree]
    simp [hd]
  · intro z hz
    apply hns
    let bb := algebraMap K ↥(IntermediateField.adjoin K {x}) b
    have h2 : (2 : ↥(IntermediateField.adjoin K {x})) ≠ 0 := by
      intro h
      apply htwo
      apply (algebraMap K ↥(IntermediateField.adjoin K {x})).injective
      simpa only [map_ofNat, map_zero] using h
    have h4 : (4 : ↥(IntermediateField.adjoin K {x})) ≠ 0 := by
      convert mul_ne_zero h2 h2 using 1
      norm_num
    have hroot : z^2 + bb*z + algebraMap K _ c - pb.gen = 0 := by
      simpa [Polynomial.IsRoot, quad, pb, bb, eval_map, eval₂_add, eval₂_mul,
        eval₂_pow, eval₂_X, eval₂_C, IntermediateField.adjoin.powerBasis_gen] using hz
    refine ⟨z + bb/2, ?_⟩
    simp only [map_sub, map_div₀, map_pow, map_ofNat]
    dsimp [bb] at *
    field_simp [h2, h4]
    linear_combination -16 * hroot

abbrev F5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by decide⟩
@[simp] theorem eval_quad {R : Type*} [CommRing R] (b c x : R) :
    (quad b c).eval x = x^2 + b*x + c := by
  simp only [quad, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]

def S : F5[X] := quad 3 0
def V : F5[X] := quad 2 0
def W : F5[X] := quad 1 0

theorem two_ne_zero : (2 : F5) ≠ 0 := by decide
theorem inv_four : (4 : F5)⁻¹ = 4 := by
  apply inv_eq_of_mul_eq_one_left
  decide

theorem ns_two : ¬ IsSquare (2 : F5) := by decide
theorem ns_three : ¬ IsSquare (3 : F5) := by decide

theorem quad_irred_five (b c : F5) (hn : ∀ x : F5, (quad b c).eval x ≠ 0) :
    Irreducible (quad b c) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [quad_natDegree]
  · exact hn

def tower (H : F5[X]) : ℕ → F5[X]
  | 0 => H
  | k+1 => (tower H k).comp S

theorem tower_properties {H : F5[X]} (hm : H.Monic) (hi : Irreducible H)
    (he : Even H.natDegree) (h3 : ¬ IsSquare (H.eval 3))
    (h4 : ¬ IsSquare (H.eval 4)) (k : ℕ) :
    (tower H k).Monic ∧ Irreducible (tower H k) ∧ Even (tower H k).natDegree ∧
    ¬ IsSquare ((tower H k).eval 3) ∧ ¬ IsSquare ((tower H k).eval 4) := by
  induction k with
  | zero => exact ⟨hm, hi, he, h3, h4⟩
  | succ k ih =>
    rcases ih with ⟨ihm, ihi, ihe, ih3, ih4⟩
    have ic : Irreducible ((tower H k).comp S) := by
      apply monic_comp_quad two_ne_zero ihm ihi ihe 3 0
      rw [show (0 - (3 : F5)^2 / 4) = 4 by simp only [div_eq_mul_inv, inv_four]; decide]; exact ih4
    refine ⟨ihm.comp (quad_monic 3 0)
      (by change (quad (3 : F5) 0).natDegree ≠ 0; rw [quad_natDegree]; decide), ic, ?_, ?_, ?_⟩
    · rw [tower, natDegree_comp, show S.natDegree = 2 from quad_natDegree 3 0]
      exact ⟨(tower H k).natDegree, by omega⟩
    · simpa only [tower, Polynomial.eval_comp, S, eval_quad,
        show (3^2 + 3*3 + 0 : F5) = 3 by decide, show (4^2 + 3*4 + 0 : F5) = 3 by decide] using ih3
    · simpa only [tower, Polynomial.eval_comp, S, eval_quad,
        show (3^2 + 3*3 + 0 : F5) = 3 by decide, show (4^2 + 3*4 + 0 : F5) = 3 by decide] using ih3

theorem tail_irred {H : F5[X]} (hm : H.Monic) (hi : Irreducible H)
    (he : Even H.natDegree) (h3 : ¬ IsSquare (H.eval 3))
    (h4 : ¬ IsSquare (H.eval 4)) (k : ℕ) :
    Irreducible ((((tower H k).comp V).comp W).comp W) := by
  rcases tower_properties hm hi he h3 h4 k with ⟨tm, ti, te, t3, t4⟩
  have vm := tm.comp (quad_monic (2 : F5) 0) (by rw [quad_natDegree]; decide)
  have vi : Irreducible ((tower H k).comp V) := by
    apply monic_comp_quad two_ne_zero tm ti te 2 0
    rw [show (0 - (2 : F5)^2 / 4) = 4 by simp only [div_eq_mul_inv, inv_four]; decide]; exact t4
  have ve : Even ((tower H k).comp V).natDegree := by
    rw [natDegree_comp, show V.natDegree = 2 from quad_natDegree 2 0]
    exact ⟨(tower H k).natDegree, by omega⟩
  have wi : Irreducible (((tower H k).comp V).comp W) := by
    apply monic_comp_quad two_ne_zero vm vi ve 1 0
    simpa only [Polynomial.eval_comp, V, eval_quad,
      show (0 - (1 : F5)^2/4) = 1 by simp only [div_eq_mul_inv, inv_four]; decide,
      show ((1 : F5)^2 + 2*1 + 0) = 3 by decide] using t3
  have wm := vm.comp (quad_monic (1 : F5) 0) (by rw [quad_natDegree]; decide)
  have we : Even (((tower H k).comp V).comp W).natDegree := by
    rw [natDegree_comp, show W.natDegree = 2 from quad_natDegree 1 0]
    exact ⟨((tower H k).comp V).natDegree, by omega⟩
  apply monic_comp_quad two_ne_zero wm wi we 1 0
  simpa only [Polynomial.eval_comp, V, W, eval_quad,
    show (0 - (1 : F5)^2/4) = 1 by simp only [div_eq_mul_inv, inv_four]; decide,
    show ((1 : F5)^2 + 1*1 + 0) = 2 by decide,
    show ((2 : F5)^2 + 2*2 + 0) = 3 by decide] using t3

theorem tail_minus_irred (k : ℕ) :
    Irreducible ((((tower (quad (2 : F5) 3) k).comp V).comp W).comp W) := by
  apply tail_irred (quad_monic _ _) ?_ ?_ ?_ ?_ k
  · apply quad_irred_five
    simp only [eval_quad]
    decide
  · rw [quad_natDegree]; decide
  · convert ns_three using 1; simp only [eval_quad]; decide
  · convert ns_two using 1; simp only [eval_quad]; decide

theorem tail_plus_irred (k : ℕ) :
    Irreducible ((((tower (quad (4 : F5) 1) k).comp V).comp W).comp W) := by
  apply tail_irred (quad_monic _ _) ?_ ?_ ?_ ?_ k
  · apply quad_irred_five
    simp only [eval_quad]
    decide
  · rw [quad_natDegree]; decide
  · convert ns_two using 1; simp only [eval_quad]; decide
  · convert ns_three using 1; simp only [eval_quad]; decide

/-! Indexing: `a n` is a_{n+1} and `f n` is f_{n+1} in the MO question.
`A n` and `B n` are the two factors for the question's index n+3. -/
def a : ℕ → ℤ
  | 0 => 1
  | n+1 => 2 * a n ^ 2

def f : ℕ → ℤ[X]
  | 0 => quad 1 0
  | n+1 => f n * (f n + C (a n))

def A (n : ℕ) : ℤ[X] := f (n+1) - C (2*a n) * f n + C (a (n+1))
def B (n : ℕ) : ℤ[X] := f (n+1) + C (2*a n) * f n + C (2*a (n+1))

theorem a_closed (n : ℕ) : a n = (2 : ℤ) ^ (2^n-1) := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have hp : 1 ≤ 2^n := Nat.one_le_pow n 2 (by decide)
    have he : 2^(n+1)-1 = 1 + (2^n-1)*2 := by rw [pow_succ]; omega
    rw [a, ih, he, pow_add, pow_mul]
    simp only [pow_one]

theorem f_succ_comp (n : ℕ) : f (n+1) = (quad (a n) 0).comp (f n) := by
  simp only [f, quad, add_comp, pow_comp, X_comp, mul_comp, C_comp]
  simp only [C_0]
  ring

theorem f_monic_degree (n : ℕ) : (f n).Monic ∧ (f n).natDegree = 2^(n+1) := by
  induction n with
  | zero => exact ⟨quad_monic 1 0, by simp [f, quad_natDegree]⟩
  | succ n ih =>
    have hn : (f n).natDegree ≠ 0 := by rw [ih.2]; positivity
    rw [f_succ_comp]
    refine ⟨(quad_monic _ _).comp ih.1 hn, ?_⟩
    rw [natDegree_comp, quad_natDegree, ih.2, pow_succ]
    ring

theorem A_comp (n : ℕ) : A n = (quad (-a n) (2*a n^2)).comp (f n) := by
  simp only [A, quad, add_comp, pow_comp, X_comp, mul_comp, C_comp]
  simp only [f, a, C_neg, C_mul, C_pow, C_ofNat]
  ring

theorem B_comp (n : ℕ) : B n = (quad (3*a n) (4*a n^2)).comp (f n) := by
  simp only [B, quad, add_comp, pow_comp, X_comp, mul_comp, C_comp]
  simp only [f, a, C_mul, C_pow, C_ofNat]
  ring

theorem factorization (n : ℕ) : A n * B n = f (n+2) + C (a (n+2)) := by
  rw [A_comp, B_comp]
  simp only [quad, add_comp, pow_comp, X_comp, mul_comp, C_comp]
  simp only [f, a, C_neg, C_mul, C_pow, C_ofNat]
  ring

theorem factors_monic (n : ℕ) : (A n).Monic ∧ (B n).Monic := by
  have hn : (f n).natDegree ≠ 0 := by rw [(f_monic_degree n).2]; positivity
  rw [A_comp, B_comp]
  exact ⟨(quad_monic _ _).comp (f_monic_degree n).1 hn,
    (quad_monic _ _).comp (f_monic_degree n).1 hn⟩

theorem factors_degree (n : ℕ) : (A n).natDegree = 2^(n+2) ∧
    (B n).natDegree = 2^(n+2) := by
  rw [A_comp, B_comp, natDegree_comp, natDegree_comp, quad_natDegree,
    quad_natDegree, (f_monic_degree n).2, pow_succ]
  constructor <;> ring

abbrev reduce5 : ℤ →+* F5 := Int.castRingHom F5
def f5 (n : ℕ) : F5[X] := (f n).map reduce5

theorem a_mod5 (k : ℕ) : reduce5 (a (k+2)) = 3 := by
  induction k with
  | zero => norm_num [a, reduce5]; decide
  | succ k ih =>
    change reduce5 (2 * a (k+2)^2) = 3
    rw [map_mul, map_pow, ih]
    norm_num [reduce5]
    decide

theorem map_quad {R U : Type*} [CommRing R] [CommRing U] (φ : R →+* U) (b c : R) :
    (quad b c).map φ = quad (φ b) (φ c) := by
  simp only [quad, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]

theorem f5_zero : f5 0 = W := by
  simp only [f5, f, map_quad]
  rfl

theorem f5_one : f5 1 = W.comp W := by
  change (f (0+1)).map reduce5 = _
  rw [f_succ_comp, map_comp, map_quad]
  change W.comp (f5 0) = _
  rw [f5_zero]

theorem f5_two : f5 2 = (V.comp W).comp W := by
  change (f (1+1)).map reduce5 = _
  rw [f_succ_comp, map_comp, map_quad]
  have ha : reduce5 (a 1) = 2 := by norm_num [a, reduce5]
  rw [ha, _root_.map_zero]
  change V.comp (f5 1) = _
  rw [f5_one, ← comp_assoc]

theorem f5_succ (k : ℕ) : f5 (k+3) = S.comp (f5 (k+2)) := by
  change (f (k+2+1)).map reduce5 = _
  rw [f_succ_comp, map_comp, map_quad, a_mod5, _root_.map_zero]
  rfl

theorem tower_shift (H : F5[X]) (k : ℕ) : tower (H.comp S) k = tower H (k+1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [tower, ih]

theorem tail_formula (H : F5[X]) (k : ℕ) :
    H.comp (f5 (k+2)) = (((tower H k).comp V).comp W).comp W := by
  induction k generalizing H with
  | zero => rw [f5_two, ← comp_assoc, ← comp_assoc]; rfl
  | succ k ih =>
    rw [show k+1+2 = k+3 by omega, f5_succ, ← comp_assoc, ih, tower_shift]

theorem A5_tail (k : ℕ) : (A (k+2)).map reduce5 =
    (((tower (quad (2 : F5) 3) k).comp V).comp W).comp W := by
  rw [A_comp, map_comp, map_quad]
  have hb : reduce5 (-a (k+2)) = 2 := by
    rw [_root_.map_neg, a_mod5]; decide
  have hc : reduce5 (2*a (k+2)^2) = 3 := by
    rw [_root_.map_mul, _root_.map_pow, a_mod5]
    norm_num [reduce5]
    decide
  rw [hb, hc]
  exact tail_formula _ k

theorem B5_tail (k : ℕ) : (B (k+2)).map reduce5 =
    (((tower (quad (4 : F5) 1) k).comp V).comp W).comp W := by
  rw [B_comp, map_comp, map_quad]
  have hb : reduce5 (3*a (k+2)) = 4 := by
    rw [_root_.map_mul, a_mod5]
    norm_num [reduce5]
    decide
  have hc : reduce5 (4*a (k+2)^2) = 1 := by
    rw [_root_.map_mul, _root_.map_pow, a_mod5]
    norm_num [reduce5]
    decide
  rw [hb, hc]
  exact tail_formula _ k

theorem one_W_irred {H : F5[X]} (hm : H.Monic) (hi : Irreducible H)
    (he : Even H.natDegree) (h1 : ¬ IsSquare (H.eval 1)) :
    Irreducible (H.comp W) := by
  apply monic_comp_quad two_ne_zero hm hi he 1 0
  simpa only [show (0 - (1 : F5)^2/4) = 1 by
    simp only [div_eq_mul_inv, inv_four]; decide] using h1

theorem two_W_irred {H : F5[X]} (hm : H.Monic) (hi : Irreducible H)
    (he : Even H.natDegree) (h1 : ¬ IsSquare (H.eval 1))
    (h2 : ¬ IsSquare (H.eval 2)) : Irreducible ((H.comp W).comp W) := by
  apply one_W_irred (hm.comp (quad_monic 1 0) (by rw [quad_natDegree]; decide))
    (one_W_irred hm hi he h1)
  · rw [natDegree_comp, quad_natDegree]
    exact ⟨H.natDegree, by omega⟩
  · simpa only [Polynomial.eval_comp, W, eval_quad,
      show ((1 : F5)^2+1*1+0) = 2 by decide] using h2

theorem A5_zero : (A 0).map reduce5 = (quad (4 : F5) 2).comp W := by
  rw [A_comp, map_comp, map_quad]
  have hb : reduce5 (-a 0) = 4 := by norm_num [a, reduce5]; decide
  have hc : reduce5 (2*a 0^2) = 2 := by norm_num [a, reduce5]
  rw [hb, hc]
  exact congrArg ((quad (4 : F5) 2).comp) f5_zero

theorem B5_zero : (B 0).map reduce5 = (quad (3 : F5) 4).comp W := by
  rw [B_comp, map_comp, map_quad]
  have hb : reduce5 (3*a 0) = 3 := by norm_num [a, reduce5]
  have hc : reduce5 (4*a 0^2) = 4 := by norm_num [a, reduce5]
  rw [hb, hc]
  exact congrArg ((quad (3 : F5) 4).comp) f5_zero

theorem A5_one : (A 1).map reduce5 = ((quad (3 : F5) 3).comp W).comp W := by
  rw [A_comp, map_comp, map_quad]
  have hb : reduce5 (-a 1) = 3 := by norm_num [a, reduce5]; decide
  have hc : reduce5 (2*a 1^2) = 3 := by norm_num [a, reduce5]; decide
  rw [hb, hc]
  change (quad (3 : F5) 3).comp (f5 1) = _
  rw [f5_one, ← comp_assoc]

theorem B5_one : (B 1).map reduce5 = ((quad (1 : F5) 1).comp W).comp W := by
  rw [B_comp, map_comp, map_quad]
  have hb : reduce5 (3*a 1) = 1 := by norm_num [a, reduce5]; decide
  have hc : reduce5 (4*a 1^2) = 1 := by norm_num [a, reduce5]; decide
  rw [hb, hc]
  change (quad (1 : F5) 1).comp (f5 1) = _
  rw [f5_one, ← comp_assoc]

theorem factors_irreducible_mod5 (n : ℕ) :
    Irreducible ((A n).map reduce5) ∧ Irreducible ((B n).map reduce5) := by
  rcases n with _ | n
  · rw [A5_zero, B5_zero]
    constructor
    · apply one_W_irred (quad_monic _ _) ?_ ?_ ?_
      · apply quad_irred_five; simp only [eval_quad]; decide
      · rw [quad_natDegree]; decide
      · simp only [eval_quad]; decide
    · apply one_W_irred (quad_monic _ _) ?_ ?_ ?_
      · apply quad_irred_five; simp only [eval_quad]; decide
      · rw [quad_natDegree]; decide
      · simp only [eval_quad]; decide
  rcases n with _ | k
  · rw [A5_one, B5_one]
    constructor
    · apply two_W_irred (quad_monic _ _) ?_ ?_ ?_ ?_
      · apply quad_irred_five; simp only [eval_quad]; decide
      · rw [quad_natDegree]; decide
      · simp only [eval_quad]; decide
      · simp only [eval_quad]; decide
    · apply two_W_irred (quad_monic _ _) ?_ ?_ ?_ ?_
      · apply quad_irred_five; simp only [eval_quad]; decide
      · rw [quad_natDegree]; decide
      · simp only [eval_quad]; decide
      · simp only [eval_quad]; decide
  · rw [A5_tail, B5_tail]
    exact ⟨tail_minus_irred k, tail_plus_irred k⟩

theorem factors_irreducible_int (n : ℕ) : Irreducible (A n) ∧ Irreducible (B n) := by
  have hm := factors_monic n
  have hi := factors_irreducible_mod5 n
  exact ⟨Polynomial.Monic.irreducible_of_irreducible_map reduce5 (A n) hm.1 hi.1,
    Polynomial.Monic.irreducible_of_irreducible_map reduce5 (B n) hm.2 hi.2⟩

/-- The original two factors are irreducible over Q for every index n+3. -/
theorem factors_irreducible_rat (n : ℕ) :
    Irreducible ((A n).map (algebraMap ℤ ℚ)) ∧
    Irreducible ((B n).map (algebraMap ℤ ℚ)) := by
  have hm := factors_monic n
  have hi := factors_irreducible_int n
  exact ⟨hm.1.irreducible_iff_irreducible_map_fraction_map.mp hi.1,
    hm.2.irreducible_iff_irreducible_map_fraction_map.mp hi.2⟩

/-! The following definitions use exactly the question's indexing and coefficients. -/

def stanley_a (n : ℕ) : ℤ := 2 ^ (2^(n-1)-1)
def stanleyF (n : ℕ) : ℤ[X] := f (n-1)
def stanleyA (n : ℕ) : ℤ[X] :=
  stanleyF (n-1) - C (2 * stanley_a (n-2)) * stanleyF (n-2) + C (stanley_a (n-1))
def stanleyB (n : ℕ) : ℤ[X] :=
  stanleyF (n-1) + C (2 * stanley_a (n-2)) * stanleyF (n-2) + C (2 * stanley_a (n-1))

theorem stanleyF_one : stanleyF 1 = X^2 + X := by
  simp [stanleyF, f, quad]

theorem stanleyF_recurrence (n : ℕ) (hn : 1 ≤ n) :
    stanleyF (n+1) = stanleyF n * (stanleyF n + C (stanley_a n)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  simpa [stanleyF, stanley_a, a_closed] using (show f (k+1) = f k * (f k + C (a k)) from rfl)

theorem stanley_factors_eq (k : ℕ) : stanleyA (k+3) = A k ∧ stanleyB (k+3) = B k := by
  simp [stanleyA, stanleyB, stanleyF, stanley_a, A, B, a_closed,
    show k+3-1 = k+2 by omega, show k+3-2 = k+1 by omega]

/-- Both factors in Stanley's question are irreducible modulo 5 for every n ≥ 3. -/
theorem stanley_irreducible_mod5 (n : ℕ) (hn : 3 ≤ n) :
    Irreducible ((stanleyA n).map reduce5) ∧ Irreducible ((stanleyB n).map reduce5) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
  rw [(stanley_factors_eq k).1, (stanley_factors_eq k).2]
  exact factors_irreducible_mod5 k

/-- Both factors in Stanley's question are irreducible over Q for every n ≥ 3. -/
theorem stanley_irreducible_rat (n : ℕ) (hn : 3 ≤ n) :
    Irreducible ((stanleyA n).map (algebraMap ℤ ℚ)) ∧
    Irreducible ((stanleyB n).map (algebraMap ℤ ℚ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
  rw [(stanley_factors_eq k).1, (stanley_factors_eq k).2]
  exact factors_irreducible_rat k

/-- The explicit factorization in the original indexing. -/
theorem stanley_factorization (n : ℕ) (hn : 3 ≤ n) :
    stanleyA n * stanleyB n = stanleyF n + C (stanley_a n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
  rw [(stanley_factors_eq k).1, (stanley_factors_eq k).2]
  simpa [stanleyF, stanley_a, a_closed] using factorization k

/-- Both factors have the degrees stated in the original question. -/
theorem stanley_factors_degree (n : ℕ) (hn : 3 ≤ n) :
    (stanleyA n).natDegree = 2^(n-1) ∧ (stanleyB n).natDegree = 2^(n-1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
  rw [(stanley_factors_eq k).1, (stanley_factors_eq k).2]
  simpa using factors_degree k

end StanleySylow
