import LeanProofs.StanleySylow.Question

/-!
# The true Sylow polynomials

The cycle polynomial `P_n(q) = ∑_{w ∈ G_{2^n}} q^{κ(w)}` of a Sylow 2-subgroup of `S_{2^n}` obeys
the wreath-product recurrence `P_{n+1} = P_n (P_n + |G_{2^n}|)`, `|G_{2^n}| = 2^{2^n - 1} = a n`,
from `P_0 = q` (Pólya). This differs from the recurrence printed in MO 489315, which adds `a (n-1)`.
Here we prove, for the true family, the same three facts: the explicit factorization of
`P_{n+2} + |G_{2^{n+2}}|`, agreement of the two factors above degree `2^n`, and irreducibility of
both factors over `𝔽₅`, `ℤ` and `ℚ`, for every `n`. The question's family gets the coefficient
agreement too (`top_coeffs_agree`).
-/

noncomputable section
open Polynomial

namespace StanleySylow

/-- The Sylow cycle polynomials: `Ps 0 = X`, `Ps (n+1) = Ps n * (Ps n + |G_{2^n}|)`. -/
def Ps : ℕ → ℤ[X]
  | 0 => X
  | n+1 => Ps n * (Ps n + C (a n))

def AS (n : ℕ) : ℤ[X] := Ps (n+1) - C (2*a n) * Ps n + C (a (n+1))
def BS (n : ℕ) : ℤ[X] := Ps (n+1) + C (2*a n) * Ps n + C (2*a (n+1))

theorem Ps_succ_comp (n : ℕ) : Ps (n+1) = (quad (a n) 0).comp (Ps n) := by
  simp only [Ps, quad, add_comp, pow_comp, X_comp, mul_comp, C_comp, C_0, zero_comp]
  ring

theorem Ps_monic_degree (n : ℕ) : (Ps n).Monic ∧ (Ps n).natDegree = 2^n := by
  induction n with
  | zero => exact ⟨monic_X, by simp [Ps]⟩
  | succ n ih =>
    have hn : (Ps n).natDegree ≠ 0 := by rw [ih.2]; positivity
    rw [Ps_succ_comp]
    refine ⟨(quad_monic _ _).comp ih.1 hn, ?_⟩
    rw [natDegree_comp, quad_natDegree, ih.2, pow_succ]
    ring

theorem AS_comp (n : ℕ) : AS n = (quad (-a n) (2*a n^2)).comp (Ps n) := by
  simp only [AS, quad, add_comp, pow_comp, X_comp, mul_comp, C_comp]
  simp only [Ps, a, C_neg, C_mul, C_pow, C_ofNat]
  ring

theorem BS_comp (n : ℕ) : BS n = (quad (3*a n) (4*a n^2)).comp (Ps n) := by
  simp only [BS, quad, add_comp, pow_comp, X_comp, mul_comp, C_comp]
  simp only [Ps, a, C_mul, C_pow, C_ofNat]
  ring

/-- **Factorization.** `P_{n+2} + |G_{2^{n+2}}| = AS n * BS n`. -/
theorem sylow_factorization (n : ℕ) : AS n * BS n = Ps (n+2) + C (a (n+2)) := by
  rw [AS_comp, BS_comp]
  simp only [quad, add_comp, pow_comp, X_comp, mul_comp, C_comp]
  simp only [Ps, a, C_neg, C_mul, C_pow, C_ofNat]
  ring

theorem sylow_factors_monic (n : ℕ) : (AS n).Monic ∧ (BS n).Monic := by
  have hn : (Ps n).natDegree ≠ 0 := by rw [(Ps_monic_degree n).2]; positivity
  rw [AS_comp, BS_comp]
  exact ⟨(quad_monic _ _).comp (Ps_monic_degree n).1 hn,
    (quad_monic _ _).comp (Ps_monic_degree n).1 hn⟩

theorem sylow_factors_degree (n : ℕ) :
    (AS n).natDegree = 2^(n+1) ∧ (BS n).natDegree = 2^(n+1) := by
  rw [AS_comp, BS_comp, natDegree_comp, natDegree_comp, quad_natDegree,
    quad_natDegree, (Ps_monic_degree n).2, pow_succ]
  constructor <;> ring

/-- **Agreement of the top coefficients.** The two factors, of degree `2^(n+1)`, have the same
coefficient in every degree above `2^n`. -/
theorem sylow_top_coeffs_agree (n i : ℕ) (hi : 2 ^ n < i) : (AS n).coeff i = (BS n).coeff i := by
  have hd : BS n - AS n = C (4 * a n) * Ps n + C (a (n+1)) := by
    simp only [AS, BS, a, C_mul, C_pow, C_ofNat]; ring
  have hle : (C (4 * a n) * Ps n + C (a (n+1))).natDegree ≤ 2^n := by
    refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
    exact (natDegree_C_mul_le _ _).trans (Ps_monic_degree n).2.le
  have h0 : (BS n - AS n).coeff i = 0 := by
    rw [hd]; exact coeff_eq_zero_of_natDegree_lt (by omega)
  rw [coeff_sub] at h0
  linarith

/-- The question's family has the same agreement, above degree `2^(n+1)` of `2^(n+2)`. -/
theorem top_coeffs_agree (n i : ℕ) (hi : 2 ^ (n + 1) < i) : (A n).coeff i = (B n).coeff i := by
  have hd : B n - A n = C (4 * a n) * f n + C (a (n+1)) := by
    simp only [A, B, a, C_mul, C_pow, C_ofNat]; ring
  have hle : (C (4 * a n) * f n + C (a (n+1))).natDegree ≤ 2^(n+1) := by
    refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
    exact (natDegree_C_mul_le _ _).trans (f_monic_degree n).2.le
  have h0 : (B n - A n).coeff i = 0 := by
    rw [hd]; exact coeff_eq_zero_of_natDegree_lt (by omega)
  rw [coeff_sub] at h0
  linarith

/-! ## Reduction modulo 5 -/

def Ps5 (n : ℕ) : F5[X] := (Ps n).map reduce5

theorem Ps5_one : Ps5 1 = W := by
  change (Ps (0+1)).map reduce5 = _
  rw [Ps_succ_comp, map_comp, map_quad]
  have ha : reduce5 (a 0) = 1 := by norm_num [a, reduce5]
  rw [ha, _root_.map_zero]
  simp [Ps, W]

theorem Ps5_two : Ps5 2 = V.comp W := by
  change (Ps (1+1)).map reduce5 = _
  rw [Ps_succ_comp, map_comp, map_quad]
  have ha : reduce5 (a 1) = 2 := by norm_num [a, reduce5]
  rw [ha, _root_.map_zero]
  change V.comp (Ps5 1) = _
  rw [Ps5_one]

theorem Ps5_succ (k : ℕ) : Ps5 (k+3) = S.comp (Ps5 (k+2)) := by
  change (Ps (k+2+1)).map reduce5 = _
  rw [Ps_succ_comp, map_comp, map_quad, a_mod5, _root_.map_zero]
  rfl

theorem sylow_tail_formula (H : F5[X]) (k : ℕ) :
    H.comp (Ps5 (k+2)) = ((tower H k).comp V).comp W := by
  induction k generalizing H with
  | zero => rw [Ps5_two, ← comp_assoc]; rfl
  | succ k ih =>
    rw [show k+1+2 = k+3 by omega, Ps5_succ, ← comp_assoc, ih, tower_shift]

/-- One quadratic step less than `tail_irred`: `tower H k ∘ V ∘ W` is irreducible. -/
theorem tail1_irred {H : F5[X]} (hm : H.Monic) (hi : Irreducible H)
    (he : Even H.natDegree) (h3 : ¬ IsSquare (H.eval 3))
    (h4 : ¬ IsSquare (H.eval 4)) (k : ℕ) :
    Irreducible (((tower H k).comp V).comp W) := by
  rcases tower_properties hm hi he h3 h4 k with ⟨tm, ti, te, t3, t4⟩
  have vm := tm.comp (quad_monic (2 : F5) 0) (by rw [quad_natDegree]; decide)
  have vi : Irreducible ((tower H k).comp V) := by
    apply monic_comp_quad two_ne_zero tm ti te 2 0
    rw [show (0 - (2 : F5)^2 / 4) = 4 by simp only [div_eq_mul_inv, inv_four]; decide]
    exact t4
  have ve : Even ((tower H k).comp V).natDegree := by
    rw [natDegree_comp, show V.natDegree = 2 from quad_natDegree 2 0]
    exact ⟨(tower H k).natDegree, by omega⟩
  apply monic_comp_quad two_ne_zero vm vi ve 1 0
  simpa only [Polynomial.eval_comp, V, eval_quad, show (0 - (1 : F5)^2/4) = 1 by
    simp only [div_eq_mul_inv, inv_four]; decide, show ((1 : F5)^2 + 2*1 + 0) = 3 by decide]
    using t3

theorem AS5_tail (k : ℕ) : (AS (k+2)).map reduce5 =
    ((tower (quad (2 : F5) 3) k).comp V).comp W := by
  rw [AS_comp, map_comp, map_quad]
  have hb : reduce5 (-a (k+2)) = 2 := by rw [_root_.map_neg, a_mod5]; decide
  have hc : reduce5 (2*a (k+2)^2) = 3 := by
    rw [_root_.map_mul, _root_.map_pow, a_mod5]; norm_num [reduce5]; decide
  rw [hb, hc]
  exact sylow_tail_formula _ k

theorem BS5_tail (k : ℕ) : (BS (k+2)).map reduce5 =
    ((tower (quad (4 : F5) 1) k).comp V).comp W := by
  rw [BS_comp, map_comp, map_quad]
  have hb : reduce5 (3*a (k+2)) = 4 := by
    rw [_root_.map_mul, a_mod5]; norm_num [reduce5]; decide
  have hc : reduce5 (4*a (k+2)^2) = 1 := by
    rw [_root_.map_mul, _root_.map_pow, a_mod5]; norm_num [reduce5]; decide
  rw [hb, hc]
  exact sylow_tail_formula _ k

theorem AS5_zero : (AS 0).map reduce5 = quad (4 : F5) 2 := by
  rw [AS_comp, map_comp, map_quad]
  have hb : reduce5 (-a 0) = 4 := by norm_num [a, reduce5]; decide
  have hc : reduce5 (2*a 0^2) = 2 := by norm_num [a, reduce5]
  rw [hb, hc]
  simp [Ps]

theorem BS5_zero : (BS 0).map reduce5 = quad (3 : F5) 4 := by
  rw [BS_comp, map_comp, map_quad]
  have hb : reduce5 (3*a 0) = 3 := by norm_num [a, reduce5]
  have hc : reduce5 (4*a 0^2) = 4 := by norm_num [a, reduce5]
  rw [hb, hc]
  simp [Ps]

theorem AS5_one : (AS 1).map reduce5 = (quad (3 : F5) 3).comp W := by
  rw [AS_comp, map_comp, map_quad]
  have hb : reduce5 (-a 1) = 3 := by norm_num [a, reduce5]; decide
  have hc : reduce5 (2*a 1^2) = 3 := by norm_num [a, reduce5]; decide
  rw [hb, hc]
  change (quad (3 : F5) 3).comp (Ps5 1) = _
  rw [Ps5_one]

theorem BS5_one : (BS 1).map reduce5 = (quad (1 : F5) 1).comp W := by
  rw [BS_comp, map_comp, map_quad]
  have hb : reduce5 (3*a 1) = 1 := by norm_num [a, reduce5]; decide
  have hc : reduce5 (4*a 1^2) = 1 := by norm_num [a, reduce5]; decide
  rw [hb, hc]
  change (quad (1 : F5) 1).comp (Ps5 1) = _
  rw [Ps5_one]

theorem sylow_irreducible_mod5 (n : ℕ) :
    Irreducible ((AS n).map reduce5) ∧ Irreducible ((BS n).map reduce5) := by
  rcases n with _ | n
  · rw [AS5_zero, BS5_zero]
    exact ⟨quad_irred_five _ _ (by simp only [eval_quad]; decide),
      quad_irred_five _ _ (by simp only [eval_quad]; decide)⟩
  rcases n with _ | k
  · rw [AS5_one, BS5_one]
    constructor
    · apply one_W_irred (quad_monic _ _) ?_ ?_ ?_
      · apply quad_irred_five; simp only [eval_quad]; decide
      · rw [quad_natDegree]; decide
      · simp only [eval_quad]; decide
    · apply one_W_irred (quad_monic _ _) ?_ ?_ ?_
      · apply quad_irred_five; simp only [eval_quad]; decide
      · rw [quad_natDegree]; decide
      · simp only [eval_quad]; decide
  · rw [AS5_tail, BS5_tail]
    constructor
    · apply tail1_irred (quad_monic _ _) ?_ ?_ ?_ ?_ k
      · apply quad_irred_five; simp only [eval_quad]; decide
      · rw [quad_natDegree]; decide
      · convert ns_three using 1; simp only [eval_quad]; decide
      · convert ns_two using 1; simp only [eval_quad]; decide
    · apply tail1_irred (quad_monic _ _) ?_ ?_ ?_ ?_ k
      · apply quad_irred_five; simp only [eval_quad]; decide
      · rw [quad_natDegree]; decide
      · convert ns_two using 1; simp only [eval_quad]; decide
      · convert ns_three using 1; simp only [eval_quad]; decide

/-- **Irreducibility over `ℚ`** of both factors of `P_{n+2} + |G_{2^{n+2}}|`, for every `n`. -/
theorem sylow_irreducible_rat (n : ℕ) :
    Irreducible ((AS n).map (algebraMap ℤ ℚ)) ∧ Irreducible ((BS n).map (algebraMap ℤ ℚ)) := by
  have hm := sylow_factors_monic n
  have hi := sylow_irreducible_mod5 n
  have hz : Irreducible (AS n) ∧ Irreducible (BS n) :=
    ⟨hm.1.irreducible_of_irreducible_map reduce5 (AS n) hi.1,
      hm.2.irreducible_of_irreducible_map reduce5 (BS n) hi.2⟩
  exact ⟨hm.1.irreducible_iff_irreducible_map_fraction_map.mp hz.1,
    hm.2.irreducible_iff_irreducible_map_fraction_map.mp hz.2⟩

/-- The initial cases: `P_2 + 8 = (q² - q + 2)(q² + 3q + 4)`, and `P_2` is the cycle polynomial of
the dihedral group of order 8 acting on the corners of a square. -/
example : Ps 2 = X^4 + C 2 * X^3 + C 3 * X^2 + C 2 * X := by
  simp only [Ps, a]; norm_num [C_ofNat]; ring

example : AS 0 = X^2 - X + C 2 ∧ BS 0 = X^2 + C 3 * X + C 4 := by
  constructor <;> simp only [AS, BS, Ps, a] <;> norm_num [C_mul, C_ofNat, C_1] <;> ring

end StanleySylow
