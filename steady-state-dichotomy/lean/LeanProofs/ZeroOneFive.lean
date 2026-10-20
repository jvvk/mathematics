/-
An eight-reaction quadratic zero-one network with exactly five positive, nondegenerate steady states, the
Bernstein maximum for this class (chem-tang-zhang-three-steady-states, session 5/6, 2026-10-16).

Reactions and rates: X1 → X1+X3 (5), X1 → X2 (1), X1+X3 → X1+X2+X3 (1), X1+X2 → X2 (1), X2+X3 → X1 (2/5),
X3 → 0 (1/2), 0 → X1+X2 (1/2500), X2 → X1 (1/100000). Concentrations (x, y, z).

Route (same shape as the four-state proof): f3 is linear in x and, after that substitution, 100000·f2 is linear in
y, so the curve f2 = f3 = 0 is rational in z: y = -N(z)/D(z), x = z(5+4y)/50. On it f1 = -E(z)/(1250 D(z)^2) with
E of degree five. Five sign changes give five roots; a quintic has at most five. At a root
det J = -M(z) E'(z)/(1250 D(z)^2) with M > 0, and E' has a fixed sign on each root interval.
-/
import Mathlib

namespace ZeroOneFive

open Polynomial Set

noncomputable section

def f1 (x y z : ℝ) : ℝ := 1 / 2500 - x - x * y + 2 / 5 * y * z + 1 / 100000 * y
def f2 (x y z : ℝ) : ℝ := 1 / 2500 + x + x * z - 2 / 5 * y * z - 1 / 100000 * y
def f3 (x y z : ℝ) : ℝ := 5 * x - z / 2 - 2 / 5 * y * z

/-- Mass action, reaction by reaction, in the order listed in the header. -/
theorem f_from_network (x y z : ℝ) :
    f1 x y z = -1 * x - 1 * x * y + 2 / 5 * y * z + 1 / 2500 + 1 / 100000 * y ∧
    f2 x y z = 1 * x + 1 * x * z - 2 / 5 * y * z + 1 / 2500 - 1 / 100000 * y ∧
    f3 x y z = 5 * x - 2 / 5 * y * z - 1 / 2 * z := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [f1, f2, f3] <;> ring

def D (z : ℝ) : ℝ := 8000 * z ^ 2 - 32000 * z - 1
def N (z : ℝ) : ℝ := 10000 * z ^ 2 + 10000 * z + 40
def Y (z : ℝ) : ℝ := -N z / D z
def X (z : ℝ) : ℝ := z * (5 + 4 * Y z) / 50
def E (z : ℝ) : ℝ :=
  40000000000 * z ^ 5 - 110031000000 * z ^ 4 + 50416250000 * z ^ 3 - 782738125 * z ^ 2 + 101000 * z - 1
def dE (z : ℝ) : ℝ :=
  200000000000 * z ^ 4 - 440124000000 * z ^ 3 + 151248750000 * z ^ 2 - 1565476250 * z + 101000
def M (z : ℝ) : ℝ := 8 / 5 * z - 2 / 5 * z ^ 2 + 1 / 20000

/-! ### The Jacobian -/

theorem hasDerivAt_affine (a b x : ℝ) (g : ℝ → ℝ) (hg : ∀ t, g t = a * t + b) : HasDerivAt g a x := by
  have h := ((hasDerivAt_id x).const_mul a).add_const b
  simp only [id, mul_one] at h
  rwa [show g = fun t => a * t + b from funext hg]

def jac (x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1 - y, -x + 2 / 5 * z + 1 / 100000, 2 / 5 * y;
     1 + z, -2 / 5 * z - 1 / 100000, x - 2 / 5 * y;
     5, -2 / 5 * z, -1 / 2 - 2 / 5 * y]

theorem jac_partials (x y z : ℝ) :
    HasDerivAt (fun t => f1 t y z) (jac x y z 0 0) x ∧ HasDerivAt (fun t => f1 x t z) (jac x y z 0 1) y ∧
    HasDerivAt (fun t => f1 x y t) (jac x y z 0 2) z ∧ HasDerivAt (fun t => f2 t y z) (jac x y z 1 0) x ∧
    HasDerivAt (fun t => f2 x t z) (jac x y z 1 1) y ∧ HasDerivAt (fun t => f2 x y t) (jac x y z 1 2) z ∧
    HasDerivAt (fun t => f3 t y z) (jac x y z 2 0) x ∧ HasDerivAt (fun t => f3 x t z) (jac x y z 2 1) y ∧
    HasDerivAt (fun t => f3 x y t) (jac x y z 2 2) z := by
  refine ⟨hasDerivAt_affine _ (1 / 2500 + 2 / 5 * y * z + 1 / 100000 * y) _ _ ?_,
    hasDerivAt_affine _ (1 / 2500 - x) _ _ ?_, hasDerivAt_affine _ (1 / 2500 - x - x * y + 1 / 100000 * y) _ _ ?_,
    hasDerivAt_affine _ (1 / 2500 - 2 / 5 * y * z - 1 / 100000 * y) _ _ ?_,
    hasDerivAt_affine _ (1 / 2500 + x + x * z) _ _ ?_, hasDerivAt_affine _ (1 / 2500 + x - 1 / 100000 * y) _ _ ?_,
    hasDerivAt_affine _ (-z / 2 - 2 / 5 * y * z) _ _ ?_, hasDerivAt_affine _ (5 * x - z / 2) _ _ ?_,
    hasDerivAt_affine _ (5 * x) _ _ ?_⟩ <;>
    intro t <;> simp [jac, f1, f2, f3] <;> ring

def detJ (x y z : ℝ) : ℝ :=
  -5 * x ^ 2 - 4 / 5 * x * y * z + 8 / 5 * x * y + 11 / 10 * x * z - 9999 / 20000 * x - y ^ 2 / 250000 -
    49999 / 250000 * y * z - y / 200000 + z ^ 2 / 5 + z / 200000

theorem det_jac (x y z : ℝ) : (jac x y z).det = detJ x y z := by
  simp [jac, detJ, Matrix.det_fin_three]; ring

/-! ### Reduction to one variable -/

theorem D_neg {z : ℝ} (h0 : 0 < z) (h4 : z < 4) : D z < 0 := by unfold D; nlinarith
theorem N_pos {z : ℝ} (h0 : 0 < z) : 0 < N z := by unfold N; positivity

theorem curve (z : ℝ) (hD : D z ≠ 0) :
    f2 (X z) (Y z) z = 0 ∧ f3 (X z) (Y z) z = 0 ∧ f1 (X z) (Y z) z = -E z / (1250 * D z ^ 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [f1, f2, f3, X, Y, N, E] <;> field_simp <;> unfold D <;> ring

theorem on_curve {x y z : ℝ} (hy : 0 < y) (hz : 0 < z) (e1 : f1 x y z = 0) (e2 : f2 x y z = 0)
    (e3 : f3 x y z = 0) : D z < 0 ∧ x = X z ∧ y = Y z ∧ E z = 0 := by
  simp only [f2, f3] at e2 e3
  have hx : 50 * x = z * (5 + 4 * y) := by linear_combination 10 * e3
  have lin : y * D z + N z = 0 := by
    unfold D N; linear_combination 100000 * e2 - 2000 * (1 + z) * hx
  have hDn : D z < 0 := by nlinarith [N_pos hz, mul_pos hy (N_pos hz)]
  have hD : D z ≠ 0 := hDn.ne
  have hY : y = Y z := by rw [Y, eq_div_iff hD]; linarith
  have hX : x = X z := by rw [X, ← hY]; linarith
  refine ⟨hDn, hX, hY, ?_⟩
  have := (curve z hD).2.2
  rw [← hX, ← hY, e1] at this
  have h2 : (1250 * D z ^ 2) ≠ 0 := by positivity
  have := (div_eq_zero_iff.mp this.symm).resolve_right h2
  linarith

theorem Y_pos {z : ℝ} (h0 : 0 < z) (h4 : z < 4) : 0 < Y z := by
  unfold Y; exact div_pos_of_neg_of_neg (by linarith [N_pos h0]) (D_neg h0 h4)
theorem X_pos {z : ℝ} (h0 : 0 < z) (h4 : z < 4) : 0 < X z := by
  unfold X; have := Y_pos h0 h4; positivity

/-! ### Five roots with determinant signs -,+,-,+,- -/

theorem E_cont : Continuous E := by unfold E; fun_prop

theorem root_up {a b : ℝ} (hab : a ≤ b) (ha : E a < 0) (hb : 0 < E b) : ∃ r ∈ Ioo a b, E r = 0 :=
  intermediate_value_Ioo hab E_cont.continuousOn ⟨ha, hb⟩
theorem root_dn {a b : ℝ} (hab : a ≤ b) (ha : 0 < E a) (hb : E b < 0) : ∃ r ∈ Ioo a b, E r = 0 :=
  intermediate_value_Ioo' hab E_cont.continuousOn ⟨hb, ha⟩

/-- Crude monotone bounds lo^k ≤ z^k ≤ hi^k fix the sign of E' on each (tiny) root interval. -/
theorem pw {lo hi z : ℝ} (h0 : 0 ≤ lo) (h1 : lo ≤ z) (h2 : z ≤ hi) (n : ℕ) : lo ^ n ≤ z ^ n ∧ z ^ n ≤ hi ^ n :=
  ⟨pow_le_pow_left₀ h0 h1 n, pow_le_pow_left₀ (h0.trans h1) h2 n⟩

theorem dE_sign_pos {lo hi z : ℝ} (h0 : 0 ≤ lo) (h1 : lo ≤ z) (h2 : z ≤ hi)
    (h : 0 < 200000000000 * lo ^ 4 - 440124000000 * hi ^ 3 + 151248750000 * lo ^ 2 - 1565476250 * hi + 101000) :
    0 < dE z := by
  obtain ⟨a2, -⟩ := pw h0 h1 h2 2; obtain ⟨-, b3⟩ := pw h0 h1 h2 3; obtain ⟨a4, -⟩ := pw h0 h1 h2 4
  unfold dE; nlinarith

theorem dE_sign_neg {lo hi z : ℝ} (h0 : 0 ≤ lo) (h1 : lo ≤ z) (h2 : z ≤ hi)
    (h : 200000000000 * hi ^ 4 - 440124000000 * lo ^ 3 + 151248750000 * hi ^ 2 - 1565476250 * lo + 101000 < 0) :
    dE z < 0 := by
  obtain ⟨-, b2⟩ := pw h0 h1 h2 2; obtain ⟨a3, -⟩ := pw h0 h1 h2 3; obtain ⟨-, b4⟩ := pw h0 h1 h2 4
  unfold dE; nlinarith

theorem M_pos {z : ℝ} (h0 : 0 < z) (h4 : z < 4) : 0 < M z := by unfold M; nlinarith

theorem detJ_curve (z : ℝ) (hD : D z ≠ 0) :
    detJ (X z) (Y z) z = -M z * dE z / (1250 * D z ^ 2) - 4 * (z - 2) / (3125 * D z ^ 2) * E z := by
  simp only [detJ, X, Y, N, M, dE, E]; field_simp; unfold D; ring

theorem detJ_root {z : ℝ} (hD : D z ≠ 0) (hE : E z = 0) :
    detJ (X z) (Y z) z = -M z * dE z / (1250 * D z ^ 2) := by
  rw [detJ_curve z hD, hE, mul_zero, sub_zero]

/-! ### Exactly five -/

def EE : ℝ[X] :=
  C 40000000000 * Polynomial.X ^ 5 - C 110031000000 * Polynomial.X ^ 4 + C 50416250000 * Polynomial.X ^ 3 -
    C 782738125 * Polynomial.X ^ 2 + C 101000 * Polynomial.X - C 1

theorem eval_EE (z : ℝ) : EE.eval z = E z := by simp [EE, E]
theorem EE_ne : EE ≠ 0 := fun h => by simpa [eval_EE, E] using congrArg (eval 0) h
theorem EE_deg : EE.natDegree ≤ 5 := by unfold EE; compute_degree

/-- The positive steady states of the network. -/
def S : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ f1 p.1 p.2.1 p.2.2 = 0 ∧ f2 p.1 p.2.1 p.2.2 = 0 ∧ f3 p.1 p.2.1 p.2.2 = 0}

def g (z : ℝ) : ℝ × ℝ × ℝ := (X z, Y z, z)

theorem detJ_neg {z : ℝ} (h0 : 0 < z) (h4 : z < 4) (hE : E z = 0) (hd : 0 < dE z) : detJ (X z) (Y z) z < 0 := by
  rw [detJ_root (D_neg h0 h4).ne hE]
  have : 0 < 1250 * D z ^ 2 := by have := (D_neg h0 h4).ne; positivity
  exact div_neg_of_neg_of_pos (by nlinarith [M_pos h0 h4]) this
theorem detJ_pos {z : ℝ} (h0 : 0 < z) (h4 : z < 4) (hE : E z = 0) (hd : dE z < 0) : 0 < detJ (X z) (Y z) z := by
  rw [detJ_root (D_neg h0 h4).ne hE]
  have : 0 < 1250 * D z ^ 2 := by have := (D_neg h0 h4).ne; positivity
  exact div_pos (by nlinarith [M_pos h0 h4]) this

theorem main : ∃ r₁ r₂ r₃ r₄ r₅ : ℝ,
    r₁ ∈ Ioo (1 / 92549) (1 / 92548) ∧ r₂ ∈ Ioo (5 / 41934) (4 / 33547) ∧ r₃ ∈ Ioo (1107 / 69395) (1091 / 68392) ∧
    r₄ ∈ Ioo (18817 / 33654) (18122 / 32411) ∧ r₅ ∈ Ioo (236675 / 108788) (256527 / 117913) ∧
    S = {g r₁, g r₂, g r₃, g r₄, g r₅} ∧ S.ncard = 5 ∧
    detJ (X r₁) (Y r₁) r₁ < 0 ∧ 0 < detJ (X r₂) (Y r₂) r₂ ∧ detJ (X r₃) (Y r₃) r₃ < 0 ∧
    0 < detJ (X r₄) (Y r₄) r₄ ∧ detJ (X r₅) (Y r₅) r₅ < 0 := by
  obtain ⟨r₁, ⟨a1, b1⟩, p1⟩ := root_up (a := 1 / 92549) (b := 1 / 92548) (by norm_num) (by norm_num [E]) (by norm_num [E])
  obtain ⟨r₂, ⟨a2, b2⟩, p2⟩ := root_dn (a := 5 / 41934) (b := 4 / 33547) (by norm_num) (by norm_num [E]) (by norm_num [E])
  obtain ⟨r₃, ⟨a3, b3⟩, p3⟩ := root_up (a := 1107 / 69395) (b := 1091 / 68392) (by norm_num) (by norm_num [E]) (by norm_num [E])
  obtain ⟨r₄, ⟨a4, b4⟩, p4⟩ := root_dn (a := 18817 / 33654) (b := 18122 / 32411) (by norm_num) (by norm_num [E]) (by norm_num [E])
  obtain ⟨r₅, ⟨a5, b5⟩, p5⟩ := root_up (a := 236675 / 108788) (b := 256527 / 117913) (by norm_num) (by norm_num [E]) (by norm_num [E])
  have z1 : 0 < r₁ := by linarith
  have z2 : 0 < r₂ := by linarith
  have z3 : 0 < r₃ := by linarith
  have z4 : 0 < r₄ := by linarith
  have z5 : 0 < r₅ := by linarith
  have w1 : r₁ < 4 := by linarith
  have w2 : r₂ < 4 := by linarith
  have w3 : r₃ < 4 := by linarith
  have w4 : r₄ < 4 := by linarith
  have w5 : r₅ < 4 := by linarith
  have only : ∀ z, E z = 0 → z = r₁ ∨ z = r₂ ∨ z = r₃ ∨ z = r₄ ∨ z = r₅ := by
    intro z hz
    by_contra hne
    push Not at hne
    obtain ⟨n1, n2, n3, n4, n5⟩ := hne
    have hsub : ({z, r₁, r₂, r₃, r₄, r₅} : Finset ℝ).val ⊆ EE.roots := by
      intro w hw
      have hw' : w ∈ ({z, r₁, r₂, r₃, r₄, r₅} : Finset ℝ) := hw
      rw [mem_roots EE_ne, IsRoot, eval_EE]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
      rcases hw' with h | h | h | h | h | h <;> rw [h] <;> assumption
    have hcard := card_le_degree_of_subset_roots hsub
    rw [Finset.card_insert_of_notMem (by simp [n1, n2, n3, n4, n5]),
      Finset.card_insert_of_notMem (by simp; refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> linarith),
      Finset.card_insert_of_notMem (by simp; refine ⟨?_, ?_, ?_⟩ <;> intro h <;> linarith),
      Finset.card_insert_of_notMem (by simp; refine ⟨?_, ?_⟩ <;> intro h <;> linarith),
      Finset.card_insert_of_notMem (by simp; intro h; linarith), Finset.card_singleton] at hcard
    linarith [EE_deg]
  have mem : ∀ z, 0 < z → z < 4 → E z = 0 → g z ∈ S := by
    intro z h0 h4 hE
    obtain ⟨c2, c3, c1⟩ := curve z (D_neg h0 h4).ne
    simp only [S, g, Set.mem_ofPred_eq]
    refine ⟨X_pos h0 h4, Y_pos h0 h4, h0, ?_, c2, c3⟩
    rw [c1, hE, neg_zero, zero_div]
  have hS : S = {g r₁, g r₂, g r₃, g r₄, g r₅} := by
    ext ⟨x, y, z⟩
    constructor
    · rintro ⟨-, hy, hz, e1, e2, e3⟩
      simp only at hy hz e1 e2 e3
      obtain ⟨-, hxX, hyY, hE⟩ := on_curve hy hz e1 e2 e3
      rw [hxX, hyY]
      rcases only z hE with h | h | h | h | h <;> rw [h] <;> simp [g]
    · intro h
      simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with h | h | h | h | h <;> rw [h]
      exacts [mem r₁ z1 w1 p1, mem r₂ z2 w2 p2, mem r₃ z3 w3 p3, mem r₄ z4 w4 p4, mem r₅ z5 w5 p5]
  have hinj : Function.Injective g := fun a b h => by simpa [g] using congrArg (fun p => p.2.2) h
  have hcard : S.ncard = 5 := by
    rw [hS, show ({g r₁, g r₂, g r₃, g r₄, g r₅} : Set (ℝ × ℝ × ℝ)) =
        g '' (({r₁, r₂, r₃, r₄, r₅} : Finset ℝ) : Set ℝ) by simp [image_insert_eq],
      ncard_image_of_injective _ hinj, ncard_coe_finset,
      Finset.card_insert_of_notMem (by simp; refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> linarith),
      Finset.card_insert_of_notMem (by simp; refine ⟨?_, ?_, ?_⟩ <;> intro h <;> linarith),
      Finset.card_insert_of_notMem (by simp; refine ⟨?_, ?_⟩ <;> intro h <;> linarith),
      Finset.card_insert_of_notMem (by simp; intro h; linarith), Finset.card_singleton]
  refine ⟨r₁, r₂, r₃, r₄, r₅, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, hS, hcard, ?_, ?_, ?_, ?_, ?_⟩
  · exact detJ_neg z1 w1 p1 (dE_sign_pos (by norm_num) a1.le b1.le (by norm_num))
  · exact detJ_pos z2 w2 p2 (dE_sign_neg (by norm_num) a2.le b2.le (by norm_num))
  · exact detJ_neg z3 w3 p3 (dE_sign_pos (by norm_num) a3.le b3.le (by norm_num))
  · exact detJ_pos z4 w4 p4 (dE_sign_neg (by norm_num) a4.le b4.le (by norm_num))
  · exact detJ_neg z5 w5 p5 (dE_sign_pos (by norm_num) a5.le b5.le (by norm_num))

end

end ZeroOneFive
