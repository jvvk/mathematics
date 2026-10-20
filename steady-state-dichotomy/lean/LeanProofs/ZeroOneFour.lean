/-
A seven-reaction quadratic zero-one network with exactly four positive, nondegenerate steady states
(chem-tang-zhang-three-steady-states; witness and proof route from FOUR_STATES.md, Codex, 2026-10-16).

Reactions and rates: X1+X2 → 0 (7), X1+X3 → X2+X3 (1), X3 → X1 (1), X1+X2 → X3 (1),
X2+X3 → X1+X2+X3 (1), 0 → X2 (1), X1 → X1+X3 (3). Mass action with concentrations (x, y, z) gives f below.

Route (the paper's): f2 + 8 f3 = x(z+24) - (8z-1) puts every positive zero on the curve
x = (8z-1)/(z+24), y = (z^2+3)/(8z-1), z > 1/8, where f1 = P(z)/((z+24)(8z-1)) with
P = z^4 - 96 z^3 + 218 z^2 - 145 z + 24. Four sign changes of P give four roots; a quartic has at most four.
On the curve det J = P'(z)/(z+24) at every root of P, and P' has a fixed sign on each root interval.
-/
import Mathlib

namespace ZeroOneFour

open Polynomial Set

noncomputable section

def f1 (x y z : ℝ) : ℝ := -8 * x * y - x * z + z + y * z
def f2 (x y z : ℝ) : ℝ := -8 * x * y + x * z + 1
def f3 (x y z : ℝ) : ℝ := x * y - z + 3 * x

/-- The mass-action right-hand side of the network, read off reaction by reaction. -/
theorem f_from_network (x y z : ℝ) :
    f1 x y z = -7 * x * y - 1 * x * z + 1 * z + 1 * y * z - 1 * x * y ∧
    f2 x y z = -7 * x * y + 1 * x * z - 1 * x * y + 1 ∧
    f3 x y z = 1 * x * y - 1 * z + 3 * x := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [f1, f2, f3] <;> ring

def P (z : ℝ) : ℝ := z ^ 4 - 96 * z ^ 3 + 218 * z ^ 2 - 145 * z + 24
def dP (z : ℝ) : ℝ := 4 * z ^ 3 - 288 * z ^ 2 + 436 * z - 145
def X (z : ℝ) : ℝ := (8 * z - 1) / (z + 24)
def Y (z : ℝ) : ℝ := (z ^ 2 + 3) / (8 * z - 1)

/-! ### The Jacobian -/

/-- Every component is affine in each single variable, so each partial derivative is a slope. -/
theorem hasDerivAt_affine (a b x : ℝ) (g : ℝ → ℝ) (hg : ∀ t, g t = a * t + b) : HasDerivAt g a x := by
  have h := ((hasDerivAt_id x).const_mul a).add_const b
  simp only [id, mul_one] at h
  rwa [show g = fun t => a * t + b from funext hg]

def jac (x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-8 * y - z, -8 * x + z, -x + 1 + y;
     -8 * y + z, -8 * x, x;
     y + 3, x, -1]

/-- The entries of `jac` are the nine partial derivatives of f. -/
theorem jac_partials (x y z : ℝ) :
    HasDerivAt (fun t => f1 t y z) (jac x y z 0 0) x ∧ HasDerivAt (fun t => f1 x t z) (jac x y z 0 1) y ∧
    HasDerivAt (fun t => f1 x y t) (jac x y z 0 2) z ∧ HasDerivAt (fun t => f2 t y z) (jac x y z 1 0) x ∧
    HasDerivAt (fun t => f2 x t z) (jac x y z 1 1) y ∧ HasDerivAt (fun t => f2 x y t) (jac x y z 1 2) z ∧
    HasDerivAt (fun t => f3 t y z) (jac x y z 2 0) x ∧ HasDerivAt (fun t => f3 x t z) (jac x y z 2 1) y ∧
    HasDerivAt (fun t => f3 x y t) (jac x y z 2 2) z := by
  refine ⟨hasDerivAt_affine _ (z + y * z) _ _ ?_, hasDerivAt_affine _ (-x * z + z) _ _ ?_,
    hasDerivAt_affine _ (-8 * x * y) _ _ ?_, hasDerivAt_affine _ 1 _ _ ?_, hasDerivAt_affine _ (x * z + 1) _ _ ?_,
    hasDerivAt_affine _ (-8 * x * y + 1) _ _ ?_, hasDerivAt_affine _ (-z) _ _ ?_,
    hasDerivAt_affine _ (-z + 3 * x) _ _ ?_, hasDerivAt_affine _ (x * y + 3 * x) _ _ ?_⟩ <;>
    intro t <;> simp [jac, f1, f2, f3] <;> ring

def detJ (x y z : ℝ) : ℝ := -48 * x ^ 2 + 2 * x * y * z + 24 * x * y - 12 * x * z + 24 * x - 8 * y * z + z ^ 2

theorem det_jac (x y z : ℝ) : (jac x y z).det = detJ x y z := by
  simp [jac, detJ, Matrix.det_fin_three]; ring

/-! ### Reduction to one variable -/

theorem curve (z : ℝ) (hz : 1 / 8 < z) :
    f2 (X z) (Y z) z = 0 ∧ f3 (X z) (Y z) z = 0 ∧
      f1 (X z) (Y z) z = P z / ((z + 24) * (8 * z - 1)) := by
  have h1 : z + 24 ≠ 0 := by linarith
  have h2 : 8 * z - 1 ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_⟩ <;> simp only [f1, f2, f3, X, Y, P] <;> field_simp <;> ring

theorem on_curve {x y z : ℝ} (hx : 0 < x) (hz : 0 < z) (e1 : f1 x y z = 0) (e2 : f2 x y z = 0)
    (e3 : f3 x y z = 0) : 1 / 8 < z ∧ x = X z ∧ y = Y z ∧ P z = 0 := by
  simp only [f2, f3] at e2 e3
  have key : x * (z + 24) = 8 * z - 1 := by linear_combination e2 + 8 * e3
  have hz8 : 1 / 8 < z := by nlinarith [mul_pos hx (by linarith : (0 : ℝ) < z + 24)]
  have h1 : z + 24 ≠ 0 := by linarith
  have h2 : 8 * z - 1 ≠ 0 := by linarith
  have hX : x = X z := by rw [X, eq_div_iff h1]; exact key
  have hY : y = Y z := by
    rw [Y, eq_div_iff h2]; linear_combination (z + 24) * e3 + (-3 - y) * key
  refine ⟨hz8, hX, hY, ?_⟩
  have := (curve z hz8).2.2
  rw [← hX, ← hY, e1] at this
  rcases (div_eq_zero_iff.mp this.symm) with h | h
  · exact h
  · exact absurd h (mul_ne_zero h1 h2)

theorem X_pos {z : ℝ} (hz : 1 / 8 < z) : 0 < X z := by unfold X; apply div_pos <;> linarith
theorem Y_pos {z : ℝ} (hz : 1 / 8 < z) : 0 < Y z := by unfold Y; apply div_pos <;> nlinarith

/-! ### Four roots, each simple, with determinant signs -,+,-,+ -/

theorem P_cont : Continuous P := by unfold P; fun_prop

theorem root_dn {a b : ℝ} (hab : a ≤ b) (ha : 0 < P a) (hb : P b < 0) : ∃ r ∈ Ioo a b, P r = 0 :=
  intermediate_value_Ioo' hab P_cont.continuousOn ⟨hb, ha⟩

theorem root_up {a b : ℝ} (hab : a ≤ b) (ha : P a < 0) (hb : 0 < P b) : ∃ r ∈ Ioo a b, P r = 0 :=
  intermediate_value_Ioo hab P_cont.continuousOn ⟨ha, hb⟩

theorem dP1 {z : ℝ} (h : 6 / 25 < z) (h' : z < 13 / 50) : dP z < 0 := by
  unfold dP; nlinarith [mul_pos (by linarith : (0 : ℝ) < z) (by linarith : (0 : ℝ) < z), sq_nonneg z,
    mul_pos (mul_pos (by linarith : (0 : ℝ) < z) (by linarith : (0 : ℝ) < z)) (by linarith : (0 : ℝ) < 13 / 50 - z)]
theorem dP2 {z : ℝ} (h : 17 / 20 < z) (h' : z < 87 / 100) : 0 < dP z := by
  unfold dP; nlinarith [mul_pos (by linarith : (0 : ℝ) < z) (by linarith : (0 : ℝ) < z),
    mul_pos (mul_pos (by linarith : (0 : ℝ) < z) (by linarith : (0 : ℝ) < z)) (by linarith : (0 : ℝ) < z)]
theorem dP3 {z : ℝ} (h : 6 / 5 < z) (h' : z < 121 / 100) : dP z < 0 := by
  unfold dP; nlinarith [mul_pos (by linarith : (0 : ℝ) < z) (by linarith : (0 : ℝ) < z),
    mul_pos (mul_pos (by linarith : (0 : ℝ) < z) (by linarith : (0 : ℝ) < z)) (by linarith : (0 : ℝ) < 121 / 100 - z)]
theorem dP4 {z : ℝ} (h : 93 < z) (h' : z < 94) : 0 < dP z := by
  unfold dP; nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < z) (by linarith : (0 : ℝ) < z)) (by linarith : (0 : ℝ) < z - 72)]

theorem detJ_curve (z : ℝ) (hz : 1 / 8 < z) :
    detJ (X z) (Y z) z = dP z / (z + 24) - (16 * z + 191) / ((z + 24) ^ 2 * (8 * z - 1)) * P z := by
  have h1 : z + 24 ≠ 0 := by linarith
  have h2 : 8 * z - 1 ≠ 0 := by linarith
  simp only [detJ, X, Y, P, dP]; field_simp; ring

theorem detJ_root {z : ℝ} (hz : 1 / 8 < z) (hP : P z = 0) : detJ (X z) (Y z) z = dP z / (z + 24) := by
  rw [detJ_curve z hz, hP, mul_zero, sub_zero]

/-! ### Exactly four -/

def PP : ℝ[X] := Polynomial.X ^ 4 - C 96 * Polynomial.X ^ 3 + C 218 * Polynomial.X ^ 2 - C 145 * Polynomial.X + C 24

theorem eval_PP (z : ℝ) : PP.eval z = P z := by simp [PP, P]

theorem PP_ne : PP ≠ 0 := fun h => by simpa [eval_PP, P] using congrArg (eval 0) h

theorem PP_deg : PP.natDegree ≤ 4 := by unfold PP; compute_degree

/-- The positive steady states of the network. -/
def S : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ f1 p.1 p.2.1 p.2.2 = 0 ∧ f2 p.1 p.2.1 p.2.2 = 0 ∧ f3 p.1 p.2.1 p.2.2 = 0}

def g (z : ℝ) : ℝ × ℝ × ℝ := (X z, Y z, z)

theorem main : ∃ r₁ r₂ r₃ r₄ : ℝ,
    r₁ ∈ Ioo (6 / 25) (13 / 50) ∧ r₂ ∈ Ioo (17 / 20) (87 / 100) ∧ r₃ ∈ Ioo (6 / 5) (121 / 100) ∧ r₄ ∈ Ioo 93 94 ∧
    S = {g r₁, g r₂, g r₃, g r₄} ∧ S.ncard = 4 ∧
    detJ (X r₁) (Y r₁) r₁ < 0 ∧ 0 < detJ (X r₂) (Y r₂) r₂ ∧
    detJ (X r₃) (Y r₃) r₃ < 0 ∧ 0 < detJ (X r₄) (Y r₄) r₄ := by
  obtain ⟨r₁, ⟨a1, b1⟩, p1⟩ := root_dn (a := 6 / 25) (b := 13 / 50) (by norm_num) (by norm_num [P]) (by norm_num [P])
  obtain ⟨r₂, ⟨a2, b2⟩, p2⟩ := root_up (a := 17 / 20) (b := 87 / 100) (by norm_num) (by norm_num [P]) (by norm_num [P])
  obtain ⟨r₃, ⟨a3, b3⟩, p3⟩ := root_dn (a := 6 / 5) (b := 121 / 100) (by norm_num) (by norm_num [P]) (by norm_num [P])
  obtain ⟨r₄, ⟨a4, b4⟩, p4⟩ := root_up (a := 93) (b := 94) (by norm_num) (by norm_num [P]) (by norm_num [P])
  have q1 : (1 : ℝ) / 8 < r₁ := by linarith
  have q2 : (1 : ℝ) / 8 < r₂ := by linarith
  have q3 : (1 : ℝ) / 8 < r₃ := by linarith
  have q4 : (1 : ℝ) / 8 < r₄ := by linarith
  -- every root of P beyond 1/8 is one of the four
  have only : ∀ z, 1 / 8 < z → P z = 0 → z = r₁ ∨ z = r₂ ∨ z = r₃ ∨ z = r₄ := by
    intro z _ hz
    by_contra hne
    push Not at hne
    obtain ⟨n1, n2, n3, n4⟩ := hne
    have hsub : ({z, r₁, r₂, r₃, r₄} : Finset ℝ).val ⊆ PP.roots := by
      intro w hw
      have hw' : w ∈ ({z, r₁, r₂, r₃, r₄} : Finset ℝ) := hw
      rw [mem_roots PP_ne, IsRoot, eval_PP]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
      rcases hw' with h | h | h | h | h <;> rw [h] <;> assumption
    have hcard := card_le_degree_of_subset_roots hsub
    rw [Finset.card_insert_of_notMem (by simp [n1, n2, n3, n4]),
      Finset.card_insert_of_notMem (by simp; refine ⟨?_, ?_, ?_⟩ <;> intro h <;> linarith),
      Finset.card_insert_of_notMem (by simp; refine ⟨?_, ?_⟩ <;> intro h <;> linarith),
      Finset.card_insert_of_notMem (by simp; intro h; linarith), Finset.card_singleton] at hcard
    linarith [PP_deg]
  have mem : ∀ z, 1 / 8 < z → P z = 0 → g z ∈ S := by
    intro z hz hP
    obtain ⟨c2, c3, c1⟩ := curve z hz
    simp only [S, g, Set.mem_ofPred_eq]
    refine ⟨X_pos hz, Y_pos hz, by linarith, ?_, c2, c3⟩
    rw [c1, hP, zero_div]
  have hS : S = {g r₁, g r₂, g r₃, g r₄} := by
    ext ⟨x, y, z⟩
    constructor
    · rintro ⟨hx, -, hz, e1, e2, e3⟩
      simp only at hx hz e1 e2 e3
      obtain ⟨h8, hxX, hyY, hP⟩ := on_curve hx hz e1 e2 e3
      rw [hxX, hyY]
      rcases only z h8 hP with h | h | h | h <;> rw [h] <;> simp [g]
    · intro h
      simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with h | h | h | h <;> rw [h]
      exacts [mem r₁ q1 p1, mem r₂ q2 p2, mem r₃ q3 p3, mem r₄ q4 p4]
  have hinj : Function.Injective g := fun a b h => by simpa [g] using congrArg (fun p => p.2.2) h
  have hcard : S.ncard = 4 := by
    rw [hS, show ({g r₁, g r₂, g r₃, g r₄} : Set (ℝ × ℝ × ℝ)) = g '' (({r₁, r₂, r₃, r₄} : Finset ℝ) : Set ℝ) by
      simp [image_insert_eq], ncard_image_of_injective _ hinj, ncard_coe_finset,
      Finset.card_insert_of_notMem (by simp; refine ⟨?_, ?_, ?_⟩ <;> intro h <;> linarith),
      Finset.card_insert_of_notMem (by simp; refine ⟨?_, ?_⟩ <;> intro h <;> linarith),
      Finset.card_insert_of_notMem (by simp; intro h; linarith), Finset.card_singleton]
  refine ⟨r₁, r₂, r₃, r₄, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, hS, hcard, ?_, ?_, ?_, ?_⟩
  · rw [detJ_root q1 p1]; exact div_neg_of_neg_of_pos (dP1 a1 b1) (by linarith)
  · rw [detJ_root q2 p2]; exact div_pos (dP2 a2 b2) (by linarith)
  · rw [detJ_root q3 p3]; exact div_neg_of_neg_of_pos (dP3 a3 b3) (by linarith)
  · rw [detJ_root q4 p4]; exact div_pos (dP4 a4 b4) (by linarith)

end

end ZeroOneFour
