import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Randomized Pascal triangle (MO 479618): the model

Each interior entry is the sum of its two parents with probability `p` (heads) and the absolute
difference with probability `1 - p` (tails), independently. Row `n` is stored as `x : ℕ → ℝ`
supported on positions `3, …, n + 3` (three zeros on the left keep every index natural). With zero
padding the edges are automatically `1`: both rules give `1` from the parents `(0, 1)`.

Step `n` uses `K n = n + 8` independent coins, one per position `j < K n`; the new entry at `j` is
`cell (c j) (x (j - 1)) (x j)`. Positions whose parents are both zero get `0` whichever coin falls,
so the extra coins do not change the law of the next row.

Expectation is defined by the Markov property: `Exp p n g` is the expectation of `g (row n)`, with
`Exp p 0 g = g x0` and `Exp p (n+1) g = Exp p n (P p n g)`, where `P p n g x` averages `g` over the
`2 ^ K n` coin vectors with their product weights.
-/

open Finset

namespace RandPascal

/-- One cell: heads (`true`) writes the sum, tails the absolute difference. -/
def cell (b : Bool) (u v : ℝ) : ℝ := if b then u + v else |u - v|

/-- Probability of a single coin outcome. -/
def w (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Product weight of a coin vector. -/
def wt (p : ℝ) {K : ℕ} (c : Fin K → Bool) : ℝ := ∏ i, w p (c i)

/-- Number of coins used at step `n`. -/
def K (n : ℕ) : ℕ := n + 8

/-- The next row from row `x` (at level `n`) and coins `c`. -/
def step (n : ℕ) (x : ℕ → ℝ) (c : Fin (K n) → Bool) : ℕ → ℝ := fun j =>
  if h : j < K n then cell (c ⟨j, h⟩) (x (j - 1)) (x j) else 0

/-- Row 0: a single `1` at position 3. -/
def x0 : ℕ → ℝ := fun j => if j = 3 then 1 else 0

/-- A row at level `n`: nonnegative, supported on positions `3, …, n + 3`. -/
def Valid (n : ℕ) (x : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ (∀ j, j < 3 → x j = 0) ∧ (∀ j, n + 3 < j → x j = 0)

/-- One-step expectation of `g` from row `x` at level `n`. -/
def P (p : ℝ) (n : ℕ) (g : (ℕ → ℝ) → ℝ) (x : ℕ → ℝ) : ℝ :=
  ∑ c : Fin (K n) → Bool, wt p c * g (step n x c)

/-- `Exp p n g` is the expectation of `g` evaluated at row `n`. -/
def Exp (p : ℝ) : ℕ → ((ℕ → ℝ) → ℝ) → ℝ
  | 0, g => g x0
  | n + 1, g => Exp p n (P p n g)

/-! ## Basic facts -/

lemma cell_nonneg (b : Bool) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ cell b u v := by
  cases b <;> simp [cell] <;> positivity

lemma cell_zero (b : Bool) : cell b 0 0 = 0 := by cases b <;> simp [cell]

lemma w_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) : 0 ≤ w p b := by
  cases b <;> simp [w] <;> linarith

lemma w_add (p : ℝ) : w p true + w p false = 1 := by simp [w]

lemma wt_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {K : ℕ} (c : Fin K → Bool) : 0 ≤ wt p c :=
  prod_nonneg fun i _ => w_nonneg hp0 hp1 (c i)

lemma valid_x0 : Valid 0 x0 := by
  refine ⟨fun j => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · unfold x0; split_ifs <;> norm_num
  · unfold x0; rw [if_neg (by omega)]
  · unfold x0; rw [if_neg (by omega)]

lemma valid_step {n : ℕ} {x : ℕ → ℝ} (hx : Valid n x) (c : Fin (K n) → Bool) :
    Valid (n + 1) (step n x c) := by
  obtain ⟨h0, hlo, hhi⟩ := hx
  refine ⟨fun j => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · unfold step; split_ifs
    · exact cell_nonneg _ (h0 _) (h0 _)
    · exact le_rfl
  · unfold step; split_ifs
    · rw [hlo _ (by omega), hlo _ hj, cell_zero]
    · rfl
  · unfold step; split_ifs
    · rw [hhi _ (by omega), hhi _ (by omega), cell_zero]
    · rfl

/-! ## Monotonicity and linearity of the expectation -/

lemma P_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {n : ℕ} {g h : (ℕ → ℝ) → ℝ}
    (hgh : ∀ y, Valid (n + 1) y → g y ≤ h y) {x : ℕ → ℝ} (hx : Valid n x) :
    P p n g x ≤ P p n h x :=
  sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hgh _ (valid_step hx c)) (wt_nonneg hp0 hp1 c)

lemma Exp_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ (n : ℕ) {g h : (ℕ → ℝ) → ℝ}, (∀ y, Valid n y → g y ≤ h y) → Exp p n g ≤ Exp p n h
  | 0, _, _, hgh => hgh _ valid_x0
  | n + 1, _, _, hgh => Exp_mono hp0 hp1 n fun _ hy => P_mono hp0 hp1 hgh hy

lemma P_smul (p r : ℝ) (n : ℕ) (g : (ℕ → ℝ) → ℝ) :
    P p n (fun y => r * g y) = fun x => r * P p n g x := by
  funext x; unfold P; rw [mul_sum]; exact sum_congr rfl fun c _ => by ring

lemma Exp_smul (p r : ℝ) : ∀ (n : ℕ) (g : (ℕ → ℝ) → ℝ), Exp p n (fun y => r * g y) = r * Exp p n g
  | 0, _ => rfl
  | n + 1, g => by simp only [Exp]; rw [P_smul]; exact Exp_smul p r n _

/-- The basic iteration: a potential that grows by `λ` in one step grows like `λ ^ n`. -/
lemma Exp_growth {p lam : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hl : 0 ≤ lam) (F : ℕ → (ℕ → ℝ) → ℝ)
    (hdrift : ∀ n x, Valid n x → lam * F n x ≤ P p n (F (n + 1)) x) :
    ∀ n, lam ^ n * F 0 x0 ≤ Exp p n (F n)
  | 0 => by simp [Exp]
  | n + 1 => by
    have ih := Exp_growth hp0 hp1 hl F hdrift n
    have hm := Exp_mono hp0 hp1 n (g := fun y => lam * F n y) (h := P p n (F (n + 1)))
      fun y hy => hdrift n y hy
    rw [Exp_smul] at hm
    calc lam ^ (n + 1) * F 0 x0 = lam * (lam ^ n * F 0 x0) := by ring
      _ ≤ lam * Exp p n (F n) := mul_le_mul_of_nonneg_left ih hl
      _ ≤ Exp p (n + 1) (F (n + 1)) := hm

end RandPascal
