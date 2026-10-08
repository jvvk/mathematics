import LeanProofs.RandPascal.Sums
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Randomized Pascal triangle, Theorem A

For `0 < p ≤ 1` let `λ = p² + √(p⁴ + 4p(1-p))`. Then the expected sum of row `n` is at least `λⁿ`.
Since `λ > 1` exactly when `2p² - 4p + 1 < 0`, i.e. `p > 1 - 1/√2`, the expected row sums grow
exponentially above that value.

Proof: with `S` the row sum and `V` the total variation `∑ |x_{j+1} - x_j|`,
  (1) `E[S'] = 2p S + (1-p) V`,
  (2) `E[V'] ≥ 4p(1-p) S - 2p(1-p) V`  (only the two mixed coin outcomes are kept),
so `F = S + t V` with `t = (1-p)/(λ + 2p(1-p))` satisfies `E[F'] ≥ λ F`; and `S ≤ F ≤ (1+2t) S`.
-/

open Finset

namespace RandPascal

/-- Row sum over the box `j < M`. -/
def S (M : ℕ) (x : ℕ → ℝ) : ℝ := ∑ j ∈ range M, x j

/-- Total variation over the box `j < M`. -/
def V (M : ℕ) (x : ℕ → ℝ) : ℝ := ∑ j ∈ range M, |x (j + 1) - x j|

/-! ## Rewriting tools -/

lemma P_congr {p : ℝ} {n : ℕ} {g h : (ℕ → ℝ) → ℝ} (hgh : ∀ y, Valid (n + 1) y → g y = h y)
    {x : ℕ → ℝ} (hx : Valid n x) : P p n g x = P p n h x :=
  sum_congr rfl fun c _ => by rw [hgh _ (valid_step hx c)]

lemma P_add (p : ℝ) (n : ℕ) (g h : (ℕ → ℝ) → ℝ) (x : ℕ → ℝ) :
    P p n (fun y => g y + h y) x = P p n g x + P p n h x := by
  unfold P; rw [← sum_add_distrib]; exact sum_congr rfl fun c _ => by ring

/-- A valid row extended by one zero. -/
lemma sum_succ_zero {n : ℕ} {x : ℕ → ℝ} (hx : Valid n x) (f : ℕ → ℝ) (hf : f (n + 4) = 0) :
    ∑ j ∈ range (n + 5), f j = ∑ j ∈ range (n + 4), f j := by
  rw [show n + 5 = (n + 4) + 1 by ring, sum_range_succ, hf, add_zero]

/-- Sum of the shifted entries of a valid row. -/
lemma sum_x_shift {n : ℕ} {x : ℕ → ℝ} (hx : Valid n x) (k : ℕ) (hk : k ≤ 3) :
    ∑ j ∈ range (n + 5), x (j + k) = S (n + 4) x := by
  rw [sum_shift x (n + 5) k (fun j hj => hx.2.1 j (by omega)) (fun j hj => hx.2.2 j (by omega))]
  exact sum_succ_zero hx x (hx.2.2 _ (by omega))

lemma sum_V_shift {n : ℕ} {x : ℕ → ℝ} (hx : Valid n x) (k : ℕ) (hk : k ≤ 2) :
    ∑ j ∈ range (n + 5), |x (j + k + 1) - x (j + k)| = V (n + 4) x := by
  have := sum_shift (fun j => |x (j + 1) - x j|) (n + 5) k
    (fun j hj => by simp [hx.2.1 j (by omega), hx.2.1 (j + 1) (by omega)])
    (fun j hj => by simp [hx.2.2 j (by omega), hx.2.2 (j + 1) (by omega)])
  beta_reduce at this
  calc ∑ j ∈ range (n + 5), |x (j + k + 1) - x (j + k)|
      = ∑ j ∈ range (n + 5), |x (j + 1) - x j| := by
        rw [← this]
    _ = V (n + 4) x := sum_succ_zero hx _ (by simp [hx.2.2 (n + 4) (by omega),
          hx.2.2 (n + 5) (by omega)])

lemma sum_x_zero {n : ℕ} {x : ℕ → ℝ} (hx : Valid n x) :
    ∑ j ∈ range (n + 5), x j = S (n + 4) x := sum_succ_zero hx x (hx.2.2 _ (by omega))

lemma sum_V_zero {n : ℕ} {x : ℕ → ℝ} (hx : Valid n x) :
    ∑ j ∈ range (n + 5), |x j - x (j + 1)| = V (n + 4) x := by
  rw [← sum_V_shift hx 0 (by norm_num)]
  exact sum_congr rfl fun j _ => by rw [abs_sub_comm]; simp

lemma sum_V_one {n : ℕ} {x : ℕ → ℝ} (hx : Valid n x) :
    ∑ j ∈ range (n + 5), |x (j + 1) - x (j + 2)| = V (n + 4) x := by
  rw [← sum_V_shift hx 1 (by norm_num)]
  exact sum_congr rfl fun j _ => by rw [abs_sub_comm]

/-! ## The two expectation estimates -/

lemma E3_first (p a b c d : ℝ) :
    E3 p (fun A _ _ => A) a b c d = p * (a + b) + (1 - p) * |a - b| := by
  simp [E3, cell, w]; ring

lemma E3_jump (p a b c d : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (1 - p) * ((a + b - |a - b|) + (b + c - |b - c|)) ≤
      E3 p (fun A B _ => |B - A|) a b c d := by
  simp only [E3, Fintype.sum_bool, cell, w, if_true, Bool.false_eq_true, if_false]
  have hq : 0 ≤ 1 - p := by linarith
  -- the two mixed outcomes alone already give the bound
  have m1 : (b + c) - |a - b| ≤ abs (b + c - abs (a - b)) := le_abs_self _
  have m2 : (a + b) - |b - c| ≤ abs (abs (b - c) - (a + b)) :=
    (le_abs_self _).trans_eq (abs_sub_comm _ _)
  have n1 : 0 ≤ abs (b + c - (a + b)) := abs_nonneg _
  have n2 : 0 ≤ abs (abs (b - c) - abs (a - b)) := abs_nonneg _
  have hpq : 0 ≤ p * (1 - p) := mul_nonneg hp0 hq
  have hpp : 0 ≤ p * p := mul_nonneg hp0 hp0
  have hqq : 0 ≤ (1 - p) * (1 - p) := mul_nonneg hq hq
  nlinarith [mul_le_mul_of_nonneg_left m1 hpq, mul_le_mul_of_nonneg_left m2 hpq,
    mul_nonneg hpp n1, mul_nonneg hqq n2, mul_nonneg hpq n1, mul_nonneg hpq n2]

/-- (1): exact expectation of the next row sum. -/
lemma P_S {p : ℝ} {n : ℕ} {x : ℕ → ℝ} (hx : Valid n x) :
    P p n (S (n + 5)) x = 2 * p * S (n + 4) x + (1 - p) * V (n + 4) x := by
  rw [P_congr (h := fun y => ∑ j ∈ range (n + 5), (fun A (_ _ : ℝ) => A) (y (j + 1)) (y (j + 2))
      (y (j + 3))) (fun y hy => ?_) hx]
  · rw [P_window p n x (fun A _ _ => A)]
    simp only [E3_first, sum_add_distrib, ← mul_sum]
    rw [sum_x_zero hx, sum_x_shift hx 1 (by norm_num), sum_V_zero hx]
    ring
  · simp only [S]
    rw [sum_shift y (n + 5) 1 (fun j hj => hy.2.1 j (by omega)) (fun j hj => hy.2.2 j (by omega))]

/-- (2): lower bound for the expected next total variation. -/
lemma P_V {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {n : ℕ} {x : ℕ → ℝ} (hx : Valid n x) :
    4 * p * (1 - p) * S (n + 4) x - 2 * p * (1 - p) * V (n + 4) x ≤ P p n (V (n + 5)) x := by
  rw [P_congr (h := fun y => ∑ j ∈ range (n + 5), (fun A B (_ : ℝ) => |B - A|) (y (j + 1))
      (y (j + 2)) (y (j + 3))) (fun y hy => ?_) hx]
  · rw [P_window p n x (fun A B _ => |B - A|)]
    calc 4 * p * (1 - p) * S (n + 4) x - 2 * p * (1 - p) * V (n + 4) x
        = ∑ j ∈ range (n + 5), p * (1 - p) * ((x j + x (j + 1) - |x j - x (j + 1)|) +
            (x (j + 1) + x (j + 2) - |x (j + 1) - x (j + 2)|)) := by
          simp only [← mul_sum, sum_add_distrib, sum_sub_distrib]
          rw [sum_x_zero hx, sum_x_shift hx 1 (by norm_num), sum_x_shift hx 2 (by norm_num),
            sum_V_zero hx, sum_V_one hx]
          ring
      _ ≤ _ := sum_le_sum fun j _ => E3_jump p _ _ _ _ hp0 hp1
  · simp only [V]
    have := sum_shift (fun j => |y (j + 1) - y j|) (n + 5) 1
      (fun j hj => by simp [hy.2.1 j (by omega), hy.2.1 (j + 1) (by omega)])
      (fun j hj => by simp [hy.2.2 j (by omega), hy.2.2 (j + 1) (by omega)])
    rw [← this]

/-! ## Theorem A -/

/-- The growth factor of Theorem A. -/
noncomputable def lamA (p : ℝ) : ℝ := p ^ 2 + Real.sqrt (p ^ 4 + 4 * p * (1 - p))

lemma lamA_sq {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    lamA p ^ 2 = 2 * p ^ 2 * lamA p + 4 * p * (1 - p) := by
  have h : 0 ≤ p ^ 4 + 4 * p * (1 - p) := by
    have : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
    positivity
  unfold lamA
  nlinarith [Real.sq_sqrt h]

lemma lamA_nonneg (p : ℝ) : 0 ≤ lamA p := by unfold lamA; positivity

lemma V_le_two_S {n : ℕ} {x : ℕ → ℝ} (hx : Valid n x) : V (n + 4) x ≤ 2 * S (n + 4) x := by
  have h1 : ∑ j ∈ range (n + 4), x (j + 1) = S (n + 4) x := by
    rw [sum_shift x (n + 4) 1 (fun j hj => hx.2.1 j (by omega)) (fun j hj => hx.2.2 j (by omega))]
    rfl
  calc V (n + 4) x ≤ ∑ j ∈ range (n + 4), (x (j + 1) + x j) :=
        sum_le_sum fun j _ => by
          rw [abs_le]; constructor <;> linarith [hx.1 j, hx.1 (j + 1)]
    _ = 2 * S (n + 4) x := by rw [sum_add_distrib, h1]; unfold S; ring

lemma S_nonneg {n : ℕ} {x : ℕ → ℝ} (hx : Valid n x) : 0 ≤ S (n + 4) x :=
  sum_nonneg fun j _ => hx.1 j

lemma V_nonneg (M : ℕ) (x : ℕ → ℝ) : 0 ≤ V M x := sum_nonneg fun _ _ => abs_nonneg _

lemma S_x0 : S 4 x0 = 1 := by simp [S, x0]

lemma V_x0 : V 4 x0 = 2 := by simp [V, x0, sum_range_succ]; norm_num

/-- **Theorem A.** For `0 < p ≤ 1`, `E[S_n] ≥ λⁿ` with `λ = p² + √(p⁴ + 4p(1-p))`. -/
theorem theoremA {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (n : ℕ) :
    lamA p ^ n ≤ Exp p n (S (n + 4)) := by
  set lam := lamA p
  have hl := lamA_nonneg p
  have hD : 0 < lam + 2 * p * (1 - p) := by
    have : 0 < lam := by
      unfold lam lamA; have : 0 < p ^ 2 := by positivity
      linarith [Real.sqrt_nonneg (p ^ 4 + 4 * p * (1 - p))]
    nlinarith [mul_nonneg hp0.le (by linarith : (0 : ℝ) ≤ 1 - p)]
  set t := (1 - p) / (lam + 2 * p * (1 - p)) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hD.le
  have htD : t * (lam + 2 * p * (1 - p)) = 1 - p := by rw [ht, div_mul_cancel₀ _ hD.ne']
  have hsq := lamA_sq hp0.le hp1
  let F : ℕ → (ℕ → ℝ) → ℝ := fun m y => S (m + 4) y + t * V (m + 4) y
  have hdrift : ∀ m y, Valid m y → lam * F m y ≤ P p m (F (m + 1)) y := by
    intro m y hy
    have e : P p m (F (m + 1)) y = P p m (S (m + 5)) y + t * P p m (V (m + 5)) y := by
      rw [show F (m + 1) = fun z => S (m + 5) z + t * V (m + 5) z from rfl, P_add]
      rw [show (P p m fun z => t * V (m + 5) z) = fun x => t * P p m (V (m + 5)) x from
        P_smul p t m (V (m + 5))]
    rw [e, P_S hy]
    have hV := P_V hp0.le hp1 hy
    have hS0 := S_nonneg hy
    have hV0 := V_nonneg (m + 4) y
    -- coefficient of S: 2p + 4p(1-p)t = λ; coefficient of V: (1-p) - 2p(1-p)t = λ t
    have c1 : 2 * p + 4 * p * (1 - p) * t = lam := by
      have : (2 * p + 4 * p * (1 - p) * t - lam) * (lam + 2 * p * (1 - p)) = 0 := by
        have : (2 * p + 4 * p * (1 - p) * t - lam) * (lam + 2 * p * (1 - p)) =
            (2 * p - lam) * (lam + 2 * p * (1 - p)) + 4 * p * (1 - p) * (t * (lam + 2 * p * (1 - p)))
            := by ring
        rw [this, htD]; nlinarith [hsq]
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    have c2 : (1 - p) - 2 * p * (1 - p) * t = lam * t := by nlinarith [htD]
    show lam * (S (m + 4) y + t * V (m + 4) y) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hV ht0]
  have hgrow := Exp_growth hp0.le hp1 hl F hdrift n
  have hF0 : F 0 x0 = 1 + 2 * t := by
    show S (0 + 4) x0 + t * V (0 + 4) x0 = 1 + 2 * t; simp [S_x0, V_x0]; ring
  -- `F ≤ (1 + 2t) S` on valid rows
  have hmono := Exp_mono hp0.le hp1 n (g := F n) (h := fun y => (1 + 2 * t) * S (n + 4) y)
    fun y hy => by
      show S (n + 4) y + t * V (n + 4) y ≤ _
      nlinarith [V_le_two_S hy, mul_le_mul_of_nonneg_left (V_le_two_S hy) ht0]
  rw [Exp_smul] at hmono
  have hpos : 0 < 1 + 2 * t := by linarith
  have h1 := hgrow.trans hmono
  rw [hF0] at h1
  exact le_of_mul_le_mul_left (by linarith) hpos

/-- `λ > 1` exactly in the range `p > 1 - 1/√2`, i.e. `2p² - 4p + 1 < 0`. -/
lemma one_lt_lamA {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : 2 * p ^ 2 - 4 * p + 1 < 0) :
    1 < lamA p := by
  have hsq := lamA_sq hp0 hp1
  have hl := lamA_nonneg p
  have hge : p ^ 2 ≤ lamA p := by
    unfold lamA; linarith [Real.sqrt_nonneg (p ^ 4 + 4 * p * (1 - p))]
  by_contra hc
  have hc' : lamA p ≤ 1 := not_lt.1 hc
  -- `λ ↦ λ² - 2p²λ` is increasing on `[p², 1]`, so `4p(1-p) = λ² - 2p²λ ≤ 1 - 2p²`
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - lamA p)
    (by nlinarith : (0 : ℝ) ≤ 1 + lamA p - 2 * p ^ 2)]

end RandPascal
