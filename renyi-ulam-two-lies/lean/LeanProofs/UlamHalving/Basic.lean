import Mathlib

/-!
# The Rényi-Ulam liar game with two lies

A state `(a, b, c)` counts the candidates contradicted by `0`, `1` and `2` answers. A question `(u, v, w)` with
`u ≤ a`, `v ≤ b`, `w ≤ c` names how many of each class are in the queried set. The answer YES leaves
`(u, v + (a - u), w + (b - v))`; NO leaves `(a - u, (b - v) + u, (c - w) + v)`. Paul has won when at most one
candidate remains. `Solv n x`: Paul can win from `x` within `n` questions.

Berlekamp's volume `V n (a, b, c) = W n * a + (n + 1) * b + c`, `W n = 1 + n + C(n, 2)`, is conserved by every
question, so a solvable state has volume at most `2^n`.
-/

namespace UlamHalving

/-- A state of the two-lie game. -/
structure St where
  a : ℕ
  b : ℕ
  c : ℕ

def St.size (x : St) : ℕ := x.a + x.b + x.c

/-- Children of a question `(u, v, w)`. -/
def yes (x : St) (u v w : ℕ) : St := ⟨u, v + (x.a - u), w + (x.b - v)⟩
def no (x : St) (u v w : ℕ) : St := ⟨x.a - u, (x.b - v) + u, (x.c - w) + v⟩

/-- `Solv n x`: Paul wins from `x` within `n` questions. -/
inductive Solv : ℕ → St → Prop
  | win {n : ℕ} {x : St} : x.size ≤ 1 → Solv n x
  | step {n : ℕ} {x : St} (u v w : ℕ) : u ≤ x.a → v ≤ x.b → w ≤ x.c →
      Solv n (yes x u v w) → Solv n (no x u v w) → Solv (n + 1) x

/-- Weight of a candidate with two lies left, `1 + n + C(n, 2)`. -/
def W (n : ℕ) : ℕ := 1 + n + n.choose 2

/-- Berlekamp's volume. -/
def V (n : ℕ) (x : St) : ℕ := W n * x.a + (n + 1) * x.b + x.c

lemma W_succ (n : ℕ) : W (n + 1) = W n + (n + 1) := by
  simp only [W, Nat.choose_succ_succ', Nat.choose_one_right]; ring

/-- **Conservation of volume.** -/
theorem V_conserve (n : ℕ) (x : St) (u v w : ℕ) (hu : u ≤ x.a) (hv : v ≤ x.b) (hw : w ≤ x.c) :
    V (n + 1) x = V n (yes x u v w) + V n (no x u v w) := by
  obtain ⟨a, b, c⟩ := x
  simp only [V, yes, no, W_succ] at *
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hu
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hv
  obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hw
  simp only [Nat.add_sub_cancel_left]; ring

lemma W_le (n : ℕ) : W n ≤ 2 ^ n := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
    rw [W_succ, pow_succ]
    have : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    have : 1 + n ≤ W n := by simp [W]
    omega

/-- **The volume bound**: a solvable state has volume at most `2^n`. -/
theorem V_le (n : ℕ) (x : St) (h : Solv n x) : V n x ≤ 2 ^ n := by
  induction h with
  | @win n x hx =>
    obtain ⟨a, b, c⟩ := x
    simp only [St.size] at hx
    have hW := W_le n
    have h1 : n + 1 ≤ W n := by simp [W]; omega
    simp only [V]
    rcases (by omega : (a = 1 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 1 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c ≤ 1)) with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, hc⟩ <;> nlinarith [Nat.one_le_two_pow (n := n)]
  | @step n x u v w hu hv hw _ _ ihY ihN =>
    rw [V_conserve n x u v w hu hv hw, pow_succ]; omega

end UlamHalving
