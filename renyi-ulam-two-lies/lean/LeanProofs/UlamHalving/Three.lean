import Mathlib

/-!
# Even splitting fails with three lies

A state `(a, b, c, d)` of the three-lie Rényi-Ulam game counts the candidates contradicted by `0, 1, 2, 3` answers.
A question `(u, v, w, t)` with `u ≤ a, v ≤ b, w ≤ c, t ≤ d` names how many of each class are queried; a candidate
moves up one class when the answer disagrees with it. `Solv n x`: the questioner wins from `x` within `n` questions.

Berlekamp's volume `V n x = Σ x_i * W i n`, `W i n = Σ_{j ≤ 3 - i} C(n, j)`, is conserved, so a solvable state has
volume at most `2^n` (`V_le`).

Main result (`not_solv_105`): with `a = (2^105 - 153920) / 198592`, the halving child `(a, a + 26, 86, 60)` of the
even state `(2a, 52, 120, 0)` is not solvable in `105` questions, although its volume is `2^105 - 28`. The proof is
the paper's: the first question's YES volume modulo `C(104, 2) = 5356` forces two cases, and in each case one child
fails the volume bound for its own first question modulo `103`.

That the even state itself is solvable in `106` questions is certified outside Lean, by a list of `2126` explicit
questions checked by two independent programs (see the paper, Section 7).
-/

namespace UlamHalving.Three

/-- A state of the three-lie game. -/
structure St where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ

def St.size (x : St) : ℕ := x.a + x.b + x.c + x.d

/-- Children of a question `(u, v, w, t)`. -/
def yes (x : St) (u v w t : ℕ) : St := ⟨u, v + (x.a - u), w + (x.b - v), t + (x.c - w)⟩
def no (x : St) (u v w t : ℕ) : St := ⟨x.a - u, (x.b - v) + u, (x.c - w) + v, (x.d - t) + w⟩

/-- `Solv n x`: the questioner wins from `x` within `n` questions. -/
inductive Solv : ℕ → St → Prop
  | win {n : ℕ} {x : St} : x.size ≤ 1 → Solv n x
  | step {n : ℕ} {x : St} (u v w t : ℕ) : u ≤ x.a → v ≤ x.b → w ≤ x.c → t ≤ x.d →
      Solv n (yes x u v w t) → Solv n (no x u v w t) → Solv (n + 1) x

/-- Weights: answer sequences of length `n` along which a candidate with `3 - i` lies left survives. -/
def W0 (n : ℕ) : ℕ := 1 + n + n.choose 2 + n.choose 3
def W1 (n : ℕ) : ℕ := 1 + n + n.choose 2
def W2 (n : ℕ) : ℕ := 1 + n

/-- Berlekamp's volume. -/
def V (n : ℕ) (x : St) : ℕ := W0 n * x.a + W1 n * x.b + W2 n * x.c + x.d

lemma W0_succ (n : ℕ) : W0 (n + 1) = W0 n + W1 n := by
  simp only [W0, W1, Nat.choose_succ_succ', Nat.choose_one_right]; ring

lemma W1_succ (n : ℕ) : W1 (n + 1) = W1 n + W2 n := by
  simp only [W1, W2, Nat.choose_succ_succ', Nat.choose_one_right]; ring

/-- **Conservation of volume.** -/
theorem V_conserve (n : ℕ) (x : St) (u v w t : ℕ) (hu : u ≤ x.a) (hv : v ≤ x.b) (hw : w ≤ x.c)
    (ht : t ≤ x.d) : V (n + 1) x = V n (yes x u v w t) + V n (no x u v w t) := by
  obtain ⟨a, b, c, d⟩ := x
  simp only [V, yes, no, W0_succ, W1_succ] at *
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hu
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hv
  obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hw
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le ht
  simp only [Nat.add_sub_cancel_left, W2]; ring

lemma W_le (n : ℕ) : W0 n ≤ 2 ^ n ∧ W1 n ≤ 2 ^ n ∧ W2 n ≤ 2 ^ n := by
  induction n with
  | zero => simp [W0, W1, W2]
  | succ n ih =>
    have h2 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    refine ⟨?_, ?_, ?_⟩
    · rw [W0_succ, pow_succ]; omega
    · rw [W1_succ, pow_succ]; omega
    · simp only [W2, pow_succ]; omega

/-- **The volume bound**: a solvable state has volume at most `2^n`. -/
theorem V_le (n : ℕ) (x : St) (h : Solv n x) : V n x ≤ 2 ^ n := by
  induction h with
  | @win n x hx =>
    obtain ⟨a, b, c, d⟩ := x
    simp only [St.size] at hx
    obtain ⟨h0, h1, h2⟩ := W_le n
    have h21 : W2 n ≤ W1 n := by simp [W1, W2]
    have h10 : W1 n ≤ W0 n := by simp [W0, W1]
    have hW2 : 1 ≤ W2 n := by simp [W2]
    simp only [V]
    rcases (by omega : (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨ (a = 0 ∧ b = 1 ∧ c = 0 ∧ d = 0) ∨
        (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d ≤ 1)) with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, hd⟩ <;>
      nlinarith [Nat.one_le_two_pow (n := n)]
  | @step n x u v w t hu hv hw ht _ _ ihY ihN =>
    rw [V_conserve n x u v w t hu hv hw ht, pow_succ]; omega

/-- A state with at least two candidates that is solvable in `n + 1` questions has a first question whose
children are solvable in `n`; with conservation, the YES child's volume is pinned between
`V (n+1) x - 2^n` and `2^n`. -/
lemma first_question {n : ℕ} {x : St} (h : Solv (n + 1) x) (hx : 2 ≤ x.size) :
    ∃ u v w t, u ≤ x.a ∧ v ≤ x.b ∧ w ≤ x.c ∧ t ≤ x.d ∧
      V n (yes x u v w t) ≤ 2 ^ n ∧ V n (no x u v w t) ≤ 2 ^ n ∧
      Solv n (yes x u v w t) ∧ Solv n (no x u v w t) := by
  cases h with
  | win hs => omega
  | step u v w t hu hv hw ht hY hN =>
    exact ⟨u, v, w, t, hu, hv, hw, ht, V_le _ _ hY, V_le _ _ hN, hY, hN⟩

/-- The integer `a` of the counterexample. -/
def A : ℕ := 204262101229170061472237061

lemma A_spec : 198592 * A = 2 ^ 105 - 153920 := by norm_num [A]

/-- The halving child of `(2A, 52, 120, 0)`. -/
def h : St := ⟨A, A + 26, 86, 60⟩

lemma h_eq_halving : yes ⟨2 * A, 52, 120, 0⟩ A 26 60 0 = h ∧ no ⟨2 * A, 52, 120, 0⟩ A 26 60 0 = h := by
  simp only [yes, no, h]; constructor <;> congr 1

lemma choose2 (n : ℕ) : n.choose 2 = n * (n - 1) / 2 := Nat.choose_two_right n
lemma c103_2 : (103 : ℕ).choose 2 = 5253 := by rw [Nat.choose_two_right]
lemma c104_2 : (104 : ℕ).choose 2 = 5356 := by rw [Nat.choose_two_right]
lemma c105_2 : (105 : ℕ).choose 2 = 5460 := by rw [Nat.choose_two_right]
lemma c103_3 : (103 : ℕ).choose 3 = 176851 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; rfl
lemma c104_3 : (104 : ℕ).choose 3 = 182104 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; rfl
lemma c105_3 : (105 : ℕ).choose 3 = 187460 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; rfl

/-- The halving child's volume is `2^105 - 28`: the volume bound alone does not exclude `105` questions. -/
theorem V_h : V 105 h = 2 ^ 105 - 28 := by
  simp only [V, W0, W1, W2, h, c105_2, c105_3, A]; norm_num

/-- **Second-level obstruction.** If a state `z` is solvable in `104` questions, its first question's YES volume at
depth `103` is `2^103 - ℓ` with `0 ≤ ℓ ≤ σ = 2^104 - V 104 z`, and every coefficient of that volume except the
last-class one is a multiple of `103`. Stated as: there are `M, ℓ, t'` with `t' ≤ z.d`, `ℓ + V 104 z ≤ 2^104`, and
`W1 103 * z.a + 104 * z.b + z.c + 103 * M + t' + ℓ = 2^103`. -/
lemma second_level {z : St} (hz : Solv 104 z) (h2 : 2 ≤ z.size) :
    ∃ M ℓ t', t' ≤ z.d ∧ ℓ + V 104 z ≤ 2 ^ 104 ∧
      W1 103 * z.a + 104 * z.b + z.c + 103 * M + t' + ℓ = 2 ^ 103 := by
  obtain ⟨u, v, w, t, hu, hv, hw, ht, hY, hN, -, -⟩ := first_question hz h2
  have hc : V 104 z = V 103 (yes z u v w t) + V 103 (no z u v w t) := V_conserve 103 z u v w t hu hv hw ht
  refine ⟨1717 * u + 51 * v + w, 2 ^ 103 - V 103 (yes z u v w t), t, ht, ?_, ?_⟩
  · omega
  · obtain ⟨a, b, c, d⟩ := z
    simp only [V, yes, W0, W1, W2, c103_2, c103_3] at hY ⊢
    simp only at hu hv hw ht
    omega

/-- First level, as arithmetic: the YES volume of a first question `(u, v, w, t)` from `h` is
`5566 A + 2816 + 182104 u + 5356 v + 104 w + t`, and `182104 = 34 * 5356`; with slack `λ ≤ 28` only two
values of `(w, t + λ)` reach `2^104`. -/
lemma first_level (u v w t l : ℕ) (hw : w ≤ 86) (ht : t ≤ 60) (hl : l ≤ 28)
    (e : 5566 * A + 2816 + 182104 * u + 5356 * v + 104 * w + t + l = 2 ^ 104) :
    (w = 17 ∧ t + l = 70) ∨ (w = 69 ∧ t + l = 18) := by
  -- write the u, v part as a multiple of 5356; then each w leaves one unknown multiple
  have e' : 5356 * (34 * u + v) + 104 * w + (t + l) = 2 ^ 104 - 5566 * A - 2816 := by
    simp only [A] at e ⊢; omega
  simp only [A] at e'
  interval_cases w <;> omega

/-- Second level, YES child: its residue is `2A + 26 + w` modulo `103`; with `w = 69` the remainder needed is `69`,
more than the `35` available. -/
lemma yes_fails (K s : ℕ) (hs : s ≤ 35) (e : 103 * K + 2 * A + 26 + 69 + s = 2 ^ 103) : False := by
  simp only [A] at e; omega

/-- Second level, NO child: its residue is `2A + 2790 - w` modulo `103`; with `w = 17` the remainder needed is
`69`, more than the `35` available. -/
lemma no_fails (K s : ℕ) (hs : s ≤ 35) (e : 103 * K + 2 * A + 2790 + s = 2 ^ 103 + 17) : False := by
  simp only [A] at e; omega

/-- **The halving child is not solvable in `105` questions.** -/
theorem not_solv_105 : ¬ Solv 105 h := by
  intro hs
  have hsz : 2 ≤ h.size := by simp [St.size, h, A]
  obtain ⟨u, v, w, t, hu, hv, hw, ht, hY, hN, sY, sN⟩ := first_question hs hsz
  have hc : V 105 h = V 104 (yes h u v w t) + V 104 (no h u v w t) := V_conserve 104 h u v w t hu hv hw ht
  rw [V_h] at hc
  simp only [h] at hu hv hw ht
  have szY : 2 ≤ (yes h u v w t).size := by simp only [St.size, yes, h]; omega
  have szN : 2 ≤ (no h u v w t).size := by simp only [St.size, no, h]; omega
  obtain ⟨M1, l1, t1, ht1, hl1, e1⟩ := second_level sY szY
  obtain ⟨M2, l2, t2, ht2, hl2, e2⟩ := second_level sN szN
  have hYv : V 104 (yes h u v w t) = 5566 * A + 2816 + 182104 * u + 5356 * v + 104 * w + t := by
    simp only [V, yes, h, W0, W1, W2, c104_2, c104_3]; omega
  -- slack of the YES child
  set l := 2 ^ 104 - V 104 (yes h u v w t) with hl
  have hl28 : l ≤ 28 := by omega
  have hcase := first_level u v w t l hw ht hl28 (by omega)
  -- the two children's second-level equations, with the multiples of 103 collected
  have hYc : W1 103 * (yes h u v w t).a + 104 * (yes h u v w t).b + (yes h u v w t).c =
      103 * (51 * u + v + A) + 2 * A + 26 + w := by
    simp only [W1, yes, h, c103_2]; omega
  have hNc : W1 103 * (no h u v w t).a + 104 * (no h u v w t).b + (no h u v w t).c + 103 * (51 * u + v) + w =
      103 * (53 * A) + 2 * A + 2790 := by
    simp only [W1, no, h, c103_2]; omega
  have hYd : (yes h u v w t).d = t + (86 - w) := by simp [yes, h]
  have hNd : (no h u v w t).d = (60 - t) + w := by simp [no, h]
  rcases hcase with ⟨rfl, htl⟩ | ⟨rfl, htl⟩
  · -- w = 17: the NO child fails
    refine no_fails (M2 + 53 * A - 51 * u - v) (t2 + l2) (by omega) ?_
    have : 51 * u + v ≤ M2 + 53 * A := by simp only [A] at hu hv ⊢; omega
    omega
  · -- w = 69: the YES child fails
    exact yes_fails (M1 + 51 * u + v + A) (t1 + l1) (by omega) (by omega)

end UlamHalving.Three
