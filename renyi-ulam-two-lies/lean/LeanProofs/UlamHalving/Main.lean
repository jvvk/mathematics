import LeanProofs.UlamHalving.Lemma3

/-!
# Even splitting is optimal (PROOF.md, Theorem, analytic range)

For every parent depth `n + 2 ≥ 16`, conditional on the depth-12 base of Lemma 2: if `(2a, 2b, 2c)` is solvable
within `n + 2` questions, its even-splitting child `(a, a + b, b + c)` is solvable within `n + 1`. Route:
deletion drops the `2c` last-class candidates; `key` gives the criterion for `(a, a + b, b)` and `lemma3` solves
it; padding restores `b + c`, whose volume bound is half the parent's (conservation under the halving question).
Depths below 16 are the finite certificate of PROOF.md, Section 2, and are not formalised here.
-/

namespace UlamHalving

lemma V_parent_full (n a b c : ℕ) : V (n + 2) ⟨2 * a, 2 * b, 2 * c⟩ = 2 * V (n + 1) ⟨a, a + b, b + c⟩ := by
  simp only [V, W_succ]; ring

/-- **Main theorem.** For parent depth `n + 2 ≥ 16`, assuming the depth-12 base: the even-splitting child of a
solvable even state is solvable. -/
theorem halving_child (base12 : ∀ a b c : ℕ, a ≤ b → 66 ≤ c → V 12 ⟨a, b, c⟩ ≤ 2 ^ 12 → Solv 12 ⟨a, b, c⟩)
    (n : ℕ) (hn : 14 ≤ n) (a b c : ℕ) (h : Solv (n + 2) ⟨2 * a, 2 * b, 2 * c⟩) :
    Solv (n + 1) ⟨a, a + b, b + c⟩ := by
  have h0 : Solv (n + 2) ⟨2 * a, 2 * b, 0⟩ := h.mono _ le_rfl le_rfl (Nat.zero_le _)
  have hcrit := key n a b (Nat.gcd n (n.choose 2)) (Nat.gcd_pos_of_pos_left _ (by omega))
    (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) h0
  have hV0 : V (n + 1) ⟨a, a + b, b⟩ ≤ 2 ^ (n + 1) := by
    have := s_nonneg n a b h0
    have : (V (n + 1) ⟨a, a + b, b⟩ : ℤ) ≤ 2 ^ (n + 1) := by linarith
    exact_mod_cast this
  have hz := lemma3 base12 n hn a b hcrit hV0
  have hV : V (n + 1) ⟨a, a + b, b + c⟩ ≤ 2 ^ (n + 1) := by
    have := V_le _ _ h
    rw [V_parent_full, pow_succ 2 (n + 1)] at this
    omega
  exact padding' hz (Nat.le_add_right b c) hV

lemma halving_children (a b c : ℕ) :
    yes ⟨2 * a, 2 * b, 2 * c⟩ a b c = ⟨a, a + b, b + c⟩ ∧ no ⟨2 * a, 2 * b, 2 * c⟩ a b c = ⟨a, a + b, b + c⟩ := by
  constructor <;> simp only [yes, no] <;> congr 1 <;> omega

/-- **Corollary: the halving question is optimal.** For parent depth `n + 2 ≥ 16`, assuming the depth-12 base,
an even state is solvable within `n + 2` questions if and only if the halving question `(a, b, c)` leads to two
children each solvable within `n + 1`. -/
theorem halving_optimal (base12 : ∀ a b c : ℕ, a ≤ b → 66 ≤ c → V 12 ⟨a, b, c⟩ ≤ 2 ^ 12 → Solv 12 ⟨a, b, c⟩)
    (n : ℕ) (hn : 14 ≤ n) (a b c : ℕ) :
    Solv (n + 2) ⟨2 * a, 2 * b, 2 * c⟩ ↔
      Solv (n + 1) (yes ⟨2 * a, 2 * b, 2 * c⟩ a b c) ∧ Solv (n + 1) (no ⟨2 * a, 2 * b, 2 * c⟩ a b c) := by
  obtain ⟨hy, hno⟩ := halving_children a b c
  constructor
  · intro h
    rw [hy, hno]
    exact ⟨halving_child base12 n hn a b c h, halving_child base12 n hn a b c h⟩
  · rintro ⟨h1, h2⟩
    exact Solv.step a b c (by simp only; omega) (by simp only; omega) (by simp only; omega) h1 h2

end UlamHalving
