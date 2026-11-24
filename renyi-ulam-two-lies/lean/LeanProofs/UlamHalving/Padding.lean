import LeanProofs.UlamHalving.Mono

/-!
# Padding with candidates that have no lies left (PROOF.md, Lemma 1, sufficiency)

If `(a, b, c₀)` is solvable within `n` questions, then adding last-class candidates keeps it solvable as long as
the volume bound holds. The proof follows the strategy for `(a, b, c₀)` and, at each question, sends as many of
the new candidates to the YES side as its spare volume `2^(n-1) - V(YES)` allows; the rest go to the NO side,
whose spare volume is then enough by conservation. At a leaf (at most one candidate) the state left has
`a + b ≤ 1`, and `small` solves it by asking about the one non-last-class candidate together with as many
last-class candidates as the YES side can take.
-/

namespace UlamHalving

lemma V_small_le (n a b : ℕ) (h : a + b ≤ 1) : V n ⟨a, b, 0⟩ ≤ 2 ^ n := by
  have hW := W_le n
  have h1 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  simp only [V]
  rcases (by omega : (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1)) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

/-- A state with at most one candidate outside the last class is solvable whenever its volume allows. -/
theorem small : ∀ (n : ℕ) (x : St), x.a + x.b ≤ 1 → V n x ≤ 2 ^ n → Solv n x := by
  intro n
  induction n with
  | zero =>
    intro x _ hV
    apply Solv.win
    simp only [V, St.size, W, pow_zero, Nat.choose_zero_succ] at *
    omega
  | succ n ih =>
    intro x hab hV
    obtain ⟨a, b, c⟩ := x
    simp only at hab
    have h0 := V_small_le n a b hab
    set w := min c (2 ^ n - V n ⟨a, b, 0⟩) with hw
    have cons := V_conserve n ⟨a, b, c⟩ a b w le_rfl le_rfl (min_le_left _ _)
    have eY : yes ⟨a, b, c⟩ a b w = ⟨a, b, w⟩ := by simp only [yes, Nat.sub_self]; simp
    have eN : no ⟨a, b, c⟩ a b w = ⟨0, a, c - w + b⟩ := by simp only [no, Nat.sub_self]; congr 1; omega
    have hY : V n ⟨a, b, w⟩ = V n ⟨a, b, 0⟩ + w := by simp only [V]; ring
    have hN : V n ⟨0, a, c - w + b⟩ = (n + 1) * a + b + (c - w) := by simp only [V]; ring
    rw [eY, eN] at cons
    refine Solv.step a b w le_rfl le_rfl (min_le_left _ _) ?_ ?_
    · rw [eY]; exact ih _ (by simp only; omega) (by omega)
    · rw [eN]
      refine ih _ (by simp only; omega) ?_
      rw [pow_succ] at hV
      rw [hY, hN] at cons
      rw [hN]
      have h1 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
      have h2 : (n + 1) * a + b ≤ 2 ^ n := by
        rcases (by omega : a = 0 ∨ (a = 1 ∧ b = 0)) with rfl | ⟨rfl, rfl⟩ <;> simp <;> omega
      omega

/-- **Padding, general form.** Adding `k` last-class candidates to a solvable state keeps it solvable whenever
the volume bound still holds. -/
theorem pad {n : ℕ} {x : St} (h : Solv n x) :
    ∀ k : ℕ, V n ⟨x.a, x.b, x.c + k⟩ ≤ 2 ^ n → Solv n ⟨x.a, x.b, x.c + k⟩ := by
  induction h with
  | @win n x hx =>
    intro k hV
    exact small n _ (by simp only [St.size] at hx ⊢; omega) hV
  | @step n x u v w hu hv hw hY hN ihY ihN =>
    intro k hV
    obtain ⟨a, b, c⟩ := x
    simp only at hu hv hw hV ⊢
    have vY := V_le _ _ hY
    have vN := V_le _ _ hN
    have cons := V_conserve n ⟨a, b, c⟩ u v w hu hv hw
    set k₁ := min k (2 ^ n - V n (yes ⟨a, b, c⟩ u v w)) with hk₁
    have hVk : V (n + 1) ⟨a, b, c + k⟩ = V (n + 1) ⟨a, b, c⟩ + k := by simp only [V]; ring
    refine Solv.step u v (w + k₁) hu hv (by simp only; omega) ?_ ?_
    · have e : yes ⟨a, b, c + k⟩ u v (w + k₁) =
          ⟨(yes ⟨a, b, c⟩ u v w).a, (yes ⟨a, b, c⟩ u v w).b, (yes ⟨a, b, c⟩ u v w).c + k₁⟩ := by
        simp only [yes]; congr 1; omega
      rw [e]
      apply ihY
      have : V n ⟨(yes ⟨a, b, c⟩ u v w).a, (yes ⟨a, b, c⟩ u v w).b, (yes ⟨a, b, c⟩ u v w).c + k₁⟩ =
          V n (yes ⟨a, b, c⟩ u v w) + k₁ := by simp only [V]; ring
      rw [this]; omega
    · have e : no ⟨a, b, c + k⟩ u v (w + k₁) =
          ⟨(no ⟨a, b, c⟩ u v w).a, (no ⟨a, b, c⟩ u v w).b, (no ⟨a, b, c⟩ u v w).c + (k - k₁)⟩ := by
        simp only [no]; congr 1; omega
      rw [e]
      apply ihN
      have : V n ⟨(no ⟨a, b, c⟩ u v w).a, (no ⟨a, b, c⟩ u v w).b, (no ⟨a, b, c⟩ u v w).c + (k - k₁)⟩ =
          V n (no ⟨a, b, c⟩ u v w) + (k - k₁) := by simp only [V]; ring
      rw [this]
      rw [hVk, cons, pow_succ] at hV
      omega

/-- **Lemma 1 (sufficiency).** If `(a, b, 0)` is solvable within `n` questions, then `(a, b, c)` is solvable
within `n` questions whenever `V n (a, b, c) ≤ 2^n`. -/
theorem padding {n a b c : ℕ} (h : Solv n ⟨a, b, 0⟩) (hV : V n ⟨a, b, c⟩ ≤ 2 ^ n) : Solv n ⟨a, b, c⟩ := by
  have := pad h c (by simpa using hV)
  simpa using this

/-- Lemma 1 with any starting last coordinate `c₀ ≤ c`. -/
theorem padding' {n a b c₀ c : ℕ} (h : Solv n ⟨a, b, c₀⟩) (hc : c₀ ≤ c) (hV : V n ⟨a, b, c⟩ ≤ 2 ^ n) :
    Solv n ⟨a, b, c⟩ := by
  have := pad h (c - c₀) (by simp only; rwa [Nat.add_sub_cancel' hc])
  simp only [Nat.add_sub_cancel' hc] at this
  exact this

end UlamHalving
