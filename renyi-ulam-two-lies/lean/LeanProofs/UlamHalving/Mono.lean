import LeanProofs.UlamHalving.Basic

/-!
# Deletion monotonicity

Deleting candidates never spoils a winning strategy: if `x` is solvable within `n` questions and `x'` is
componentwise at most `x`, then so is `x'`. Each question `(u, v, w)` of a strategy for `x` is restricted to
`(min u x'.a, min v x'.b, min w x'.c)`; the restricted children are componentwise below the original children.
-/

namespace UlamHalving

/-- **Deletion monotonicity.** -/
theorem Solv.mono {n : ℕ} {x : St} (h : Solv n x) :
    ∀ x' : St, x'.a ≤ x.a → x'.b ≤ x.b → x'.c ≤ x.c → Solv n x' := by
  induction h with
  | @win n x hx =>
    intro x' ha hb hc
    exact Solv.win (by simp only [St.size] at *; omega)
  | @step n x u v w hu hv hw _ _ ihY ihN =>
    intro x' ha hb hc
    refine Solv.step (min u x'.a) (min v x'.b) (min w x'.c) (min_le_right _ _) (min_le_right _ _)
      (min_le_right _ _) ?_ ?_
    · apply ihY <;> simp only [yes] <;> omega
    · apply ihN <;> simp only [no] <;> omega

end UlamHalving
