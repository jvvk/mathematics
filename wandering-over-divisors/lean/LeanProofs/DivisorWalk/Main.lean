import LeanProofs.DivisorWalk

open DivisorWalk

/-! Axiom audit: every result should depend only on `propext`, `Classical.choice`, `Quot.sound`. -/
#print axioms DivisorWalk.reflect
#print axioms DivisorWalk.sweep
#print axioms DivisorWalk.sweep_top
#print axioms DivisorWalk.climb
#print axioms DivisorWalk.diag
#print axioms DivisorWalk.bottom
#print axioms DivisorWalk.corner_right
#print axioms DivisorWalk.corner_left
#print axioms DivisorWalk.two_zero
#print axioms DivisorWalk.two_two

/-! The statements, as checked. -/
example (n k : ℕ) (hk : k < n) : BobAnswers n (insert (k + 1, k) {(k, k)}) (k + 1, k) := diag n k hk _ (Or.inl rfl)
example (n a : ℕ) (hn : 2 ≤ n) (h1 : 1 ≤ a) (h2 : a ≤ n) : BobAnswers n (insert (a, 1) {(a, 0)}) (a, 1) :=
  bottom n a hn h1 h2
example (n : ℕ) (hn : 3 ≤ n) : BobWins n {(2, 2)} (2, 2) := two_two n hn
