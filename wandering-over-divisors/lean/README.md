# Lean formalisation: wandering over the divisors of a power of ten

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that ten wrong variants fail.

The game, in Lean (namespace `DivisorWalk`, file `Game.lean`):

```lean
def Move (n : ℕ) (p q : Sq) : Prop :=
  q.1 ≤ n ∧ q.2 ≤ n ∧
    (q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1) ∨ (1 ≤ p.1 ∧ 1 ≤ p.2 ∧ q = (p.1 - 1, p.2 - 1)))

inductive BobWins (n : ℕ) : Finset Sq → Sq → Prop
  | mk {V : Finset Sq} {p : Sq} (f : Sq → Sq)
      (hmove : ∀ q, Move n p q → q ∉ V → Move n q (f q))
      (hfree : ∀ q, Move n p q → q ∉ V → f q ∉ insert q V)
      (hwin : ∀ q, Move n p q → q ∉ V → BobWins n (insert (f q) (insert q V)) (f q)) :
      BobWins n V p
```

`BobWins n V p` says that Alice is to move at `p` with the squares `V` named, and Bob has a winning
strategy: for each legal move `q` of Alice, Bob's reply `f q` is legal and unnamed, and Bob still wins after
it. The predicate is inductive, so the strategy tree is finite; when Alice has no legal move the condition
holds vacuously, which is the rule that the player who cannot move loses.

| Note | Lean | File |
|---|---|---|
| Reflection in the diagonal | `reflect` | `Game.lean` |
| Lemma 2: sweeping the right-hand edge; the top row | `sweep`, `sweep_top` | `Game.lean` |
| The diagonal climb (used in Theorems 3, 5, 7) | `climb` | `Game.lean` |
| Theorem 3: diagonal openings | `diag`, `corner_stuck` | `Theorems.lean` |
| Theorem 5: the bottom row, opening N | `bottom`, `bottom_phase1`, `bottom_end` | `Theorems.lean` |
| Theorem 7: corners, `(2, 0)`, `(2, 2)` | `corner_right`, `corner_left`, `two_zero`, `two_zero_after`, `two_two`, `two_climb`, `two_end` | `Theorems.lean` |

Theorem statements, as checked: `diag n k (hk : k < n) q (hq : q = (k + 1, k) ∨ q = (k, k + 1)) :
BobAnswers n (insert q {(k, k)}) q`; `bottom n a (hn : 2 ≤ n) (ha1 : 1 ≤ a) (ha : a ≤ n) :
BobAnswers n (insert (a, 1) {(a, 0)}) (a, 1)`; `two_two n (hn : 3 ≤ n) : BobWins n {(2, 2)} (2, 2)`, and so
on, where `BobAnswers n V q` says Bob, to move at `q` with `V` named, has a reply after which he wins.

## What is not formalised

- Theorem 1 and every table: these are exhaustive searches, done by two independent programs in `verify/`
  (searches stay out of the Lean kernel).
- Conjecture 8 and the remarks of Section 8: conjectures and computational observations, checked in
  `verify/`.
