# Lean formalisation: labelling binary trees by powers of two

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that ten wrong variants fail.

Trees and labellings, in Lean (namespace `PowTwoTrees`, file `Basic.lean`):

```lean
inductive BT
  | leaf : BT
  | one : BT → BT
  | two : BT → BT → BT

inductive Fits : BT → Finset ℕ → ℕ → Prop
  | leaf (r : ℕ) : Fits .leaf {r} r
  | one {c S r} (k : ℕ) : Fits c S (r + 2 ^ k) → r ∉ S → Fits (.one c) (insert r S) r
  | two {a b A B r} (i j : ℕ) :
      Fits a A (r + 2 ^ i) → Fits b B (r + 2 ^ j) → Disjoint A B → r ∉ A → r ∉ B →
      Fits (.two a b) (insert r (A ∪ B)) r

def Labelled (t : BT) : Prop := Fits t (Finset.range t.size) 0
```

`Fits t S r` says that `t` is labelled bijectively by `S`, the root by `r`, and each child by its parent's
label plus a power of two. `two a b` and `two b a` are the same tree (`fits_two_comm`).

| Note | Lean | File |
|---|---|---|
| Labels increase; the set has `t.size` elements | `Fits.basic` | `Basic.lean` |
| Shifting and doubling preserve labellings | `Fits.shift`, `Fits.double`, `Fits.unshift` | `Basic.lean` |
| Theorem 1(a): a single child at the root | `unary_root` | `Reductions.lean` |
| Theorem 1(b): branch sizes equal or differing by one | `parity` | `Reductions.lean` |
| Theorem 1(c): a branch of size `2^k − 1` | `mersenne` | `Reductions.lean` |
| Theorem 1(d): one chain above a subtree | `prefix_case1`, `prefix_case2`, `fits_pre` | `Reductions.lean` |
| Theorem 1(e): two chains | `two_prefix_case1`, `two_prefix_case2` | `Reductions.lean` |
| Lemma 2: the tail lemma | `tail` | `Universal.lean` |
| Lemma 3: the primitive tail; the generation rule (1) | `primitive_tail`, `two_powers` | `Universal.lean` |
| Corollary 4: primitive universal sets lie in `[0, 2^(n−2)]` | `span_bound` | `Universal.lean` |

In Theorem 1, the hypotheses "every tree named below is labelled" become hypotheses `Labelled c`,
`Labelled b`, … on the smaller trees, so each statement is the construction itself, for every size.

## What is not formalised

- Proposition 5 and Table 1: exhaustive searches, done by the programs in `verify/` (searches stay out of the
  Lean kernel).
