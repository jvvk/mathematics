# Lean formalisation: Infinitely many integers that are not quotients of zero-free balanced ternary numbers

Lean 4 (v4.34.0), core library only (no Mathlib), about 31,000 lines, most of them generated.
`ZF m` says that `m` has a balanced ternary representation with every digit `1` or `-1`; each
theorem states `¬ ∃ m N : Int, 0 < m ∧ ZF m ∧ 0 < N ∧ ZF N ∧ N = n * m`, that is, `n ∉ B/B`.
Every theorem below depends only on Lean's standard axioms; `Audit.lean` prints them when compiled.

## Build

```
lake build             # about 2.5 minutes on a laptop; compiles every file and runs the axiom audit
```

## Where each result is

| Paper | Lean | File |
|---|---|---|
| Proposition 2.2 (the criterion), for a predicate and for a concrete carry list | `not_BB_of_inv`, `not_BB_of_cert` | `TernCore.lean` |
| Section 3, by hand: `4·3^k + 5`, `k ≥ 5`, and Corollary 1.2 | `four_pow_plus_five_not_in_BB`, `infinitely_many_exceptions` | `BT.lean` |
| Theorem 1.1: `4·3^k ± 5`, `8·3^k + 7`, `8·3^k + 17` (`k ≥ 5`), `8·3^k − 7` (`k ≥ 7`) | `Tern.not_BB_4_p5`, `_4_m5`, `_8_p7`, `_8_p17`, `_8_m7` | `Fam_4_p5.lean`, … |
| Theorem 1.3: the eight families on residue classes of `k` | `Tern.not_BB_8_m17_2r0`, `_16_p17_2r0`, `_10_m11_4r2`, `_10_m19_4r2`, `_20_m19_4r2`, `_5_m4_4r2`, `_5_p4_4r0`, `_40_p41_4r0` | `Fam_<a>_<b>_<M>r<r>.lean` |

`BT.lean` follows Section 3 line by line. The `Fam_*` files follow Section 4: each carry set of
Appendix A is an inductive predicate, closure is proved constructor by constructor with `omega`
(powers of 3 as atoms), and the values of `k` below 14 are closed by their exact carry sets,
checked by `decide`.

## Generator

`generator/gen_lean.py` writes the `Fam_*` files from the carry sets in `generator/hyps.json` and
`hyps2.json` (the data of Appendix A). It only chooses which constructor and index each move lands on;
Lean re-checks every choice. Regenerating all thirteen files reproduces them byte for byte:

```
cd generator
python3 gen_lean.py 4 5 5 14          # Theorem 1.1: a b first-k 14
python3 gen_lean.py 5 4 8 14 4 0      # Theorem 1.3: a b first-k 14 modulus residue
```

## Mutation tests

`python3 mutants.py` (after `lake build`, about 20 minutes) compiles an unchanged control, which must
succeed, and the eight corrupted versions listed in Section 5 of the paper, each of which must fail.
