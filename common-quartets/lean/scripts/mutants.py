"""Mutation tests for the Lean files: each mutant plants one wrong statement, constant or definition and
must make its file fail to compile. Run from lean/ after `lake build LeanProofs`."""
import os, subprocess, sys

MUTANTS = [
    ('LeanProofs/QuartetIter.lean', 'threshold 2*3^(k-1) instead of 2*3^(k-1)+1', '(hn : 2 * 3 ^ (k - 1) + 1 ≤ U.card)', '(hn : 2 * 3 ^ (k - 1) ≤ U.card)'),
    ('LeanProofs/QuartetIter.lean', 'three leaves per side claimed at the threshold', 'Disjoint X Y ∧ 2 ≤ X.card ∧ 2 ≤ Y.card ∧ ∀ i < k', 'Disjoint X Y ∧ 3 ≤ X.card ∧ 2 ≤ Y.card ∧ ∀ i < k'),
    ('LeanProofs/QuartetIter.lean', 'cell lemma with |U|/5', '    (U.card ≤ 6 * (X ∩ C).card ∧ U.card ≤ 6 * ((U \\ X) \\ C).card) ∨', '    (U.card ≤ 5 * (X ∩ C).card ∧ U.card ≤ 6 * ((U \\ X) \\ C).card) ∨'),
    ('LeanProofs/QuartetIter.lean', 'iteration loses only factor 2 per tree', '      U.card ≤ 2 * 3 ^ (j - 1) * X.card ∧ U.card ≤ 2 * 3 ^ (j - 1) * Y.card := by', '      U.card ≤ 2 * 2 ^ (j - 1) * X.card ∧ U.card ≤ 2 * 2 ^ (j - 1) * Y.card := by'),
    ('LeanProofs/QuartetIter.lean', '1/3-2/3 axiom weakened to 1/4', '    ∃ C ⊆ U, Sep C (U \\ C) ∧ U.card ≤ 3 * C.card ∧ U.card ≤ 3 * (U \\ C).card', '    ∃ C ⊆ U, Sep C (U \\ C) ∧ U.card ≤ 4 * C.card ∧ U.card ≤ 4 * (U \\ C).card'),
    ('LeanProofs/CatFamily.lean', 'claimed on 2^k+3 leaves (range h+1)', '    a.natAbs ≤ 2 ^ (k - 1) → b.natAbs ≤ 2 ^ (k - 1) → c.natAbs ≤ 2 ^ (k - 1) →\n    d.natAbs ≤ 2 ^ (k - 1) → ¬ Common k a b c d := by', '    a.natAbs ≤ 2 ^ (k - 1) + 1 → b.natAbs ≤ 2 ^ (k - 1) + 1 → c.natAbs ≤ 2 ^ (k - 1) + 1 →\n    d.natAbs ≤ 2 ^ (k - 1) + 1 → ¬ Common k a b c d := by'),
    ('LeanProofs/CatFamily.lean', 'one order fewer (j < k - 2)', '  disp (pos none) a b c d ∧ ∀ j < k - 1, disp (pos (some j)) a b c d', '  disp (pos none) a b c d ∧ ∀ j < k - 2, disp (pos (some j)) a b c d'),
    ('LeanProofs/CatFamily.lean', 'psi off by one', 'def psi (H : ℤ) (x : ℤ) : ℤ := if 0 < x then x - H else x + H', 'def psi (H : ℤ) (x : ℤ) : ℤ := if 0 < x then x - H + 1 else x + H'),
    ('LeanProofs/CatFamily.lean', 'outer split claimed below the second-highest bit', '    ∃ b < k - 1, (pos (some b) y < -(H : ℤ) ∧ (H : ℤ) < pos (some b) z) ∨', '    ∃ b < k - 2, (pos (some b) y < -(H : ℤ) ∧ (H : ℤ) < pos (some b) z) ∨'),
    ('LeanProofs/CommonQuartet.lean', 'T3 leaves 0 and 5 swapped (3 common quartets)', 'def T3 : Tr := L 0 ⋆ (((L 5 ⋆ L 9)', 'def T3 : Tr := L 5 ⋆ (((L 0 ⋆ L 9)'),
    ('LeanProofs/CommonQuartet.lean', 'leaf 12 duplicated as 11 in T2', 'def T2 : Tr := L 0 ⋆ ((L 12 ⋆', 'def T2 : Tr := L 0 ⋆ ((L 11 ⋆'),
    ('LeanProofs/CommonQuartet.lean', 'claimed on 14 leaves', 'theorem witness_leaves : onLeaves T1 13 ∧ onLeaves T2 13 ∧ onLeaves T3 13', 'theorem witness_leaves : onLeaves T1 14 ∧ onLeaves T2 13 ∧ onLeaves T3 13'),
    ('LeanProofs/CommonQuartet.lean', '715 quartets claimed as 714', '(quads 13).length = 715', '(quads 13).length = 714'),
    ('LeanProofs/CommonQuartet.lean', 'split test ignores the complement side', '  (S.contains x && S.contains y && !S.contains u && !S.contains v) ||\n  (!S.contains x && !S.contains y && S.contains u && S.contains v)', '  (S.contains x && S.contains y && !S.contains u && !S.contains v)'),
    ('LeanProofs/CommonQuartet.lean', 'only two of the three splits of a 4-set', '  [(a, b, c, d), (a, c, b, d), (a, d, b, c)]', '  [(a, b, c, d), (a, c, b, d)]'),
    ('LeanProofs/CommonQuartet.lean', 'cyclic form with x -> 5x instead of 3x', 'def times3 (x : Nat) : Nat := 3 * x % 13', 'def times3 (x : Nat) : Nat := 5 * x % 13'),
    ('LeanProofs/CommonQuartet.lean', 'cyclic T with leaves 1 and 8 swapped', 'def T : Tr := L 0 ⋆ (L 1 ⋆ ((((L 8 ⋆ L 11)', 'def T : Tr := L 0 ⋆ (L 8 ⋆ ((((L 1 ⋆ L 11)'),
]

killed = 0
for src, name, old, new in MUTANTS:
    text = open(src).read()
    assert text.count(old) == 1, f"{name}: anchor not unique in {src}"
    open(src, "w").write(text.replace(old, new))
    try:
        r = subprocess.run(["lake", "env", "lean", src], capture_output=True, text=True, timeout=900)
        dead = r.returncode != 0 or "error" in r.stdout + r.stderr
    finally:
        open(src, "w").write(text)
    killed += dead
    print(("killed   " if dead else "SURVIVED ") + f"{src}: {name}", flush=True)
print(f"{killed}/{len(MUTANTS)} mutants killed")
sys.exit(0 if killed == len(MUTANTS) else 1)
