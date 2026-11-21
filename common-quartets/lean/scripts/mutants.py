"""Mutation tests for the Lean files: each mutant plants one wrong statement, constant or definition and
must make its file fail to compile. Run from lean/ after `lake build LeanProofs`.

Every target file must first compile unchanged (a per-target control). A mutant counts as rejected only when
Lean exits 1 with an error located in the mutated file; a timeout, a signal or any other failure is reported as
INCONCLUSIVE and fails the suite."""
import pathlib
import re, signal, subprocess, sys

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



RESOURCE = re.compile(r"maximum number of heartbeats|maximum recursion depth|deep recursion|stack overflow|out of memory", re.I)
INFRA = re.compile(r"unknown module|unknown package|unknown namespace|could not resolve|object file|no such file|failed to load|import", re.I)
PARSE = re.compile(r"(unexpected|expected) ")
LOGDIR = pathlib.Path(__file__).resolve().parent / "mutants-output"


def classify(code, out: str, fname: str, mline: int, tag: str) -> str:
    """COMPILES; REJECTED (exit 1, an elaboration error in `fname` at or after the mutated line `mline`, and no
    parse, import or resource error); otherwise INCONCLUSIVE. The full output is kept in mutants-output/."""
    LOGDIR.mkdir(exist_ok=True)
    (LOGDIR / f"{tag}.txt").write_text(f"exit {code}\n{out}")
    if code is None:
        return "INCONCLUSIVE (timeout)"
    errs = [(int(l), m) for l, m in re.findall(re.escape(fname) + r":(\d+):\d+: error: ?(.*)", out)]
    if code == 0 and not errs and not re.search(r": error", out):
        return "COMPILES"
    if RESOURCE.search(out):
        return f"INCONCLUSIVE (exit {code}, resource limit)"
    if any(PARSE.match(m) or INFRA.search(m) for _, m in errs) or (not errs and INFRA.search(out)):
        return f"INCONCLUSIVE (exit {code}, parse or import error)"
    if code == 1 and any(l >= mline for l, _ in errs):
        return "REJECTED"
    return f"INCONCLUSIVE (exit {code}, no error at or after the mutated line in {fname})"


def mutated_line(text: str, old: str) -> int:
    return text[: text.index(old)].count("\n") + 1


def run(src: str, mline: int, tag: str) -> str:
    try:
        r = subprocess.run(["lake", "env", "lean", src], capture_output=True, text=True, timeout=900)
    except subprocess.TimeoutExpired as e:
        return classify(None, str(e.stdout or "") + str(e.stderr or ""), src, mline, tag)
    return classify(r.returncode, r.stdout + r.stderr, src, mline, tag)


# a SIGTERM raises SystemExit, so the finally clause below restores a file mutated in place
signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))

ok = True
for src in sorted({m[0] for m in MUTANTS}):
    v = run(src, 0, "control-" + src.replace("/", "_"))
    print(f"control {src}: {v}", flush=True)
    ok &= v == "COMPILES"
if not ok:
    sys.exit("CONTROL FAILED: an unchanged target does not compile; mutants not run")

killed = 0
for killed_or_index, (src, name, old, new) in enumerate(MUTANTS):
    text = open(src).read()
    assert text.count(old) == 1, f"{name}: anchor not unique in {src}"
    open(src, "w").write(text.replace(old, new))
    try:
        v = run(src, mutated_line(text, old), f"mutant-{killed_or_index}")
    finally:
        open(src, "w").write(text)
    killed += v == "REJECTED"
    print(("killed   " if v == "REJECTED" else ("SURVIVED " if v == "COMPILES" else v + " ")) + f"{src}: {name}", flush=True)
print(f"{killed}/{len(MUTANTS)} mutants killed")
sys.exit(0 if killed == len(MUTANTS) else 1)
