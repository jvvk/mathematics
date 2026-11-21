#!/usr/bin/env python3
"""Mutation tests for LeanProofs/ZeroSumGame (MO 453809): every wrong variant must FAIL to check.

Each mutant copies one file to ZeroSumGame/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). Unmutated copies must pass (baseline). A mutant counts
as rejected only on exit 1 with an elaboration error located in Mut.lean; timeouts, signals, resource limits
and parse errors are inconclusive and fail the suite.
"""
import os
import pathlib
import re
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "ZeroSumGame"
MUT = D / "Mut.lean"

MUTANTS = [
    ("rank lemma: 1 + sum q -> 2 + sum q", "Dimension.lean",
     "    (∑ i, q i) + 1 ≤ finrank ℝ (incidenceSpan H) := by",
     "    (∑ i, q i) + 2 ≤ finrank ℝ (incidenceSpan H) := by"),
    ("square game: n(n+1)/2 - 1 -> n(n+1)/2 - 2", "Dimension.lean",
     "      finrank ℝ L ≤ n * (n + 1) / 2 - 1) ∧", "      finrank ℝ L ≤ n * (n + 1) / 2 - 2) ∧"),
    ("order 3: one usable position instead of two", "Order3.lean",
     "∃ j l : Fin 3, j ≠ j₀ ∧", "∃ j l : Fin 3, True ∧"),
    ("collision: p + r doubled when p = r (should be p = s)", "Gaps.lean",
     "(t = p + r ∧ p = s)", "(t = p + r ∧ p = r)"),
    ("family IV: s = p -> s = 2p", "Gaps.lean",
     "(q = 2 * p ∧ r = p ∧ s = p)", "(q = 2 * p ∧ r = p ∧ s = 2 * p)"),
    ("third row (0, r, r+s) -> (0, r, s)", "Gaps.lean",
     "def Qv (r s : ℝ) : Fin 3 → ℝ := ![0, r, r + s]", "def Qv (r s : ℝ) : Fin 3 → ℝ := ![0, r, s]"),
    ("two values: isolation needs k <= count -> k < count", "TwoValued.lean",
     "∀ E : I → Option Bool, (∀ i b, E i = some b → k i ≤ (posOf a val i b).card) →",
     "∀ E : I → Option Bool, (∀ i b, E i = some b → k i < (posOf a val i b).card) →"),
]


RESOURCE = re.compile(r"maximum number of heartbeats|maximum recursion depth|deep recursion|stack overflow|out of memory", re.I)
PARSE = re.compile(r"(unexpected|expected) ")


def check(text: str) -> str:
    """COMPILES, REJECTED (exit 1 with an elaboration error located in Mut.lean) or INCONCLUSIVE (timeout,
    signal, resource limit, parse error only, or no error located in Mut.lean); diagnostics are kept."""
    MUT.write_text(text)
    p = subprocess.Popen(["nice", "-n", "15", "lake", "env", "lean", str(MUT)], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                         start_new_session=True)
    try:
        out, _ = p.communicate(timeout=1200)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)  # lake's lean child too
        p.communicate()
        return "INCONCLUSIVE: timeout after 1200 s"
    errs = re.findall(r"Mut\.lean:\d+:\d+: error: ?(.*)", out)
    if p.returncode == 0 and not errs:
        return "COMPILES"
    if RESOURCE.search(out):
        return f"INCONCLUSIVE: exit {p.returncode}, resource limit: " + out[-500:]
    if errs and all(PARSE.match(e) for e in errs):
        return f"INCONCLUSIVE: exit {p.returncode}, parse error only: " + errs[0]
    if p.returncode == 1 and errs:
        return "REJECTED: " + errs[0][:120]
    return f"INCONCLUSIVE: exit {p.returncode}, no error located in Mut.lean: " + out[-500:]


def main() -> int:
    bad = 0
    sel = [m for m in MUTANTS if not sys.argv[1:] or any(a in m[1] for a in sys.argv[1:])]
    try:
        for f in sorted({m[1] for m in sel}):
            v = check((D / f).read_text())
            print(f"baseline {f}: {v}", flush=True)
            bad += v != "COMPILES"
        if bad:
            print("BASELINE FAILED: an unchanged file does not compile; mutants not run")
            return 1
        for name, f, old, new in sel:
            src = (D / f).read_text()
            if src.count(old) != 1:
                print(f"MUTATION DID NOT APPLY: {name}", flush=True)
                bad += 1
                continue
            v = check(src.replace(old, new))
            print(f"{'rejected' if v.startswith('REJECTED') else v.split(':')[0]}: {name}  [{v}]", flush=True)
            bad += not v.startswith("REJECTED")
    finally:
        MUT.unlink(missing_ok=True)
    print(f"{len(sel)} mutants, {bad} problems")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
