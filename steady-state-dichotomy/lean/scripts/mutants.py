"""Mutation tests for the Lean files: each mutant plants one wrong count, sign, rate, Jacobian entry or root
interval and must make its file fail to compile, with a Lean error located in the mutated file. Crashes, timeouts,
resource limits and infrastructure failures count as failures of the harness, never as rejections. Run from lean/
after `lake build LeanProofs`."""
import os, re, subprocess, sys

MUTANTS = [
    ('LeanProofs/ZeroOneFour.lean', 'five positive states instead of four', 'S = {g r₁, g r₂, g r₃, g r₄} ∧ S.ncard = 4 ∧', 'S = {g r₁, g r₂, g r₃, g r₄} ∧ S.ncard = 5 ∧'),
    ('LeanProofs/ZeroOneFour.lean', 'first state det J positive (signs +,+,-,+)', '    detJ (X r₁) (Y r₁) r₁ < 0 ∧ 0 < detJ (X r₂) (Y r₂) r₂ ∧', '    0 < detJ (X r₁) (Y r₁) r₁ ∧ 0 < detJ (X r₂) (Y r₂) r₂ ∧'),
    ('LeanProofs/ZeroOneFour.lean', 'largest root in (94,95)', 'r₃ ∈ Ioo (6 / 5) (121 / 100) ∧ r₄ ∈ Ioo 93 94 ∧', 'r₃ ∈ Ioo (6 / 5) (121 / 100) ∧ r₄ ∈ Ioo 94 95 ∧'),
    ('LeanProofs/ZeroOneFour.lean', 'P coefficient 218 -> 217', 'def P (z : ℝ) : ℝ := z ^ 4 - 96 * z ^ 3 + 218 * z ^ 2 - 145 * z + 24', 'def P (z : ℝ) : ℝ := z ^ 4 - 96 * z ^ 3 + 217 * z ^ 2 - 145 * z + 24'),
    ('LeanProofs/ZeroOneFour.lean', 'inflow 0 -> X2 at rate 2', 'def f2 (x y z : ℝ) : ℝ := -8 * x * y + x * z + 1', 'def f2 (x y z : ℝ) : ℝ := -8 * x * y + x * z + 2'),
    ('LeanProofs/ZeroOneFour.lean', 'network bookkeeping: X1+X2 -> 0 at rate 6', '    f1 x y z = -7 * x * y - 1 * x * z + 1 * z + 1 * y * z - 1 * x * y ∧', '    f1 x y z = -6 * x * y - 1 * x * z + 1 * z + 1 * y * z - 1 * x * y ∧'),
    ('LeanProofs/ZeroOneFour.lean', 'Jacobian entry d f2/dz = -x', '     -8 * y + z, -8 * x, x;', '     -8 * y + z, -8 * x, -x;'),
    ('LeanProofs/ZeroOneFour.lean', 'det J coefficient -48 -> -47', 'def detJ (x y z : ℝ) : ℝ := -48 * x ^ 2', 'def detJ (x y z : ℝ) : ℝ := -47 * x ^ 2'),
    ('LeanProofs/ZeroOneFour.lean', 'curve x = (8z-1)/(z+23)', 'def X (z : ℝ) : ℝ := (8 * z - 1) / (z + 24)', 'def X (z : ℝ) : ℝ := (8 * z - 1) / (z + 23)'),
    ('LeanProofs/ZeroOneFour.lean', 'det J identity coefficient 191 -> 190', 'detJ (X z) (Y z) z = dP z / (z + 24) - (16 * z + 191) /', 'detJ (X z) (Y z) z = dP z / (z + 24) - (16 * z + 190) /'),
    ('LeanProofs/ZeroOneFive.lean', 'six positive states instead of five', 'S = {g r₁, g r₂, g r₃, g r₄, g r₅} ∧ S.ncard = 5 ∧', 'S = {g r₁, g r₂, g r₃, g r₄, g r₅} ∧ S.ncard = 6 ∧'),
    ('LeanProofs/ZeroOneFive.lean', 'four positive states instead of five', 'S = {g r₁, g r₂, g r₃, g r₄, g r₅} ∧ S.ncard = 5 ∧', 'S = {g r₁, g r₂, g r₃, g r₄, g r₅} ∧ S.ncard = 4 ∧'),
    ('LeanProofs/ZeroOneFive.lean', 'last state det J positive', '0 < detJ (X r₄) (Y r₄) r₄ ∧ detJ (X r₅) (Y r₅) r₅ < 0 := by', '0 < detJ (X r₄) (Y r₄) r₄ ∧ 0 < detJ (X r₅) (Y r₅) r₅ := by'),
    ('LeanProofs/ZeroOneFive.lean', 'smallest root interval shifted', 'r₁ ∈ Ioo (1 / 92549) (1 / 92548) ∧', 'r₁ ∈ Ioo (1 / 92548) (1 / 92547) ∧'),
    ('LeanProofs/ZeroOneFive.lean', 'rate X2 -> X1 doubled in f2', 'def f2 (x y z : ℝ) : ℝ := 1 / 2500 + x + x * z - 2 / 5 * y * z - 1 / 100000 * y', 'def f2 (x y z : ℝ) : ℝ := 1 / 2500 + x + x * z - 2 / 5 * y * z - 2 / 100000 * y'),
    ('LeanProofs/ZeroOneFive.lean', 'inflow 0 -> X1+X2 at 1/2000 in f1', 'def f1 (x y z : ℝ) : ℝ := 1 / 2500 - x', 'def f1 (x y z : ℝ) : ℝ := 1 / 2000 - x'),
    ('LeanProofs/ZeroOneFive.lean', 'network bookkeeping: X3 -> 0 at rate 1', '    f3 x y z = 5 * x - 2 / 5 * y * z - 1 / 2 * z := by', '    f3 x y z = 5 * x - 2 / 5 * y * z - 1 * z := by'),
    ('LeanProofs/ZeroOneFive.lean', 'eliminant coefficient 101000 -> 100000', '- 782738125 * z ^ 2 + 101000 * z - 1', '- 782738125 * z ^ 2 + 100000 * z - 1'),
    ('LeanProofs/ZeroOneFive.lean', 'Jacobian entry df3/dy = +2/5 z', '     5, -2 / 5 * z, -1 / 2 - 2 / 5 * y]', '     5, 2 / 5 * z, -1 / 2 - 2 / 5 * y]'),
    ('LeanProofs/ZeroOneFive.lean', 'M coefficient 8/5 -> 7/5', 'def M (z : ℝ) : ℝ := 8 / 5 * z', 'def M (z : ℝ) : ℝ := 7 / 5 * z'),
    ('LeanProofs/ZeroOneFive.lean', 'curve parametrisation D with 31999', 'def D (z : ℝ) : ℝ := 8000 * z ^ 2 - 32000 * z - 1', 'def D (z : ℝ) : ℝ := 8000 * z ^ 2 - 31999 * z - 1'),
]

def run_lean(src):
    try:
        r = subprocess.run(["lake", "env", "lean", src], capture_output=True, text=True, timeout=900)
    except subprocess.TimeoutExpired:
        return "TIMEOUT", "no Lean error line (timed out after 900s)"
    except OSError as e:
        return "INFRA", f"no Lean error line ({e})"
    output = re.sub(r"\x1b\[[0-9;]*m", "", r.stdout + "\n" + r.stderr)
    errors = [line for line in output.splitlines() if "error:" in line]
    first = errors[0] if errors else "no Lean error line"
    if r.returncode < 0:
        return "CRASH", f"signal {-r.returncode}; {first}"
    # Missing imports/toolchains are infrastructure failures, even with a source location.
    infra = re.search(r"toolchain|unknown module prefix|unknown package|no such file or directory|"
                      r"object file .* does not exist|failed to (?:download|load)|shared librar", output, re.I)
    if infra:
        return "INFRA", first + f" ({infra.group(0)})"
    located = []
    for line in errors:
        match = re.match(r"^(.+?):\d+:\d+:\s*error:", line)
        if match and os.path.realpath(match.group(1)) == os.path.realpath(src):
            located.append(line)
    # Resource limits (recursion depth, heartbeats, deterministic timeouts, memory) say nothing about the
    # mutated statement, so they are harness failures, not rejections.
    resource = re.search(r"maximum recursion depth|maxRecDepth|heartbeat|deterministic\)? timeout|"
                         r"out of memory|stack overflow", output, re.I)
    if resource:
        return "RESOURCE", first + f" ({resource.group(0)})"
    if r.returncode == 1 and located:
        return "REJECTED", located[0]
    if r.returncode == 0 and not errors:
        return "PASSED", first
    detail = next((line for line in output.splitlines() if line.strip()), "no output")
    return "INFRA", f"returncode {r.returncode}; {first}; {detail}"


def main():
    baselines = list(dict.fromkeys(src for src, _, _, _ in MUTANTS))
    bad = 0
    for src in baselines:
        status, why = run_lean(src)
        print(f"{'PASS' if status == 'PASSED' else 'FAIL'} baseline {src}: {status}; {why}", flush=True)
        bad += status != "PASSED"
    if bad:
        print(f"FAIL: {bad} baselines failed; mutants not run")
        return 1
    rejected = 0
    for src, name, old, new in MUTANTS:
        text = open(src).read()
        if text.count(old) != 1:
            print(f"FAIL INFRA {src}: {name}; anchor not unique", flush=True)
            continue
        try:
            open(src, "w").write(text.replace(old, new))
            status, why = run_lean(src)
        finally:
            open(src, "w").write(text)
        status = "SURVIVED" if status == "PASSED" else status
        rejected += status == "REJECTED"
        print(("REJECTED " if status == "REJECTED" else f"FAIL {status} ") + f"{src}: {name}\n    {why}", flush=True)
    ok = rejected == len(MUTANTS)
    print(f"{'PASS' if ok else 'FAIL'}: {len(baselines)} baselines passed, {rejected}/{len(MUTANTS)} mutants REJECTED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
