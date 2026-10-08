#!/usr/bin/env python3
"""Targeted mutation checks for the fixed-window part of MO 458571 Theorem 1.

Every unchanged module must compile; each deliberate corruption must produce a Lean
error. A timeout or missing dependency is a checker failure, not a rejected mutant.
All checks run serially, with a 120-second cap and nice priority 15.
"""
from pathlib import Path
import argparse
import subprocess
import tempfile

MUTANTS = [
    ('L1 limit zero -> one', 'CountConvergence.lean',
     "Tendsto (fun n => ∑' k, |w n k - v k|) atTop (𝓝 0)",
     "Tendsto (fun n => ∑' k, |w n k - v k|) atTop (𝓝 1)"),
    ('conditional average doubled', 'CountConvergence.lean',
     "atTop (𝓝 (∑' k, v k * qlim k)) := by",
     "atTop (𝓝 (2 * ∑' k, v k * qlim k)) := by"),
    ('binomial mean doubled', 'CountConvergence.lean',
     "(fun n : ℕ => (n : ℝ) * (p n : ℝ))",
     "(fun n : ℕ => (2 * n : ℝ) * (p n : ℝ))"),
    ('count masses shifted', 'MarkedWindow.lean',
     'Measure.sum fun k : ℕ => ρ {k} •',
     'Measure.sum fun k : ℕ => ρ {k + 1} •'),
    ('product scaling exponent k+1', 'MarkedWindow.lean',
     '= c ^ k • (Measure.pi fun _ : Fin k => ν) := by',
     '= c ^ (k + 1) • (Measure.pi fun _ : Fin k => ν) := by'),
    ('Poisson rate doubled', 'MarkedWindow.lean',
     '= law ((r : ℝ≥0∞) • ν) := by',
     '= law ((2 * r : ℝ≥0∞) • ν) := by'),
    ('retained window complemented', 'IIDWindow.lean',
     'exact c.filter (· ∈ B)', 'exact c.filter (· ∉ B)'),
    ('iid count n+1', 'IIDWindow.lean',
     '(ProbabilityTheory.binomial n p) {k} *',
     '(ProbabilityTheory.binomial (n + 1) p) {k} *'),
    ('event stability negated', 'WindowLimit.lean',
     '∀ᶠ n in atTop, E n (config x) ↔ F (config x))',
     '∀ᶠ n in atTop, E n (config x) ↔ ¬ F (config x))'),
    ('mapped iid limiting rate doubled', 'WindowLimit.lean',
     '(𝓝 ((law ((r : ℝ≥0∞) • ν)).real {ω | F (config ω.2)}))',
     '(𝓝 ((law ((2 * r : ℝ≥0∞) • ν)).real {ω | F (config ω.2)}))'),
    ('void exponent n+1', 'IIDBounds.lean',
     '= (1 - μ B) ^ n := by', '= (1 - μ B) ^ (n + 1) := by'),
    ('void limiting exponent doubled', 'IIDBounds.lean',
     '(Real.exp (-(r : ℝ)))', '(Real.exp (-2 * (r : ℝ)))'),
    ('union bound divided by two', 'IIDBounds.lean',
     '≤ (n : ℝ≥0∞) * μ B := by', '≤ (n : ℝ≥0∞) / 2 * μ B := by'),
]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--project', type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument('--source-root', type=Path)
    ap.add_argument('--imports', type=Path)
    args = ap.parse_args()
    sources = (args.source_root or args.project) / 'EnclosingCopy' / 'Poisson'
    problems = 0
    with tempfile.TemporaryDirectory(prefix='mo458571-window-') as tmp:
        path = Path(tmp) / 'Mut.lean'
        def check(source):
            path.write_text(source)
            cmd = ['timeout', '120', 'nice', '-n', '15', 'lake', 'env']
            if args.imports:
                cmd += ['sh', '-c', 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean "$2"',
                        'window-check', str(args.imports), str(path)]
            else:
                cmd += ['lean', str(path)]
            result = subprocess.run(cmd, cwd=args.project, capture_output=True, text=True,
                                    timeout=125)
            output = result.stdout + result.stderr
            if result.returncode in (124, 137) or 'object file' in output or 'unknown module prefix' in output:
                raise RuntimeError(output)
            return result.returncode == 0, output
        for file in sorted({m[1] for m in MUTANTS}):
            ok, output = check((sources / file).read_text())
            print(f"baseline {'ok' if ok else 'FAILED'}: {file}", flush=True)
            if not ok:
                print(output)
                problems += 1
        for name, file, old, new in MUTANTS:
            source = (sources / file).read_text()
            # A shared formula may occur in multiple theorem statements: change the first only.
            if old not in source:
                print(f'mutation did not apply: {name}', flush=True)
                problems += 1
                continue
            ok, output = check(source.replace(old, new, 1))
            rejected = not ok and ('error:' in output or 'error(' in output)
            print(f"{'rejected' if rejected else 'FAILED'}: {name}", flush=True)
            if not rejected:
                print(output)
                problems += 1
    print(f'{len(MUTANTS)} mutations; {problems} problems', flush=True)
    return int(problems != 0)

if __name__ == '__main__':
    raise SystemExit(main())
