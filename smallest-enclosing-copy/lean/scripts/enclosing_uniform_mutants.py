#!/usr/bin/env python3
"""Targeted mutation checks for uniform and varying full boundary event convergence for MO 458571 Theorem 1.

Every unchanged module must compile; each deliberate corruption must produce a Lean
error. A timeout or missing dependency is a checker failure, not a rejected mutant.
All checks run serially, with a 120-second cap and nice priority 15.
"""
from pathlib import Path
import argparse
import subprocess
import tempfile

MUTANTS = [('count mixture error halved', 'Poisson/FixedMarkComparison.lean', "∑' k : ℕ, |ρ.real {k} - σ.real {k}|", "(∑' k : ℕ, |ρ.real {k} - σ.real {k}|) / 2"), ('iid count size increased', 'Poisson/FixedMarkComparison.lean', 'countMix (ProbabilityTheory.binomial n\n', 'countMix (ProbabilityTheory.binomial (n + 1)\n'), ('physical rate doubled', 'Poisson/FixedMarkComparison.lean', '(law ((r : ℝ≥0∞) • ν)).real', '(law ((2 * r : ℝ≥0∞) • ν)).real'), ('ae limit shifted', 'Poisson/EventConvergence.lean', 'atTop (𝓝 (μ.real {x | F x})) := by', 'atTop (𝓝 (μ.real {x | F x} + 1)) := by'), ('ae indicators stabilize to complement', 'Poisson/EventConvergence.lean', 'E n x ↔ F x) :', 'E n x ↔ ¬ F x) :'), ('physical omission allowance deleted', 'Enclosing/UniformBoundary.lean', '(Measure.pi fun _ : Fin n => polygonSample v hm hv harea).real (endpointHit K δ T n) +', '0 +'), ('trimmed target intensity doubled', 'Enclosing/UniformBoundary.lean', 'PoissonPP.law (ENNReal.ofReal A⁻¹ • trimmedIntensity a b T)', 'PoissonPP.law (2 • ENNReal.ofReal A⁻¹ • trimmedIntensity a b T)'), ('full target intensity doubled', 'Enclosing/UniformBoundary.lean', 'PoissonPP.law (ENNReal.ofReal A⁻¹ • Λ K T)', 'PoissonPP.law (2 • ENNReal.ofReal A⁻¹ • Λ K T)'), ('normalized target intensity doubled', 'Enclosing/UniformBoundary.lean', '(PoissonPP.law (Λ K T)).real', '(PoissonPP.law (2 • Λ K T)).real'), ('varying limit intensity doubled', 'Enclosing/VaryingBoundaryLimit.lean', '(PoissonPP.law (Λ K T)).real', '(PoissonPP.law (2 • Λ K T)).real'), ('varying events stabilize to complement', 'Enclosing/VaryingBoundaryLimit.lean', '↔ F (PoissonPP.config ω.2)) :', '↔ ¬ F (PoissonPP.config ω.2)) :')]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--project', type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument('--source-root', type=Path)
    ap.add_argument('--imports', type=Path)
    ap.add_argument('--only', nargs='+', help='Check just the named Lean source files')
    args = ap.parse_args()
    mutants = [m for m in MUTANTS if not args.only or m[1] in args.only]
    sources = (args.source_root or args.project) / 'EnclosingCopy'
    problems = 0
    with tempfile.TemporaryDirectory(prefix='mo458571-uniform-') as tmp:
        path = Path(tmp) / 'Mut.lean'
        def check(source):
            path.write_text(source)
            cmd = ['timeout', '120', 'nice', '-n', '15', 'lake', 'env']
            if args.imports:
                cmd += ['sh', '-c', 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean "$2"',
                        'boundary-check', str(args.imports), str(path)]
            else:
                cmd += ['lean', str(path)]
            result = subprocess.run(cmd, cwd=args.project, capture_output=True, text=True,
                                    timeout=125)
            output = result.stdout + result.stderr
            if result.returncode in (124, 137) or 'object file' in output or 'unknown module prefix' in output:
                raise RuntimeError(output)
            return result.returncode == 0, output
        for file in sorted({m[1] for m in mutants}):
            ok, output = check((sources / file).read_text())
            print(f"baseline {'ok' if ok else 'FAILED'}: {file}", flush=True)
            if not ok:
                print(output)
                problems += 1
        for name, file, old, new in mutants:
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
    print(f'{len(mutants)} mutations; {problems} problems', flush=True)
    return int(problems != 0)

if __name__ == '__main__':
    raise SystemExit(main())
