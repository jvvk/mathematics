#!/usr/bin/env python3
"""Targeted mutation checks for exact finite similarity geometry and stability for MO 458571 Theorem 1.

Every unchanged module must compile; each deliberate corruption must produce a Lean
error. A timeout or missing dependency is a checker failure, not a rejected mutant.
All checks run serially, with a 120-second cap and nice priority 15.
"""
from pathlib import Path
import argparse
import subprocess
import tempfile

MUTANTS = [('tangent rotation orientation reversed', 'Enclosing/TangentSimilarity.lean', '(x.1 - t * x.2, x.2 + t * x.1)', '(x.1 + t * x.2, x.2 - t * x.1)'), ('physical scale numerator doubled', 'Enclosing/TangentSimilarity.lean', '(1 + q * z.1) / sqrt', '(1 + 2 * q * z.1) / sqrt'), ('containment mark depth doubled', 'Enclosing/TangentSimilarity.lean', '(K.h i - dot x (K.u i)) / q)', '2 * (K.h i - dot x (K.u i)) / q)'), ('finite fit correction sign reversed', 'Enclosing/TangentFit.lean', 'z.2.2 * s - Hs K z i + q *', 'z.2.2 * s - Hs K z i - q *'), ('endpoint fit tests only first endpoint', 'Enclosing/TangentFit.lean', '0 ≤ tangentFitSlack K q z i (K.b i)', '0 ≤ tangentFitSlack K q z i (K.a i)'), ('radius support minimum becomes maximum', 'Enclosing/TangentFit.lean', 'K.h i - min (t * K.a i) (t * K.b i)', 'K.h i - max (t * K.a i) (t * K.b i)'), ('scale error bound halved', 'Enclosing/TangentObjective.lean', 'q * R ^ 2 * (1 + q * R) / 2 := by', 'q * R ^ 2 * (1 + q * R) / 4 := by'), ('sqrt Lipschitz error halved', 'Enclosing/TangentObjective.lean', 'q ^ 2 * R * |t - u| := by', 'q ^ 2 * R * |t - u| / 2 := by'), ('strict scale comparison reversed', 'Enclosing/TangentObjective.lean', 'tangentScale q zs < tangentScale q z := by', 'tangentScale q z < tangentScale q zs := by'), ('physical optimal face shifted', 'Enclosing/TangentObjective.lean', '↔ z.1 = zs.1) := by', '↔ z.1 = zs.1 + 1) := by'), ('certificate coordinate allowance halved', 'Enclosing/CertificateSharpness.lean', '(∑ i, |a i| / l i) * ∑ i, l i * g i', '(∑ i, |a i| / l i) / 2 * ∑ i, l i * g i'), ('inverse recovers wrong coordinate', 'Enclosing/CertificateSharpness.lean', '(vertexMatrix K x)⁻¹ c r *', '(vertexMatrix K x)⁻¹ 0 r *'), ('same-side tilt slope reversed', 'Enclosing/CertificateSharpness.lean', '((x 1).2.1 - (x 0).2.1) := by', '((x 0).2.1 - (x 1).2.1) := by'), ('vertex physical optimizer shifted', 'Enclosing/CertificateSharpness.lean', 'z = vertexCopy K x) := by', 'z = (0, (0, 0), 0)) := by'), ('nonfitting compact face made fitting', 'Enclosing/TangentEventStability.lean', '∀ z ∈ S, ¬ TangentFits K q z := by', '∀ z ∈ S, TangentFits K q z := by'), ('fit event inequality reversed', 'Enclosing/TangentEventStability.lean', 'tangentScale (1 / n) z ≤ tangentScale (1 / n) y', 'tangentScale (1 / n) y ≤ tangentScale (1 / n) z'), ('weighted tilt gap allowance halved', 'Enclosing/FiniteCoercivity.lean', '|z.2.2| * Qs K ≤ 4 * z.1 +', '|z.2.2| * Qs K ≤ 2 * z.1 +'), ('physical epsilon bound halved', 'Enclosing/FiniteCoercivity.lean', 'z.1 ≤ q * z.2.2 ^ 2 / 2 := by', 'z.1 ≤ q * z.2.2 ^ 2 / 4 := by'), ('witness depth tilt bound halved', 'Enclosing/FiniteCoercivity.lean', '|z.2.2| ≤ 8 * M * per K / Qs K := by', '|z.2.2| ≤ 4 * M * per K / Qs K := by'), ('translation balance upper sign reversed', 'Enclosing/FiniteCoercivity.lean', '|dot C (K.u i)| ≤ A + A * per K / Ls K i', '|dot C (K.u i)| ≤ A - A * per K / Ls K i'), ('deep constraint declared violating', 'Enclosing/BoundaryFeasible.lean', '¬ violates K z (tangentPointMark K (1 / n) i x) := by', 'violates K z (tangentPointMark K (1 / n) i x) := by'), ('boundary containment reverses feasibility', 'Enclosing/BoundaryFeasible.lean', '      Feasible K ((PoissonPP.inWindow', '      ¬ Feasible K ((PoissonPP.inWindow'), ('box first coordinate radius doubled', 'Enclosing/BoundaryFeasible.lean', '{z | |z.1| ≤ R ∧', '{z | |z.1| ≤ 2 * R ∧')]

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
    with tempfile.TemporaryDirectory(prefix='mo458571-tangent-') as tmp:
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
