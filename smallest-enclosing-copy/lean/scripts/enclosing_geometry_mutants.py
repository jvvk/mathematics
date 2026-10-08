#!/usr/bin/env python3
"""Targeted mutation checks for the physical-polygon geometry for MO 458571 Theorem 1.

Every unchanged module must compile; each deliberate corruption must produce a Lean
error. A timeout or missing dependency is a checker failure, not a rejected mutant.
All checks run serially, with a 120-second cap and nice priority 15.
"""
from pathlib import Path
import argparse
import subprocess
import tempfile

MUTANTS = [
    ('outward depth instead of inward', 'SideChart.lean', '(h - q.2)', '(h + q.2)'),
    ('side chart reverses position', 'SideChart.lean', '- q.1 * u.2', '+ q.1 * u.2'),
    ('rectangle area doubled', 'SideChart.lean', 'ENNReal.ofReal (b - a) * ENNReal.ofReal d := by', '2 * ENNReal.ofReal (b - a) * ENNReal.ofReal d := by'),
    ('support gap sum halved', 'PolygonRegion.lean', '* (K.h i - dot x (K.u i)) = 2 := by', '* (K.h i - dot x (K.u i)) = 1 := by'),
    ('support gap bound halved', 'PolygonRegion.lean', '≤ 2 / (K.b i - K.a i) := by', '≤ 1 / (K.b i - K.a i) := by'),
    ('left trim permits vertex', 'PolygonWindows.lean', '(ha : aEnd v i < a)', '(ha : aEnd v i ≤ a)'),
    ('right trim permits vertex', 'PolygonWindows.lean', '(hb : b < bEnd v i)', '(hb : b ≤ bEnd v i)'),
    ('side window rectangle area doubled', 'PolygonWindows.lean', '= ENNReal.ofReal (b - a) * ENNReal.ofReal d :=', '= 2 * ENNReal.ofReal (b - a) * ENNReal.ofReal d :='),
    ('normalized window probability doubled', 'PolygonSampling.lean', '(b - a) * d / (volume (polygonRegion (sidesOf v hm hv harea))).toReal := by', '2 * (b - a) * d / (volume (polygonRegion (sidesOf v hm hv harea))).toReal := by'),
    ('scaled window mass doubled', 'PolygonSampling.lean', '(b - a) * y / (volume (polygonRegion K)).toReal := by', '2 * (b - a) * y / (volume (polygonRegion K)).toReal := by'),
    ('witness void exponent doubled', 'PolygonSampling.lean', 'Real.exp (-((b - a) * y /', 'Real.exp (-2 * ((b - a) * y /'),
    ('two-depth Jacobian doubled', 'PolygonOverlap.lean', '= ENNReal.ofReal |cross u w|⁻¹ • volume := by', '= 2 * ENNReal.ofReal |cross u w|⁻¹ • volume := by'),
    ('two-strip area halved', 'PolygonOverlap.lean', 'ENNReal.ofReal |cross u w|⁻¹ * (ENNReal.ofReal d * ENNReal.ofReal e) := by', 'ENNReal.ofReal |cross u w|⁻¹ / 2 * (ENNReal.ofReal d * ENNReal.ofReal e) := by'),
    ('opposite strips allow excessive depth', 'PolygonOverlap.lean', '(hd : 2 * d < K.h i + K.h j)', '(hd : d < K.h i + K.h j)'),
    ('overlap scaled mass limit one', 'PolygonOverlap.lean', '(sideOverlap K i j (y / n))) atTop (𝓝 0) := by', '(sideOverlap K i j (y / n))) atTop (𝓝 1) := by'),
    ('corner hit probability limit one', 'PolygonOverlap.lean', '{x | ∃ j, x j ∈ cornerOverlap K (y / n)}) atTop (𝓝 0) := by', '{x | ∃ j, x j ∈ cornerOverlap K (y / n)}) atTop (𝓝 1) := by'),
    ('witness exponential sum limit one', 'PolygonWitnesses.lean', '(fun y : ℝ => ∑ t, Real.exp (-((b t - a t) * y / A))) atTop (𝓝 0)', '(fun y : ℝ => ∑ t, Real.exp (-((b t - a t) * y / A))) atTop (𝓝 1)'),
    ('witness cutoff depth n squared', 'PolygonWitnesses.lean', '(y / n)}', '(y / (n * n))}'),
    ('witness failure negative probability bound', 'PolygonWitnesses.lean', '(witnessFailure K i a b n y) < ε := by', '(witnessFailure K i a b n y) < -ε := by'),
]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--project', type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument('--source-root', type=Path)
    ap.add_argument('--imports', type=Path)
    ap.add_argument('--only', nargs='+', help='Check just the named Lean source files')
    args = ap.parse_args()
    mutants = [m for m in MUTANTS if not args.only or m[1] in args.only]
    sources = (args.source_root or args.project) / 'EnclosingCopy' / 'Enclosing'
    problems = 0
    with tempfile.TemporaryDirectory(prefix='mo458571-geometry-') as tmp:
        path = Path(tmp) / 'Mut.lean'
        def check(source):
            path.write_text(source)
            cmd = ['timeout', '120', 'nice', '-n', '15', 'lake', 'env']
            if args.imports:
                cmd += ['sh', '-c', 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean "$2"',
                        'geometry-check', str(args.imports), str(path)]
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
