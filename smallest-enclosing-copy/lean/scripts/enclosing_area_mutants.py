#!/usr/bin/env python3
"""Targeted mutation checks for physical area identification for MO 458571 Theorem 1.

Every unchanged module must compile; each deliberate corruption must produce a Lean
error. A timeout or missing dependency is a checker failure, not a rejected mutant.
All checks run serially, with a 120-second cap and nice priority 15.
"""
from pathlib import Path
import argparse
import subprocess
import tempfile

MUTANTS = [('physical strip correction sign reversed',
  'Enclosing/PhysicalStripMass.lean',
  '((K.b i - K.a i) + 2 * C * d) * d /',
  '((K.b i - K.a i) - 2 * C * d) * d /'),
 ('single strip limiting mass doubled',
  'Enclosing/PhysicalStripMass.lean',
  '(𝓝 ((K.b i - K.a i) * y /',
  '(𝓝 (2 * (K.b i - K.a i) * y /'),
 ('single strip limiting volume doubled',
  'Enclosing/PhysicalStripMass.lean',
  'atTop (𝓝 ((K.b i - K.a i) * y)) := by',
  'atTop (𝓝 (2 * (K.b i - K.a i) * y)) := by'),
 ('union corner allowance halved',
  'Enclosing/WeightedBoundaryMass.lean',
  '(Fintype.card ι : ℝ) * μ.real C',
  '(Fintype.card ι : ℝ) / 2 * μ.real C'),
 ('weighted side depths doubled',
  'Enclosing/WeightedBoundaryMass.lean',
  'physicalSideStrip K i (y i / n)',
  'physicalSideStrip K i (2 * y i / n)'),
 ('weighted union limiting area halved',
  'Enclosing/WeightedBoundaryMass.lean',
  'atTop (𝓝 (∑ i, (K.b i - K.a i) * y i)) := by',
  'atTop (𝓝 ((∑ i, (K.b i - K.a i) * y i) / 2)) := by'),
 ('contraction expands instead',
  'Enclosing/HomothetyGeometry.lean',
  'w + (1 - t) • (x - w)',
  'w + (1 + t) • (x - w)'),
 ('contracted support gap factor dropped',
  'Enclosing/HomothetyGeometry.lean',
  't * (K.h i - dot w (K.u i)) ≤',
  '(K.h i - dot w (K.u i)) ≤'),
 ('area scales linearly instead of quadratically',
  'Enclosing/HomothetyGeometry.lean',
  'ENNReal.ofReal ((1 - t) ^ 2) *',
  'ENNReal.ofReal (1 - t) *'),
 ('support line given positive area',
  'Enclosing/HomothetyGeometry.lean',
  'volume {x | K.h i - dot x (K.u i) = d} = 0 := by',
  'volume {x | K.h i - dot x (K.u i) = d} = 1 := by'),
 ('physical polygon area changed to two',
  'Enclosing/PolygonArea.lean',
  'volume.real (polygonRegion (sidesOf v hm hv harea)) = 1 := by',
  'volume.real (polygonRegion (sidesOf v hm hv harea)) = 2 := by'),
 ('uniform sample restriction doubled',
  'Enclosing/PolygonArea.lean',
  'polygonSample v hm hv harea = volume.restrict',
  'polygonSample v hm hv harea = 2 • volume.restrict'),
 ('normalized boundary intensity doubled',
  'Enclosing/PolygonArea.lean',
  'PoissonPP.law (Λ K T)).real',
  'PoissonPP.law (2 • Λ K T)).real')]

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
    with tempfile.TemporaryDirectory(prefix='mo458571-area-') as tmp:
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
