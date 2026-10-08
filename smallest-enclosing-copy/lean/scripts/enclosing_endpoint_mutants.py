#!/usr/bin/env python3
"""Targeted mutation checks for endpoint removal and the full marked boundary limit for MO 458571 Theorem 1.

Every unchanged module must compile; each deliberate corruption must produce a Lean
error. A timeout or missing dependency is a checker failure, not a rejected mutant.
All checks run serially, with a 120-second cap and nice priority 15.
"""
from pathlib import Path
import argparse
import subprocess
import tempfile

MUTANTS = [('physical strip depth halved', 'Enclosing/EndpointGeometry.lean', '∈ Icc 0 d}', '∈ Icc 0 (d / 2)}'),
 ('next support slope reversed',
  'Enclosing/EndpointGeometry.lean',
  '0 < dot (sideTangent (nrm v i)) (nrm v (i + 1)) := by',
  'dot (sideTangent (nrm v i)) (nrm v (i + 1)) < 0 := by'),
 ('previous support slope reversed',
  'Enclosing/EndpointGeometry.lean',
  'dot (sideTangent (nrm v i)) (nrm v (i - 1)) < 0 := by',
  '0 < dot (sideTangent (nrm v i)) (nrm v (i - 1)) := by'),
 ('left endpoint excess removed',
  'Enclosing/EndpointGeometry.lean',
  'sideWindow K i (K.a i - C * d) (K.b i + C * d) d := by',
  'sideWindow K i (K.a i) (K.b i + C * d) d := by'),
 ('physical subset area denominator multiplied',
  'Enclosing/EndpointMass.lean',
  'volume.real S / (volume (polygonRegion',
  'volume.real S * (volume (polygonRegion'),
 ('endpoint remainder keeps trimmed interior',
  'Enclosing/EndpointMass.lean',
  'physicalSideStrip K i d \\ sideWindow',
  'physicalSideStrip K i d ∩ sideWindow'),
 ('single-side omission coefficient halved',
  'Enclosing/EndpointMass.lean',
  '2 * (δ + C * d) * d /',
  '(δ + C * d) * d /'),
 ('sample boundary depth multiplied by count',
  'Enclosing/EndpointSampling.lean',
  'omittedBoundary K δ (T / n)',
  'omittedBoundary K δ (T * n)'),
 ('corner correction dropped from iid bound',
  'Enclosing/EndpointSampling.lean',
  '2 * (m : ℝ) * δ * T + C * T * (T / n)',
  '2 * (m : ℝ) * δ * T'),
 ('protrusion hit limit changed to one',
  'Enclosing/EndpointSampling.lean',
  '(endpointHit K 0 T n)) atTop (𝓝 0) := by',
  '(endpointHit K 0 T n)) atTop (𝓝 1) := by'),
 ('exceptional-event probability error forced zero',
  'Poisson/EventComparison.lean',
  '|μ.real E - μ.real F| ≤ μ.real B := by',
  '|μ.real E - μ.real F| ≤ 0 := by'),
 ('iid union bound count halved',
  'Poisson/EventComparison.lean',
  '≤ (n : ℝ) * μ.real B := by',
  '≤ (n : ℝ) / 2 * μ.real B := by'),
 ('superposition empty probability exponent reversed',
  'Poisson/IntensityComparison.lean',
  'Real.exp (-(Ξ univ).toReal)',
  'Real.exp ((Ξ univ).toReal)'),
 ('added Poisson intensity error forced zero',
  'Poisson/IntensityComparison.lean',
  '1 - Real.exp (-(Ξ univ).toReal) := by',
  '0 := by'),
 ('added intensity mass error halved',
  'Poisson/IntensityComparison.lean',
  'Ξ.real univ := by',
  'Ξ.real univ / 2 := by'),
 ('physical side labels shifted',
  'Enclosing/PhysicalBoundary.lean',
  '(fun i x => (i, sideMark K i n x))',
  '(fun i x => (i + 1, sideMark K i n x))'),
 ('corner exclusion removed from mark agreement',
  'Enclosing/PhysicalBoundary.lean',
  '(hcorner : x ∉ cornerOverlap K (T / n))',
  '(hcorner : True)'),
 ('endpoint exclusion removed from configuration agreement',
  'Enclosing/PhysicalBoundary.lean',
  '(hmiss : x ∉ endpointHit K δ T n)',
  '(hmiss : True)'),
 ('trim region selects depth instead of position',
  'Enclosing/BoundaryIntensityComparison.lean',
  '{p | p.2.1 ∈ Icc',
  '{p | p.2.2 ∈ Icc'),
 ('deleted limiting intensity mass halved',
  'Enclosing/BoundaryIntensityComparison.lean',
  '2 * (m : ℝ) * δ * T / A := by',
  '(m : ℝ) * δ * T / A := by'),
 ('full boundary limit intensity doubled',
  'Enclosing/FullBoundaryLimit.lean',
  'PoissonPP.law (ENNReal.ofReal A⁻¹ • Λ K T)',
  'PoissonPP.law ((2 * ENNReal.ofReal A⁻¹) • Λ K T)'),
 ('full boundary limit cutoff doubled',
  'Enclosing/FullBoundaryLimit.lean',
  'PoissonPP.law (ENNReal.ofReal A⁻¹ • Λ K T)',
  'PoissonPP.law (ENNReal.ofReal A⁻¹ • Λ K (2 * T))')]

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
    with tempfile.TemporaryDirectory(prefix='mo458571-endpoints-') as tmp:
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
