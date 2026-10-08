#!/usr/bin/env python3
"""Targeted mutation checks for the trimmed marked-window bridge for MO 458571 Theorem 1.

Every unchanged module must compile; each deliberate corruption must produce a Lean
error. A timeout or missing dependency is a checker failure, not a rejected mutant.
All checks run serially, with a 120-second cap and nice priority 15.
"""
from pathlib import Path
import argparse
import subprocess
import tempfile

MUTANTS = [
    ('depth scale reversed', 'Enclosing/DepthRescale.lean', '(q.1, r * q.2)', '(q.1, -r * q.2)'),
    ('depth Jacobian reciprocal removed', 'Enclosing/DepthRescale.lean', '= ENNReal.ofReal r⁻¹ • volume := by', '= ENNReal.ofReal r • volume := by'),
    ('rescaled rectangle depth doubled', 'Enclosing/DepthRescale.lean', '= Icc a b ×ˢ Icc 0 (T / r) := by', '= Icc a b ×ˢ Icc 0 (2 * T / r) := by'),
    ('zero-mass conditional fallback zero', 'Poisson/ConditionalWindow.lean', 'if μ B = 0 then μ else', 'if μ B = 0 then 0 else'),
    ('window restriction count mass doubled', 'Poisson/ConditionalWindow.lean', '= μ B • windowLaw μ B := by', '= (2 * μ B) • windowLaw μ B := by'),
    ('conditional mark normalization doubled', 'Poisson/ConditionalWindow.lean', '= (Λ univ)⁻¹ • Λ := by', '= (2 * (Λ univ)⁻¹) • Λ := by'),
    ('canonical iid limiting rate doubled', 'Poisson/ConditionalWindow.lean', '(𝓝 ((law ((r : ℝ≥0∞) • ν)).real', '(𝓝 ((law ((2 * r : ℝ≥0∞) • ν)).real'),
    ('glued marker selects window complement', 'Poisson/FiniteWindows.lean', '(B i).piecewise (f i) g', '(B i)ᶜ.piecewise (f i) g'),
    ('local agreement changed to fallback', 'Poisson/FiniteWindows.lean', 'glueWindows l B f fallback x = f i x := by', 'glueWindows l B f fallback x = fallback x := by'),
    ('disjoint union law doubled', 'Poisson/FiniteWindows.lean', 'Measure.sum fun i => Measure.map (f i) (μ.restrict (B i)) := by', '2 • (Measure.sum fun i => Measure.map (f i) (μ.restrict (B i))) := by'),
    ('window measurability assumption removed', 'Poisson/WindowMeasurability.lean', '(hB : MeasurableSet B)', '(hB : True)'),
    ('mark measurability assumption removed', 'Poisson/WindowMeasurability.lean', '(hf : Measurable f)', '(hf : True)'),
    ('rectangle law positive area assumption weakened', 'Enclosing/SideMarkLaw.lean', '(hab : a < b) (hT : 0 < T)', '(hab : a ≤ b) (hT : 0 < T)'),
    ('restricted polygon density doubled', 'Enclosing/SideMarkLaw.lean', '(volume (polygonRegion (sidesOf v hm hv harea)))⁻¹ •\n        volume.restrict', '(2 * (volume (polygonRegion (sidesOf v hm hv harea)))⁻¹) •\n        volume.restrict'),
    ('left side gap margin removed', 'Enclosing/SideSeparation.lean', '(ha : aEnd v i < a)', '(ha : aEnd v i ≤ a)'),
    ('right side gap margin removed', 'Enclosing/SideSeparation.lean', '(hb : b < bEnd v i)', '(hb : b ≤ bEnd v i)'),
    ('strip labels shifted', 'Enclosing/BoundaryMarkLaw.lean', '(Measure.dirac i).prod (volume.restrict', '(Measure.dirac (i + 1)).prod (volume.restrict'),
    ('strip intensity mass doubled', 'Enclosing/BoundaryMarkLaw.lean', '= ∑ i, ENNReal.ofReal (b i - a i) * ENNReal.ofReal T := by', '= 2 * ∑ i, ENNReal.ofReal (b i - a i) * ENNReal.ofReal T := by'),
    ('conditional boundary law doubled', 'Enclosing/BoundaryMarkLaw.lean', '=\n        boundaryMarkLaw a b T := by', '=\n        2 • boundaryMarkLaw a b T := by'),
    ('scaled boundary count rate doubled', 'Enclosing/BoundaryLimit.lean', '= (trimmedIntensity a b T).real univ /', '= 2 * (trimmedIntensity a b T).real univ /'),
    ('varying-event Poisson intensity doubled', 'Enclosing/BoundaryLimit.lean', 'PoissonPP.law (ENNReal.ofReal A⁻¹ • trimmedIntensity a b T)', 'PoissonPP.law ((2 * ENNReal.ofReal A⁻¹) • trimmedIntensity a b T)'),
    ('fixed-event Poisson intensity doubled', 'Enclosing/BoundaryLimit.lean', 'PoissonPP.law (ENNReal.ofReal A⁻¹ • trimmedIntensity a b T)).real\n        {ω | F (PoissonPP.config ω.2)})) := by\n  apply polygon_trimmed_window_limit', 'PoissonPP.law ((2 * ENNReal.ofReal A⁻¹) • trimmedIntensity a b T)).real\n        {ω | F (PoissonPP.config ω.2)})) := by\n  apply polygon_trimmed_window_limit'),
]

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
    with tempfile.TemporaryDirectory(prefix='mo458571-boundary-') as tmp:
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
