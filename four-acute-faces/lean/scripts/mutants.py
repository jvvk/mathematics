#!/usr/bin/env python3
"""Mutation tests for LeanProofs/AcuteTetra (four acute faces, MO 498296): every wrong variant must FAIL.

Each mutant copies one file to AcuteTetra/Mut.lean with the namespace renamed to AcuteTetraMut (so it cannot
clash with the real modules it imports), applies textual changes, and compiles it with `lake env lean`
(single process, background QoS). Unmutated renamed copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "AcuteTetra"
MUT = D / "Mut.lean"
FILES = ["Comb.lean", "Facts.lean", "Geom.lean", "Main.lean", "Count.lean", "Cone.lean", "Sphere.lean",
         "Pair.lean", "Prob.lean"]

MUTANTS = [('count constant 8 -> 9 (finite core)', 'Comb.lean', [('    8 + (allSigns.map', '    9 + (allSigns.map')]), ('drop joining constraint (finite core)', 'Comb.lean', [('  (shortList c).all fun e => (shortList c).all fun f => !disjointE e f || joined c e f', '  true')]), ('drop no-four-star constraint', 'Comb.lean', [('  allSigns.all (fun σ => !((List.finRange 4).all fun l => c l == some (incP σ l))) &&', '  true &&')]), ('joining identity without joiner h', 'Facts.lean', [('gramEq (outer (cE g) (cE g) + outer (cE h) (cE h))', 'gramEq (outer (cE g) (cE g))')]), ('star identity 4 -> 3', 'Facts.lean', [('(4 : ℤ) • unitM) = true', '(3 : ℤ) • unitM) = true')]), ('dimension 3 -> 4 in exists_short', 'Main.lean', [('theorem exists_short [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 3)', 'theorem exists_short [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 4)')]), ('main count 8 -> 9', 'Main.lean', [('        8 + (allSigns.map fun σ => (deg c σ).choose 2).sum := by', '        9 + (allSigns.map fun σ => (deg c σ).choose 2).sum := by')]), ('acute angle sign flipped', 'Geom.lean', [('  ∀ l : Fin 4, ∀ k : Fin 3, 0 < inner', '  ∀ l : Fin 4, ∀ k : Fin 3, inner'), ('    (P A σ (face l (k + 2)) - P A σ (face l k))', '    (P A σ (face l (k + 2)) - P A σ (face l k)) < 0')]), ('N + C = 4 -> 5 (Lemma 4, finite)', 'Count.lean', [('    (evenSigns.filter fun σ => 1 ≤ deg c σ && deg c σ ≤ 2).length == 4', '    (evenSigns.filter fun σ => 1 ≤ deg c σ && deg c σ ≤ 2).length == 5')]), ('cone integral (1 - t) -> (1 - t/2)', 'Cone.lean', [('    ∫ z in (0 : ℝ)..1, area t z = 2 * π / 3 * (1 - t) := by', '    ∫ z in (0 : ℝ)..1, area t z = 2 * π / 3 * (1 - t / 2) := by')]), ('Archimedes (1+t)/2 -> (1+t)/3', 'Sphere.lean', [('    unif {x | inner ℝ x u ≤ t} = ENNReal.ofReal ((1 + t) / 2) := by', '    unif {x | inner ℝ x u ≤ t} = ENNReal.ofReal ((1 + t) / 3) := by')]), ('alpha 1/6 -> 1/5', 'Pair.lean', [('theorem alpha_eq : ∫⁻ p, q p.1 p.2 ∂(unif.prod unif) = ENNReal.ofReal (1 / 6) := by', 'theorem alpha_eq : ∫⁻ p, q p.1 p.2 ∂(unif.prod unif) = ENNReal.ofReal (1 / 5) := by')]), ('gamma 1/24 -> 1/20', 'Pair.lean', [('theorem gamma_eq : ∫⁻ p, q p.1 p.2 ^ 2 ∂(unif.prod unif) = ENNReal.ofReal (1 / 24) := by', 'theorem gamma_eq : ∫⁻ p, q p.1 p.2 ^ 2 ∂(unif.prod unif) = ENNReal.ofReal (1 / 20) := by')]), ('integrated count 8 -> 9', 'Prob.lean', [('theorem count_integrated : 16 * PP (Ac allTrue) + 16 * PP (Rs allTrue) = 8 := by', 'theorem count_integrated : 16 * PP (Ac allTrue) + 16 * PP (Rs allTrue) = 9 := by')]), ('final answer 1/12 -> 1/13', 'Prob.lean', [('theorem prob_all_faces_acute : PP {A | AllFacesAcute A} = ENNReal.ofReal (1 / 12) := by', 'theorem prob_all_faces_acute : PP {A | AllFacesAcute A} = ENNReal.ofReal (1 / 13) := by')]), ('drop no-four-star (pattern identity)', 'Prob.lean', [('lemma pattern_identity : ∀ f : Fin 4 → Bool, cnt f ≤ 3 →', 'lemma pattern_identity : ∀ f : Fin 4 → Bool, cnt f ≤ 4 →')])]


def renamed(f: str) -> str:
    src = (D / f).read_text()
    opn = "" if f in ("Comb.lean", "Cone.lean") else "\nopen AcuteTetra"
    lines = []
    for ln in src.split("\n"):
        if ln == "namespace AcuteTetra":
            ln = "namespace AcuteTetraMut" + opn
        elif ln == "end AcuteTetra":
            ln = "end AcuteTetraMut"
        lines.append(ln)
    return "\n".join(lines)


def check(text: str) -> bool:
    MUT.write_text(text)
    p = subprocess.Popen(["taskpolicy", "-c", "background", "lake", "env", "lean", str(MUT)], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        out, _ = p.communicate(timeout=1800)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        p.communicate()
        print("  (timed out: counted as not compiling)", flush=True)
        return False
    return p.returncode == 0 and "error" not in out


def main() -> int:
    bad = 0
    sel = [m for m in MUTANTS if not sys.argv[1:] or any(a in m[1] for a in sys.argv[1:])]
    try:
        for f in [f for f in FILES if any(m[1] == f for m in sel)]:
            ok = check(renamed(f))
            print(f"baseline {'ok' if ok else 'FAILS'}: {f}", flush=True)
            bad += not ok
        for name, f, subs in sel:
            src = renamed(f)
            new = src
            for old, rep in subs:
                if new.count(old) != 1:
                    new = None
                    break
                new = new.replace(old, rep)
            if new is None or new == src:
                print(f"MUTATION DID NOT APPLY: {name}", flush=True)
                bad += 1
                continue
            if check(new):
                print(f"MUTANT SURVIVED: {name}", flush=True)
                bad += 1
            else:
                print(f"rejected: {name}", flush=True)
    finally:
        MUT.unlink(missing_ok=True)
    print(f"{len(sel)} mutants, {bad} problems")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
