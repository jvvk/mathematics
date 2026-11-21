"""Mutation harness for LeanProofs/SpectreCover: every mutant (a false statement or corrupted
certificate) must be rejected. Run from lean/ after `lake build LeanProofs`.

An unchanged copy of every target file must compile first (control). A mutant counts as rejected only when
`lake env lean` exits 1 with an elaboration error located in the mutated copy; a timeout, a signal, a
resource limit (heartbeats, recursion) or a parse error only is INCONCLUSIVE, and fails the suite."""
import os, re, subprocess, sys, tempfile

D = "LeanProofs/SpectreCover/"
MUTANTS = [
    (D + "Main.lean", "eleven-fold", "{p : Fin 54 × (ℤ × ℤ) | z ∈ tile p}.ncard = 12 := by",
     "{p : Fin 54 × (ℤ × ℤ) | z ∈ tile p}.ncard = 11 := by"),
    (D + "Main.lean", "triangle count 13", "theorem cnt_ae_twelve : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), cnt V vR wR z = 12",
     "theorem cnt_ae_twelve : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), cnt V vR wR z = 13"),
    (D + "Data.lean", "one placement moved", "![(0,-2,5),(0,-1,5)", "![(0,-2,6),(0,-1,5)"),
    (D + "Data.lean", "one placement rotated", "(1,-8,-10),(2,-2,-1)", "(3,-8,-10),(2,-2,-1)"),
    (D + "Data.lean", "Spectre vertex moved", "(3, 1, 0, 1), (3, 0, 0, 2)", "(3, 1, 0, 1), (3, 0, 1, 2)"),
    (D + "Data.lean", "triangulation changed", "![13, 9, 10], ![13, 10, 11]", "![13, 9, 10], ![13, 9, 11]"),
    (D + "Data.lean", "curved records: one fewer", "(curvedRecords 0).length = 378", "(curvedRecords 0).length = 377"),
    (D + "Main.lean", "total area off", "(1296, 1296) := by", "(1296, 1297) := by"),
    (D + "Concrete.lean", "covolume off", "rw [show (orientZ 0 vZ wZ) = (54, 54) by decide] at h",
     "rw [show (orientZ 0 vZ wZ) = (54, 55) by decide] at h"),
    (D + "Count.lean", "triangle area / 3",
     "volume (closedTri A B C) = ENNReal.ofReal (orient A B C / 2) := by",
     "volume (closedTri A B C) = ENNReal.ofReal (orient A B C / 3) := by"),
    (D + "Shadow.lean", "shadow sign dropped", "    (if z ∈ closedTri A B C then 1 else 0 : ℤ) = shadow A B z + shadow B C z + shadow C A z := by\n  have hD2",
     "    (if z ∈ closedTri A B C then 1 else 0 : ℤ) = shadow A B z + shadow B C z - shadow C A z := by\n  have hD2"),
    (D + "Cover.lean", "vertical move off by one", "    cnt V v w (x, y₁) = cnt V v w (x, y₂) := by",
     "    cnt V v w (x, y₁) = cnt V v w (x, y₂) + 1 := by"),
]

RESOURCE = re.compile(r"maximum number of heartbeats|maximum recursion depth|deep recursion|stack overflow|out of memory", re.I)
PARSE = re.compile(r"(unexpected|expected) ")
tmpdir = tempfile.mkdtemp(dir=os.environ.get("TMPDIR"))
path = os.path.join(tmpdir, "Mutant.lean")


def run(text: str) -> str:
    open(path, "w").write(text)
    try:
        r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True, timeout=1500)
    except subprocess.TimeoutExpired:
        return "INCONCLUSIVE (timeout)"
    out = r.stdout + r.stderr
    errs = re.findall(re.escape(path) + r":\d+:\d+: error: ?(.*)", out)
    if r.returncode == 0 and not errs:
        return "COMPILES"
    if RESOURCE.search(out):
        return f"INCONCLUSIVE (exit {r.returncode}, resource limit)"
    if errs and all(PARSE.match(e) for e in errs):
        return f"INCONCLUSIVE (exit {r.returncode}, parse error only)"
    if r.returncode == 1 and errs:
        return "REJECTED"
    return f"INCONCLUSIVE (exit {r.returncode}, no error located in the mutant)"


ok = True
for SRC in sorted({m[0] for m in MUTANTS}):
    v = run(open(SRC).read())
    print(f"control (unchanged {SRC}): {v}", flush=True)
    ok &= v == "COMPILES"
if not ok:
    os.remove(path); os.rmdir(tmpdir)
    sys.exit("CONTROL FAILED: an unchanged target does not compile; mutants not run")
killed = 0
for SRC, name, old, new in MUTANTS:
    src = open(SRC).read()
    assert src.count(old) == 1, f"pattern not unique: {name}"
    v = run(src.replace(old, new))
    killed += v == "REJECTED"
    print(("killed  " if v == "REJECTED" else v + " "), name, flush=True)
os.remove(path); os.rmdir(tmpdir)
print(f"{killed}/{len(MUTANTS)} mutants killed")
sys.exit(0 if killed == len(MUTANTS) else 1)
