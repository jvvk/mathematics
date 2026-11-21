"""Mutation harness for LeanProofs/SpectreCover: every mutant (a false statement or corrupted
certificate) must be rejected. Run from lean/ after `lake build LeanProofs`.

An unchanged copy of every target file must compile first (control). A mutant counts as rejected only when
`lake env lean` exits 1 with an elaboration error located in the mutated copy; a timeout, a signal, a
resource limit (heartbeats, recursion) or a parse error only is INCONCLUSIVE, and fails the suite."""
import os, pathlib, re, subprocess, sys, tempfile

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
INFRA = re.compile(r"unknown module|unknown package|unknown namespace|could not resolve|object file|no such file|failed to load|import", re.I)
PARSE = re.compile(r"(unexpected|expected) ")
LOGDIR = pathlib.Path(__file__).resolve().parent / "mutants-output"


def classify(code, out: str, fname: str, mline: int, tag: str) -> str:
    """COMPILES; REJECTED (exit 1, an elaboration error in `fname` at or after the mutated line `mline`, and no
    parse, import or resource error); otherwise INCONCLUSIVE. The full output is kept in mutants-output/."""
    LOGDIR.mkdir(exist_ok=True)
    (LOGDIR / f"{tag}.txt").write_text(f"exit {code}\n{out}")
    if code is None:
        return "INCONCLUSIVE (timeout)"
    errs = [(int(l), m) for l, m in re.findall(re.escape(fname) + r":(\d+):\d+: error: ?(.*)", out)]
    if code == 0 and not errs and not re.search(r": error", out):
        return "COMPILES"
    if RESOURCE.search(out):
        return f"INCONCLUSIVE (exit {code}, resource limit)"
    if any(PARSE.match(m) or INFRA.search(m) for _, m in errs) or (not errs and INFRA.search(out)):
        return f"INCONCLUSIVE (exit {code}, parse or import error)"
    if code == 1 and any(l >= mline for l, _ in errs):
        return "REJECTED"
    return f"INCONCLUSIVE (exit {code}, no error at or after the mutated line in {fname})"


def mutated_line(text: str, old: str) -> int:
    return text[: text.index(old)].count("\n") + 1
tmpdir = tempfile.mkdtemp(dir=os.environ.get("TMPDIR"))
path = os.path.join(tmpdir, "Mutant.lean")


def run(text: str, mline: int, tag: str) -> str:
    open(path, "w").write(text)
    try:
        r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True, timeout=1500)
    except subprocess.TimeoutExpired as e:
        return classify(None, str(e.stdout or "") + str(e.stderr or ""), path, mline, tag)
    return classify(r.returncode, r.stdout + r.stderr, path, mline, tag)


ok = True
for SRC in sorted({m[0] for m in MUTANTS}):
    v = run(open(SRC).read(), 0, "control-" + os.path.basename(SRC))
    print(f"control (unchanged {SRC}): {v}", flush=True)
    ok &= v == "COMPILES"
if not ok:
    os.remove(path); os.rmdir(tmpdir)
    sys.exit("CONTROL FAILED: an unchanged target does not compile; mutants not run")
killed = 0
for i, (SRC, name, old, new) in enumerate(MUTANTS):
    src = open(SRC).read()
    assert src.count(old) == 1, f"pattern not unique: {name}"
    v = run(src.replace(old, new), mutated_line(src, old), f"mutant-{i}")
    killed += v == "REJECTED"
    print(("killed  " if v == "REJECTED" else v + " "), name, flush=True)
os.remove(path); os.rmdir(tmpdir)
print(f"{killed}/{len(MUTANTS)} mutants killed")
sys.exit(0 if killed == len(MUTANTS) else 1)
