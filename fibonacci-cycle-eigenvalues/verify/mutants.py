"""Mutation tests: each mutant edits one checking script in a temporary copy of verify/; the run must exit nonzero
(a timeout or crash also counts as a rejection). The unmodified programs are run first and must all pass, including
certify.py with unequal weights as the baseline for the equal-weight mutant. Exits nonzero if a baseline fails or any
mutant survives."""
import shutil, subprocess, sys, tempfile, pathlib
HERE = pathlib.Path(__file__).resolve().parent
PY = sys.executable
CASES = [  # (script, args, old, new, description)
    ("certify.py", ["6", "1", "2"], 'T=[[one-lam*iw', 'T=[[one-lam*iw*2', "wrong transfer matrix"),
    ("certify.py", ["6", "1", "1"], None, None, "equal weights (theorem needs a != b)"),
    ("scan.py", ["200", "1", "2"], "flint.fmpq(2):{33,53,106}", "flint.fmpq(2):{33,53}", "wrong exceptional set"),
    ("scan.py", ["200", "1", "3"], "flint.fmpq(3):set()", "flint.fmpq(3):{33}", "spurious expected double"),
    ("sym.py", [], "l**2*(a-b)**2/(a**2*b**2)", "l**2*(a-b)**2/(a*b)", "wrong commutator invariant"),
    ("lam1.py", [], "else Fr(1,2)", "else Fr(1,3)", "wrong B weight at lambda = 1"),
    ("lam1_norm.py", [], "MB=[[Fr(1,2),Fr(1,2)]", "MB=[[Fr(2,3),Fr(1,3)]", "wrong M_B"),
    ("lemma_check.py", [], "y=s[m-3]+s[m-2]", "y=s[m-2]+s[m-3]", "wrong factor y"),
    ("ostrowski_check.py", [], "parts.append(j); m-=len(s[j])", "parts.append(j); m-=len(s[j])-0*1 if j>2 else len(s[j])+1", "wrong decomposition"),
    ("recheck.py", [], "twist=1j", "twist=-1j*1j", "twist phase 1 instead of i"),
    ("recheck.py", [], "assert hits == [20, 33, 53, 106]", "assert hits == [20, 33, 53]", "wrong lambda=1 set"),
]
def run(d, script, args, t=900):
    try: return subprocess.run([PY, script, *args], cwd=d, capture_output=True, timeout=t).returncode
    except subprocess.TimeoutExpired: return "timeout"
BASE = [("certify.py", ["6", "1", "2"]), ("certify.py", ["6", "3", "7/5"]), ("scan.py", ["200", "1", "2"]),
        ("scan.py", ["200", "1", "3"]), ("sym.py", []), ("lam1.py", []), ("lam1_norm.py", []), ("lemma_check.py", []),
        ("ostrowski_check.py", []), ("recheck.py", [])]
for script, args in BASE:                       # every unmodified program must pass first
    rc = run(str(HERE), script, args)
    print(f"{'BASELINE OK' if rc == 0 else 'BASELINE FAILED'} {script} {' '.join(args)} (exit {rc})", flush=True)
    if rc != 0: sys.exit(2)
bad = 0
for script, args, old, new, desc in CASES:
    with tempfile.TemporaryDirectory() as tmp:
        for f in HERE.glob("*.py"): shutil.copy(f, tmp)
        if old is not None:
            src = (pathlib.Path(tmp) / script).read_text()
            assert src.count(old) == 1, (script, old)
            (pathlib.Path(tmp) / script).write_text(src.replace(old, new))
        rc = run(tmp, script, args)
        killed = rc != 0
        print(f"{'KILLED ' if killed else 'SURVIVED'} {script:20s} {desc} (exit {rc})", flush=True)
        bad += not killed
print(f"{len(CASES)-bad}/{len(CASES)} mutants killed")
sys.exit(1 if bad else 0)
