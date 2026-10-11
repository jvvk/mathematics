"""Mutants for mo_check.py: each wrong claim must make it fail."""
import pathlib, subprocess, sys

SRC = (pathlib.Path(__file__).parent / "mo_check.py").read_text()
MUTANTS = [
    ("6a+1 intercept", "3, 6, 1)", "3, 6, 3)"),
    ("edge dropped", "(2,3),(2,4)], 0, 3", "(2,3)], 0, 3"),
    ("6a+9 intercept", "2, 4, 6, 9)", "2, 4, 6, 7)"),
]
killed = 0
for name, old, new in MUTANTS:
    assert SRC.count(old) == 1, name
    r = subprocess.run([sys.executable, "-c", SRC.replace(old, new)], capture_output=True, text=True)
    killed += r.returncode != 0
    print("killed  " if r.returncode else "SURVIVED", name)
print(f"{killed}/{len(MUTANTS)} killed")
sys.exit(0 if killed == len(MUTANTS) else 1)
