"""Mutation tests for LeanProofs/CubicK23.lean: each deliberate error must make the file fail to compile."""
import subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = (ROOT / "LeanProofs" / "CubicK23.lean").read_text()
MUTANTS = {
    "no 18-cycle (false: 18-cycles exist)": ("p.length ≠ 19 := by", "p.length ≠ 18 := by"),
    "no Hamiltonian cycle (false)": ("p.length ≠ 19 := by", "p.length ≠ 20 := by"),
    "partner shifted": ("(x.2.val + 3) % 4", "(x.2.val + 2) % 4"),
    "inner class of size one": ("decide (x.2.val < 2) != decide (y.2.val < 2)", "decide (x.2.val < 1) != decide (y.2.val < 1)"),
    "degree four": ("G.degree x = 3", "G.degree x = 4"),
    "even 'odd' cycle": ("oddCycle.length = 9", "oddCycle.length = 8"),
}
failed_to_kill = []
for name, (old, new) in MUTANTS.items():
    assert old in SRC, name
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT, delete=False) as f:
        f.write(SRC.replace(old, new))
        path = f.name
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=ROOT, capture_output=True, text=True, timeout=900)
    finally:
        Path(path).unlink()
    killed = r.returncode != 0
    print(f"{'killed' if killed else 'SURVIVED'}: {name}")
    if not killed:
        failed_to_kill.append(name)
sys.exit(1 if failed_to_kill else 0)
