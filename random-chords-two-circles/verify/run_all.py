"""Run both checkers, then each deliberate mutant, which must fail with AssertionError."""

import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parent
runs = [("check_lemma.py", None), ("check_theorem.py", None), ("check_extensions.py", None)] + [
    ("check_theorem.py", m) for m in ("moment", "case", "gp", "constant")
] + [("check_extensions.py", m) for m in ("inverse", "weights", "offaxis", "hit")]
for script, mutant in runs:
    cmd = [sys.executable, str(root / script)] + (
        ["--mutant", mutant] if mutant else []
    )
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
    if mutant:
        assert r.returncode == 1 and "AssertionError" in r.stderr, (
            mutant,
            r.stdout,
            r.stderr,
        )
        print(f"REJECTED mutant: {mutant}")
    else:
        assert r.returncode == 0, (script, r.stdout, r.stderr)
        print(r.stdout.strip())
print("ALL PASS")
