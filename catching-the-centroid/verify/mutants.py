"""Mutation tests for the checking harness: each wrong variant of core.py or exact.py must make check.py fail.

Each mutant copies verify/ to a temporary directory, applies one textual change and runs check.py there.
"""

from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent

MUTANTS = [
    ("obtuse threshold pi/3 in the kernel", "core.py", "k = (dt > np.pi / 2 + 1e-12).astype(float)",
     "k = (dt > np.pi / 3 + 1e-12).astype(float)"),
    ("angular density r instead of r^2", "core.py", "rho = r**2 / (2 * A) * (2 * np.pi / M)  # cell masses, sum ~ 1",
     "rho = r / (2 * A) * (2 * np.pi / M)  # cell masses, sum ~ 1"),
    ("centroid off by a factor", "core.py", "c = np.array([((x + xs) * cr).sum(), ((y + ys) * cr).sum()]) / (6 * A)",
     "c = np.array([((x + xs) * cr).sum(), ((y + ys) * cr).sum()]) / (4 * A)"),
    ("half-plane on the near side", "exact.py", "    sp, sq = U @ P.T, U @ Q.T", "    sp, sq = -(U @ P.T), -(U @ Q.T)"),
    ("tan substitution loses a factor h", "exact.py", "total += h[k] ** 2 / (2 * A) * val", "total += h[k] / (2 * A) * val"),
    ("symmetral clipped against K itself", "exact.py", "I = clip(V, 2 * c - V)", "I = clip(V, V)"),
    ("Monte Carlo points not uniform in a triangle", "core.py",
     "        u[flip], v[flip] = 1 - u[flip], 1 - v[flip]", "        pass"),
]


def run(dirpath: Path) -> bool:
    r = subprocess.run([sys.executable, "check.py"], cwd=dirpath, capture_output=True, text=True, timeout=900)
    return r.returncode == 0


def main() -> int:
    bad = 0
    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp) / "v"
        shutil.copytree(HERE, base, ignore=shutil.ignore_patterns("recheck", "__pycache__", "*.json"))
        if not run(base):
            print("BASELINE FAILS")
            return 1
        print("baseline: passes")
        for name, fname, old, new in MUTANTS:
            d = Path(tmp) / "m"
            if d.exists():
                shutil.rmtree(d)
            shutil.copytree(base, d)
            src = (d / fname).read_text()
            if src.count(old) != 1:
                print(f"SETUP ERROR ({src.count(old)} matches): {name}")
                bad += 1
                continue
            (d / fname).write_text(src.replace(old, new))
            ok = run(d)
            print(f"{'SURVIVED' if ok else 'killed'}: {name}")
            bad += ok
    print(f"{len(MUTANTS) - bad}/{len(MUTANTS)} mutants killed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
