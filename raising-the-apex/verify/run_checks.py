"""Foreground, single-core, bounded audit plus deliberately broken claims."""
import os
from pathlib import Path
import subprocess
import sys
import time

root = Path(__file__).resolve().parent
env = dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", VECLIB_MAXIMUM_THREADS="1")
mutants = ["boundary_sign", "edge_velocity", "determinant_sign", "orientation",
           "section_scale", "likelihood_sign", "ratio_reversal",
           "drop_logconcavity", "drop_foot_condition"]
start = time.monotonic()
for mutant in ["none", *mutants]:
    command = ["timeout", "120", "nice", "-n", "15", sys.executable,
               str(root / "verify.py"), "--mutant", mutant]
    result = subprocess.run(command, env=env, capture_output=True, text=True)
    if mutant == "none":
        if result.returncode:
            print(result.stdout, result.stderr)
            raise SystemExit("Baseline failed")
        print(result.stdout.strip(), flush=True)
    else:
        # A killed or crashing process is not a rejected mathematical mutation.
        if result.returncode != 1 or "AssertionError:" not in result.stderr:
            print(result.stdout, result.stderr)
            raise SystemExit(f"Mutation {mutant} was not detected by an assertion")
        print("REJECTED", mutant, result.stderr.strip().splitlines()[-1], flush=True)
print(f"All {len(mutants)} mutants rejected; wall time {time.monotonic()-start:.2f}s")
