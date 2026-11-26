"""Run every check of the note; exit nonzero on any failure."""
import subprocess, sys
if not __debug__:
    sys.exit("refusing to run under python -O: the checks are assertions")
steps = [["target.py", "12"], ["catalytic_check.py"], ["pde_proof.py"], ["links_check.py"]]
for st in steps:
    r = subprocess.run([sys.executable, *st])
    if r.returncode:
        sys.exit(f"FAILED: {' '.join(st)}")
print("ALL CHECKS PASSED")
