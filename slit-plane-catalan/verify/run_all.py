"""Run both verification programs; exit nonzero if either fails."""
import subprocess, sys, os
if not __debug__: sys.exit("refusing to run under python -O")
here = os.path.dirname(os.path.abspath(__file__))
for prog in ["independent.py", "codex_check.py", "tree_bijection.py"]:
    print(f"== {prog}", flush=True)
    r = subprocess.run([sys.executable, os.path.join(here, prog)], cwd=here)
    if r.returncode:
        sys.exit(f"{prog} FAILED (exit {r.returncode})")
print("ALL VERIFICATION PASSED")
