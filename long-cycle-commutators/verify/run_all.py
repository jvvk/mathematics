"""Run both independent checks of the Problem 84 note (they share no code). Exit non-zero on any failure."""
import subprocess, sys, os
here = os.path.dirname(os.path.abspath(__file__))
for script, args in (("independent.py", ["1", "3", "5", "7"]), ("codex_check.py", [])):
    r = subprocess.run([sys.executable, os.path.join(here, script), *args], capture_output=True, text=True)
    print(f"== {script}: exit {r.returncode}\n" + "\n".join(r.stdout.strip().splitlines()[-3:]))
    if r.returncode: sys.exit(r.returncode)
print("ALL VERIFICATION PASSED")
