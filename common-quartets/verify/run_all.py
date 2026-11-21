"""Every fast verify check in one process (also the check that mutants.py must break).
Exit 1: a check failed (FAIL). Exit 2: a script ended by a signal or an unexpected status (CRASH)."""
import runpy
import subprocess
import sys

d = __file__.rsplit("/", 1)[0]
for script, args in [("check_fig4.py", []), ("witness13.py", []), ("sat_h3.py", ["--count", "5", "6", "7"]),
                     ("check_n14_shape0.py", [])]:
    r = subprocess.run([sys.executable, "-I", "-W", "ignore", f"{d}/{script}", *args])
    if r.returncode == 1:
        sys.exit(f"FAIL {script}")
    if r.returncode:
        print(f"CRASH {script} (exit {r.returncode})")
        sys.exit(2)
print("all verify checks pass")
