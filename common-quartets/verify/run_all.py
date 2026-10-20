"""Every fast verify check in one process (also the check that mutants.py must break)."""
import runpy
import subprocess
import sys

d = __file__.rsplit("/", 1)[0]
for script, args in [("check_fig4.py", []), ("witness13.py", []), ("sat_h3.py", ["--count", "5", "6", "7"]),
                     ("check_n14_shape0.py", [])]:
    r = subprocess.run([sys.executable, "-I", "-W", "ignore", f"{d}/{script}", *args])
    if r.returncode:
        sys.exit(f"FAIL {script}")
print("all verify checks pass")
