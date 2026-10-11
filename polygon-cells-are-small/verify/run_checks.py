"""Serial, foreground mutation audit. A mutant must fail an expected assertion."""
import subprocess
import sys
import time
from pathlib import Path

HERE=Path(__file__).resolve().parent
VERIFIER=HERE/"verify.py"
MUTANTS={
    "drop_curvature_factor":"wrong curvature",
    "wrong_scale":"side-length scaling",
    "wrong_parity":"invalid endpoint parity",
    "omit_phase":"line does not join the claimed vertices",
    "one_sided":"chords fail to straddle point",
    "include_central":"central cell rotational images should be disjoint",
    "global_diameter":"boundary diameter contradicts global shrinkage",
}

def require_rejection(result,expected):
    assert result.returncode!=0,"mutation checker accepted a passing mutant"
    assert "AssertionError: "+expected in result.stderr,"failure did not come from intended assertion"

start=time.monotonic()
baseline=subprocess.run([sys.executable,str(VERIFIER)],capture_output=True,text=True)
assert baseline.returncode==0,baseline.stderr
assert baseline.stdout.startswith("PASS:"),baseline.stdout
print(baseline.stdout.strip())
for mutant,expected in MUTANTS.items():
    result=subprocess.run([sys.executable,str(VERIFIER),"--mutant",mutant],capture_output=True,text=True)
    require_rejection(result,expected)
    print(f"REJECT {mutant}: {expected}")
# Meta-mutation: an always-passing verifier must not count as a rejected mutant.
try:
    require_rejection(subprocess.CompletedProcess([],0,"PASS: always", ""),"wrong curvature")
except AssertionError:
    print("REJECT meta-mutation: always-passing verifier")
else:
    raise AssertionError("mutation harness always passes")
print(f"Wall time {time.monotonic()-start:.3f}s; serial stdlib only")
