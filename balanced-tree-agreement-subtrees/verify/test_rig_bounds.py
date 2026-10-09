"""The exact-arithmetic lower bounds in certify_simplex_rig.py must lie below the true values (checked at
60 digits), and an inflated candidate must fail the exact test. Usage: test_rig_bounds.py"""
import random, sys
from fractions import Fraction
import mpmath as mp
sys.argv = ["x", "2,1", "2/5", "157/2000", "0"]
import importlib.util
spec = importlib.util.spec_from_file_location("rig", "certify_simplex_rig.py")
src = open("certify_simplex_rig.py").read().split("# ---------- search ----------")[0]
ns = {"__name__": "rig"}; exec(compile(src, "rig", "exec"), ns)
mp.mp.dps = 60
rng = random.Random(5); bad = 0
for _ in range(20000):
    xi = rng.randint(1, 1 << 52)
    r = ns["lo_pow"](xi)
    true = (mp.mpf(xi) / 2**52) ** (mp.mpf(2) / 5)
    bad += not (mp.mpf(r) <= true)
for ds, r in ns["W_LO"].items():
    bad += not (mp.mpf(r) <= mp.power(2, mp.mpf(157) / 2000 * ds))
print("bounds above true value:", bad)
# mutant: an inflated candidate must fail the exact check r^5 * 2^104 <= xi^2 * d^5
xi = 123456789012345; r = float((xi / 2**52) ** 0.4) * (1 + 1e-12); n, d = r.as_integer_ratio()
print("inflated candidate rejected:", not (n**5 * (1 << 104) <= xi**2 * d**5))
