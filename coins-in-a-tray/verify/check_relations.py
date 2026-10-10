"""Cross-check of the exact relation test (exact.py) against 60-digit numerics.

For random small integer combinations of rim angles alpha_d (d < 2000) within one class, the valuation criterion must
agree with the numerical test |sum / (2 pi / w) - nearest integer| < 1e-40 at 60 digits.
Half the samples are drawn from d < 100, where most relations live.
MUTANT=1 deletes the prime 3 from every valuation vector; the check must then report disagreements.
"""
import os
import random
from collections import defaultdict

from mpmath import asin, mp, mpf, pi, sqrt

from exact import is_relation, rim_data, roots_of_unity

mp.dps = 60
random.seed(513668)
cls = defaultdict(list)
for d in range(2, 2000):
    a, v = rim_data(d)
    if os.environ.get("MUTANT") == "1" and 3 in v:
        v = {p: e for p, e in v.items() if p != 3}
    cls[a].append((d, v))
checked = relations = bad = 0
for a, lst in cls.items():
    if len(lst) < 2:
        continue
    step = 2 * pi / roots_of_unity(a)
    for _ in range(400):
        pool = [x for x in lst if x[0] < 100] if random.random() < 0.5 else lst
        pool = pool if len(pool) >= 2 else lst
        pick = random.sample(pool, min(3, len(pool)))
        ms = [random.randint(-4, 4) for _ in pick]
        total = sum(m * 2 * asin(1 / sqrt(mpf(d))) for (d, _), m in zip(pick, ms))
        t = total / step
        numeric = abs(t - mp.nint(t)) < mpf(10) ** -40
        exact = is_relation([v for _, v in pick], ms)
        checked += 1
        relations += exact
        bad += numeric != exact
print(f"checked {checked} combinations, {relations} relations, {bad} disagreements")
print("PASS" if bad == 0 else "FAIL")
