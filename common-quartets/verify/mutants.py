"""Mutation tests for the verify scripts: each mutant plants one error and run_all.py must then fail.
Run from verify/: python3 mutants.py (a few minutes)."""
import subprocess, sys

MUTANTS = [
    ('check_fig4.py', 'Fig 4: T2 leaves 4 and 10 swapped (claim fails)', 'T2 = (((1, 5), (4, 9)), (10, (3, 8)), (7, (2, 6)))', 'T2 = (((1, 5), (10, 9)), (4, (3, 8)), (7, (2, 6)))'),
    ('witness13.py', 'witness: T3 leaves 0 and 5 swapped (3 common quartets)', 'T3 = (0, (((5, 9),', 'T3 = (5, (((0, 9),'),
    ('witness13.py', 'witness: leaf 12 duplicated as 11', 'T2 = (0, ((12, ', 'T2 = (0, ((11, '),
    ('quartets.py', "quartet split read from wrong side (only clusters containing the pair's first leaf)", '            if len(A) == 2:', '            if len(A) == 2 and min(Qs) in A:'),
    ('sat_h3.py', 'encoding: tree count n=6 claimed 104', 'df = {5: 15, 6: 105, 7: 945}', 'df = {5: 15, 6: 104, 7: 945}'),
    ('sat_h3.py', 'encoding: common-quartet ban only on splits 0,1', '            for j in range(3):\n                cls.append([-x[t, Q, j] for t in range(k)])', '            for j in range(2):\n                cls.append([-x[t, Q, j] for t in range(k)])'),
    ('sat_h3.py', 'encoding: 5-point patterns from one 5-leaf shape only (caterpillar dropped)', '    assert len(pats) == 15\n    return sorted(pats)', '    assert len(pats) == 15\n    return sorted(pats)[:14]'),
    ('shapes.py', 'shapes: dedupe dropped one class', '    return [_label(g) for g in reps]', '    return [_label(g) for g in reps][1:]'),
]

killed = 0
for src, name, old, new in MUTANTS:
    text = open(src).read()
    assert text.count(old) == 1, f"{name}: anchor not unique in {src}"
    open(src, "w").write(text.replace(old, new))
    try:
        r = subprocess.run([sys.executable, "-W", "ignore", "run_all.py"], capture_output=True, text=True, timeout=600)
        dead = r.returncode != 0
    finally:
        open(src, "w").write(text)
    killed += dead
    print(("killed   " if dead else "SURVIVED ") + name, flush=True)
print(f"{killed}/{len(MUTANTS)} mutants killed")
sys.exit(0 if killed == len(MUTANTS) else 1)
