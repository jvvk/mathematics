"""Runs every check behind the note, in exact arithmetic, and fails loudly if any claimed number changes.

    python3 run_all.py          # about two minutes on one core
    python3 run_all.py --deep   # also the long certificates (degree 1000 at p = 5, 500 at p = 7, 11, 13)

Each entry: the script, its arguments, and strings that must appear in its output. Mutants (wrong field,
missing sign, wrong character, corrupted coefficient, wrong twist base, a wrongly claimed fibre) are run by
the scripts themselves and their failure is asserted here.
"""

import json
import os
import subprocess
import sys
from fractions import Fraction as F

from sympy import factorint

HERE = os.path.dirname(os.path.abspath(__file__))
PY = sys.executable

CHECKS = [
    ("prove_symsq.py", [], ["Sym^2(D) normalised coefficients equal L's: True"]),
    ("prove_pullback.py", [], ["D applied to the pullback simplifies to: 0"]),
    (
        "identities.py",
        [],
        [
            "matches recurrence to n = 120 : True",
            "to x^60: True",
            "[1, 16, 576, 25600, 1220800, 58254336]",
        ],
    ),
    (
        "strange.py",
        [],
        [
            "q : ['0', '1', '40', '1984', '106496', '5863168']",
            "K : ['1', '8', '0', '-5632', '-456064', '-17708032']",
            "'-1880/9', '-7126', '-3541608/25', '-18136853/9'",
        ],
    ),
    (
        "ct_check.py",
        [],
        [
            "u_n  from CT        : [1, 8, 96, 1280, 17440, 231168, 2817024, 27844608, 106761600"
        ],
    ),
    (
        "twisted_lambert2.py",
        [],
        [
            "non-integral n_d: 0 of 110",
            "[8, 0, -208, -7126, -141664, -2015232, -3250624, 1056216756, 46257581056",
            "untwisted: 76 of the first 80 not integral",
        ],
    ),
    (
        "mutants_twist.py",
        [],
        [
            "correct (sqrt2, (2/k)^d)    :  0 non-integral",
            "sqrt3, (3/k)^d              : 65 non-integral",
            "sqrt2, no sign              : 29 non-integral",
            "sqrt2, (-1/k)^d             : 25 non-integral",
            "sqrt2, (2/k) not ^d         : 20 non-integral",
            "correct w, K_45 += 45^2     :  1 non-integral",
        ],
    ),
    (
        "dwork_twisted.py",
        [],
        [
            "135/135 congruences hold",
            "untwisted c_p = 1                     : 16/135",
            "wrong sign c_p = 2^((p-1)/2)          : 82/135",
        ],
    ),
    ("padic.py", [], ["satisfying all 21 primes mod p^2: [] 0"]),
    (
        "checks_proof.py",
        [],
        [
            "self-duality 2V2 + θV3 = 0 through q^16: True",
            "for all odd p < 200: True []",
        ],
    ),
    (
        "controls2.py",
        ["20"],
        [
            "Domb: denominator primes [3]",
            "Almkvist-Zudilin: denominator primes []",
            "Cooper s7: denominator primes [2, 7]",
            "Cooper s10: denominator primes [5]",
        ],
    ),
    (
        "prime3_obstruction.py",
        [],
        ["modulo 9: [4, 1, 0, 0]", "modulo 9: [7, 7, 0, 0]", "impossible"],
    ),
    (
        "laurent_models.py",
        [],
        ["'lattice_points': 45", "'interior_points': [(0, 0, 0, 0)]"],
    ),
    ("deformed_sum.py", [], ["All four P jets agree through degree 40."]),
    ("good_faces.py", [], ["binom(2n,n) models with good own faces: 0"]),
    ("jets_test.py", ["bogner", "5", "60", "2"],
     ["L=bogner p=5: alpha1 values surviving mod p^2: 25 (of 25)",
      "P=I*bogner p=5 jets<2: alpha1 mod p^2: [9] (#1); predicted 9"]),
    ("jets_test.py", ["bogner", "7", "60", "2"],
     ["L=bogner p=7: alpha1 values surviving mod p^2: 49 (of 49)",
      "P=I*bogner p=7 jets<2: alpha1 mod p^2: [22] (#1); predicted 22"]),
    ("jets_test.py", ["apery", "5", "60", "2"],
     ["L=apery p=5: alpha1 values surviving mod p^2: 25 (of 25)",
      "P=I*apery p=5 jets<2: alpha1 mod p^2: [0] (#1)"]),
    ("jets_test.py", ["apery", "7", "60", "2"],
     ["L=apery p=7: alpha1 values surviving mod p^2: 49 (of 49)",
      "P=I*apery p=7 jets<2: alpha1 mod p^2: [0, 7, 21, 28, 42] (#5)",
      "P=I*apery p=7 jets<3: alpha1 mod p^2: [0] (#1)"]),
    ("run_ctrl.py", ["P", "5", "30", "2", "apery"], ["α1 values [0]"]),
    ("models_check.py", [], ["PASS moments 320, 6144", "PASS Weierstrass form"]),
]

# (p, R, precision s, residue of alpha_1) from Observation 5.9; the predicted value must equal the residue
CERTS = [
    (5, 30, 4, 509),
    (7, 40, 2, 22),
    (11, 60, 2, 8),
    (13, 70, 2, 86),
    (17, 80, 2, 270),
    (5, 500, 6, 13634),
    (7, 500, 6, 47748),
    (5, 650, 8, 310509),
]
DEEP = [
    (5, 1000, 8, 310509),
    (7, 700, 6, 47748),
    (11, 500, 4, 4848),
    (13, 500, 4, 4142),
]


def run(script, args):
    out = subprocess.run(
        [PY, script, *args], cwd=HERE, capture_output=True, text=True, timeout=3600
    )
    if out.returncode:
        raise SystemExit(
            f"FAIL {script} {args}: exit {out.returncode}\n{out.stderr[-2000:]}"
        )
    return out.stdout


def main():
    deep = "--deep" in sys.argv
    for script, args, wants in CHECKS:
        out = run(script, args)
        missing = [w for w in wants if w not in out]
        if missing:
            raise SystemExit(f"FAIL {script} {args}: missing {missing}\n{out[-3000:]}")
        print(f"PASS {script} {' '.join(args)}")
    # the planted fibre type in models_check must fail
    bad = subprocess.run(
        [PY, "models_check.py"],
        cwd=HERE,
        capture_output=True,
        text=True,
        env={**os.environ, "MUTANT": "1"},
    )
    assert bad.returncode != 0, "models_check mutant survived"
    print("PASS models_check.py MUTANT=1 fails")
    # untwisted denominators: every prime p <= 19 divides a denominator of n_d, d <= 20 (Table 2)
    K = json.load(open(os.path.join(HERE, "K110.json")))
    u = [F(0)] * 21
    for m in range(1, 21):
        u[m] = F(K[m] - sum(u[d] * d**3 for d in range(1, m) if m % d == 0), m**3)
    primes = sorted({q for d in range(1, 21) for q in factorint(u[d].denominator)})
    assert primes == [2, 3, 5, 7, 11, 13, 17, 19], primes
    print("PASS untwisted denominators of n_d, d <= 20: every prime <= 19")
    # the Frobenius certificates of Observation 5.9
    sys.path.insert(0, HERE)
    os.chdir(HERE)
    from certify import run as certify

    for p, R, s, r in CERTS + (DEEP if deep else []):
        c = certify(p, R)
        assert c["feasible"], (p, R)
        assert c["alpha1_residue"] == c["predicted"], (
            p,
            R,
            c["alpha1_residue"],
            c["predicted"],
        )
        if s is not None:
            assert (c["alpha1_precision"], c["alpha1_residue"]) == (s, r), (p, R, c)
        print(
            f"PASS certificate p={p} R={R}: alpha1 = {c['alpha1_residue']} mod {p}^{c['alpha1_precision']}"
            f" = predicted"
        )
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
