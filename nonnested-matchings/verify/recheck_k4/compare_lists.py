"""Compare the leftover families of Computation 2 as lists: ../k4_covered_list.tsv (from k4_covered.py --list-only)
against recheck_covered_list.tsv (from run_recheck_covered.py, Fable's C program). Each row: g1 g2 lm rm o1 o2."""
import sys
if not __debug__:
    sys.exit("refusing to run under python -O: the checks are assertions")
a = set(open("../k4_covered_list.tsv").read().split("\n")) - {""}
b = set(open("recheck_covered_list.tsv").read().split("\n")) - {""}
print(f"k4_covered.py: {len(a)} families; recheck_covered.c: {len(b)} families; common: {len(a & b)}")
assert a == b and len(a) == 15984
print("ALL CHECKS PASSED: the two lists of 15,984 families are identical")
