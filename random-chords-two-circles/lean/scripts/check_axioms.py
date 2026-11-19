"""Fail unless every theorem that RandomChords/Audit.lean asks about is reported exactly once and depends only on
the standard axioms.

    lake env lean RandomChords/Audit.lean > axiom-validation.txt && python3 -I scripts/check_axioms.py axiom-validation.txt

Exit 0: the reported names are exactly those of the `#print axioms` lines, each once, all within
{propext, Classical.choice, Quot.sound}. Exit 1 otherwise (a missing, extra or duplicated report, or another axiom).
"""
import collections
import re
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
audit = Path(__file__).resolve().parent.parent / "RandomChords" / "Audit.lean"
wanted = re.findall(r"^#print axioms (\S+)", audit.read_text(), re.M)
text = open(sys.argv[1]).read()
# reports start a line: 'Name' depends on axioms: [...]  (the list may wrap; names may contain primes)
reports = re.findall(r"^'(.+?)' depends on axioms: \[([^\]]*)\]", text, re.M | re.S)
clean = re.findall(r"^'(.+?)' does not depend on any axioms", text, re.M)
names = [n for n, _ in reports] + clean
count = collections.Counter(names)
bad = sorted((n, sorted(set(ax.replace(",", " ").split()) - ALLOWED)) for n, ax in reports
             if set(ax.replace(",", " ").split()) - ALLOWED)
missing = [w for w in wanted if w not in count]
extra = [n for n in count if n not in wanted]
dupes = [n for n, c in count.items() if c > 1]
print(f"{len(wanted)} theorems requested, {len(names)} reported; non-standard {len(bad)}, missing {len(missing)}, "
      f"extra {len(extra)}, duplicated {len(dupes)}")
for line in [f"NON-STANDARD: {n} {x}" for n, x in bad] + [f"MISSING: {n}" for n in missing] + \
        [f"EXTRA: {n}" for n in extra] + [f"DUPLICATED: {n}" for n in dupes]:
    print(line)
sys.exit(1 if (bad or missing or extra or dupes or not wanted) else 0)
