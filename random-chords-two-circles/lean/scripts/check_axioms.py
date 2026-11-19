"""Fail unless every theorem printed by RandomChords/Audit.lean depends only on the standard axioms.

    lake env lean RandomChords/Audit.lean > axiom-validation.txt && python3 -I scripts/check_axioms.py axiom-validation.txt

Exit 0: at least one audit line, all with axioms within {propext, Classical.choice, Quot.sound}.
Exit 1: some theorem uses another axiom (sorryAx, a native_decide axiom, a custom axiom) or nothing was audited.
"""
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
text = open(sys.argv[1]).read()
# a report may span lines: "'name' depends on axioms: [a,\n b, c]" ; "does not depend on any axioms" is also fine
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S)
clean = re.findall(r"'([^']+)' does not depend on any axioms", text)
bad = [(n, sorted(set(a.split()) - ALLOWED)) for n, ax in reports for a in [ax.replace(",", " ")] if set(a.split()) - ALLOWED]
print(f"{len(reports) + len(clean)} theorems audited; {len(bad)} with non-standard axioms")
for n, extra in bad:
    print("NON-STANDARD:", n, extra)
sys.exit(1 if bad or not (reports or clean) else 0)
