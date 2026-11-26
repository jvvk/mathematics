"""Independent recheck of Computation 2 with Fable's C program recheck_covered.c (shares no code with k4_covered.py).
Compiles it, runs units g1 = 1..16 (gaps up to 16, ends cut off or with up to 7 free vertices), and checks that the
leftover families number 15,984, each with a good window within distance 3 of a centre (column 'near' nonzero)."""
import subprocess, sys
subprocess.run(["cc", "-O2", "-o", "recheck_covered", "recheck_covered.c"], check=True)
total = bad = 0
for g in range(1, 17):
    r = subprocess.run(["./recheck_covered", str(g), "16", "10"], capture_output=True, text=True, check=True)
    rows = [l.split("\t") for l in r.stdout.splitlines() if l.strip()]
    total += len(rows); bad += sum(1 for x in rows if x[7] == "0")
    print(f"g1={g}: {len(rows)} leftovers; {r.stderr.strip()}", flush=True)
print(f"leftovers: {total}; without a good near-centre window: {bad}")
assert total == 15984 and bad == 0
print("ALL CHECKS PASSED")
