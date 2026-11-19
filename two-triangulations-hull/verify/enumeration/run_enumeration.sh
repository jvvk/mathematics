#!/bin/bash
# Section 6 enumeration with its inputs and outputs checked: run as
#   bash enumeration/run_enumeration.sh /path/to/ordertype/files      (from verify/; about 5 minutes)
# 1. each database file must have the size and SHA-256 recorded in INPUT-HASHES.json, and a whole number of records;
# 2. fmin for n = 4..8 (F = 6) must reproduce small-search.txt, and for n = 9 (F = 7) and n = 10 (F = 5) the
#    summaries in enumeration/expected09.txt and expected10.txt;
# 3. oct2 on the ten-point file must print the histogram 4:1084 5:14308463.
# fmin and oct2 exit nonzero on a truncated record or a read error, and the pipeline fails on any stage.
set -euo pipefail
DATA=${1:?usage: run_enumeration.sh DATA_DIR}
HERE=$(cd "$(dirname "$0")" && pwd)
V="$HERE/.."
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
python3 -I - "$DATA" "$V/INPUT-HASHES.json" <<'PY'
import hashlib, json, sys
from pathlib import Path
data, manifest = Path(sys.argv[1]), json.loads(Path(sys.argv[2]).read_text())
for n in range(4, 11):
    name = f"otypes{n:02d}.b08" if n <= 8 else f"otypes{n:02d}.b16"
    raw = (data / name).read_bytes()
    want = manifest[name]
    if len(raw) != want["bytes"] or hashlib.sha256(raw).hexdigest() != want["sha256"]:
        sys.exit(f"FAILED: {name} does not match INPUT-HASHES.json")
    rec = n * (2 if n <= 8 else 4)
    if len(raw) % rec:
        sys.exit(f"FAILED: {name} is not a whole number of {rec}-byte records")
    print(f"{name}: {len(raw) // rec} records, hash ok")
PY
cc -O2 -o "$TMP/fmin" "$HERE/fmin.c"
cc -O2 -o "$TMP/oct2" "$HERE/oct2.c"
for n in 4 5 6 7 8; do "$TMP/fmin" "$DATA/otypes0$n.b08" "$n" 6 -1 0; done > "$TMP/small.txt"
diff "$TMP/small.txt" "$V/small-search.txt"
"$TMP/fmin" "$DATA/otypes09.b16" 9 7 -1 0 > "$TMP/n9.txt";  diff "$TMP/n9.txt" "$HERE/expected09.txt"
"$TMP/fmin" "$DATA/otypes10.b16" 10 5 -1 0 > "$TMP/n10.txt"; diff "$TMP/n10.txt" "$HERE/expected10.txt"
"$TMP/oct2" "$DATA/otypes10.b16" 10 4 > "$TMP/oct.txt"
grep -q "^n=10 sets=14309547  histogram of min(oct, 5): 0:0 1:0 2:0 3:0 4:1084 5:14308463$" "$TMP/oct.txt" \
  || { echo "FAILED: oct2 histogram"; cat "$TMP/oct.txt"; exit 1; }
echo "ALL PASS"
