"""From enum.py's output (myfams.json), keep the uncovered families with both centre gaps <= 3, translated to start at
1, and write them to small16.json for check3.py. (Fable's check2.py also compared with the lead's files; that
comparison is left out here so that this recheck shares no input with k4_uncovered.py.)"""
import json
res = json.load(open("myfams.json"))
def tr(F):
    m = min(v for e in F for v in e)
    return tuple(sorted((a - m + 1, b - m + 1) for a, b in F))
small = {tr([tuple(e) for e in F]) for k, v in res.items() if max(map(int, k.split(","))) <= 3 for F in v["fams"]}
print("uncovered families with both centre gaps <= 3:", len(small))
assert len(small) == 16
json.dump([list(f) for f in sorted(small)], open("small16.json", "w"))
