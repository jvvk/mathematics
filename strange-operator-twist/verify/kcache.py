"""Compute K(q) of Bogner's operator to order M and cache it (exact integers)."""
import sys, json
sys.argv = ["x", sys.argv[1] if len(sys.argv) > 1 else "40"]
import strange
K, _ = strange.main()
assert all(v.denominator == 1 for v in K)
json.dump([int(v) for v in K], open(f"K{strange.M}.json", "w"))
print("cached", len(K), "coefficients")
