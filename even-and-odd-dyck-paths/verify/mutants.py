"""Mutation test for involution.py: each mutant must make check() fail for some n <= 8."""
import involution as I

orig_iota, orig_sym = I.iota, I.to_symmetric

def no_ud_ba(w):
    saved = dict(I.PARTNER); I.PARTNER.pop("ud"); I.PARTNER.pop("ba")
    v = orig_iota(w); I.PARTNER.clear(); I.PARTNER.update(saved); return v

def du_at_zero(w):
    saved = dict(I.PARTNER); I.PARTNER.update(I.PARTNER_HIGH)
    v = orig_iota(w); I.PARTNER.clear(); I.PARTNER.update(saved); return v

def no_c_to_u(w):
    half = "".join({"uu": "u", "dd": "d", "aa": "a", "bb": "b", "ab": "a"}[w[i:i+2]] for i in range(0, len(w)-1, 2))
    mid = w[-1] if len(w) % 2 else ""
    return half + mid + half[::-1].translate(str.maketrans("ud", "du"))

def offset_blocks(w):
    return w[0] + orig_iota(w[1:]) if w else w

MUTANTS = {"no_ud_ba": ("iota", no_ud_ba), "du_ab_at_height0": ("iota", du_at_zero),
           "c_to_level": ("to_symmetric", no_c_to_u), "blocks_offset": ("iota", offset_blocks)}
killed = 0
for name, (attr, f) in MUTANTS.items():
    setattr(I, attr, f)
    try:
        for n in range(1, 9): I.check(n)
        print(f"{name}: SURVIVED")
    except AssertionError as e:
        killed += 1; print(f"{name}: killed at n={n} ({e})")
    setattr(I, attr, orig_iota if attr == "iota" else orig_sym)
print(f"{killed}/{len(MUTANTS)} killed")
