# Search and certificates

All commands run from this folder, on one core. The C programs have no dependencies; Python needs `numpy`
(and `networkx`, `pynauty` for `gen_nets.py`).

## Certificates

- `certificates/cert_dD.txt` (d = 3, 4, 5): one line per unfolding: its cells in Z^(d-1), whether it is
  linear, and a lattice basis (rows, Hermite normal form) if it tiles by translations of a sublattice, else `none`.
- `certificates/inv_dD.txt` (d = 3, 4, 5): for every unfolding, a tiling by P and -P + t: an onto homomorphism
  phi: Z^(d-1) -> G, given by the images of the basis vectors in G = Z_a x Z_b x ..., with phi(P) and
  phi(t) - phi(P) partitioning G (Lemma 5 of the paper). Translates by ker(phi) then tile.
- `certificates/s2_d4.txt`: for the 116 unfoldings of the 4-cube that do not tile by lattice translations, a
  two-tile tiling whose second tile is a rotated copy.
- `certificates/nets_d6.txt.gz`, `certificates/inv_d6.txt.gz`: the 502,110 unfoldings of the 6-cube and a
  P, -P certificate for each, in the same formats.

## Programs

| Program | What it does |
|---|---|
| `unfold.c` | rolls every labelled spanning tree of the facet graph into a polycube (d <= 5), reduces by isometry, tests every sublattice of index 2d |
| `stage2.c` | two-tile search over homomorphisms to groups of order 4d; `ONLY_INVERSION=1` restricts the second tile to -P |
| `gen_nets.py` | unfoldings up to symmetry as (tree, matching avoiding the tree) with nauty canonical forms; used for d = 6 |
| `inv.c` | the fast d = 6 search: Lemma 5 directly, first onto phi with A + A != G |
| `verify.py` | independent lattice check by cyclic quotients (d = 3, 5) and exact checks of each lattice basis |
| `verify2.py` | independent two-tile check with its own group arithmetic: phi onto, finds t, one point per coset covered once, det g |
| `geomcheck.py` | literal placement of tiles in a box, every cell covered exactly once |

## Reproduce

```sh
cc -O2 -o unfold unfold.c && cc -O2 -o stage2 stage2.c
./unfold 5 cert_d5.txt                                  # 9,694 unfoldings, 6,573 lattice tilers (12 s)
sed 's/lattice=.*/lattice=none/' cert_d5.txt > all5.txt
ONLY_INVERSION=1 ./stage2 5 all5.txt inv_d5.txt         # P and -P for all 9,694 (about 73 s)
python3 verify.py certificates/cert_d5.txt 10           # independent lattice check
python3 verify2.py certificates/cert_d5.txt certificates/inv_d5.txt      # independent two-tile check
python3 geomcheck.py certificates/cert_d5.txt certificates/inv_d5.txt 25 # literal box covering
```

For d = 6 (about an hour in total; the optional first/last arguments run it in chunks):

```sh
python3 gen_nets.py 6 nets_d6.txt                       # 502,110 unfoldings, 1,911 linear
cc -O2 -o inv inv.c && ./inv 6 nets_d6.txt inv_d6.txt 0 20000   # and so on
gunzip -k certificates/*_d6.txt.gz
python3 verify2.py certificates/nets_d6.txt certificates/inv_d6.txt     # 502,110 / 502,110
```
