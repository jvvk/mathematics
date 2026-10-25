# Two-variable models of D (Discussion, last section of the paper)

Search for a Laurent polynomial h = c0 + h0 in two variables with CT(h^n) = λ^n f_n for n ≤ 8, where f_n are the
coefficients of the holomorphic solution of D (1, 4, 40, 480, ...), on a reflexive polygon.

Scope, exactly as coded:

- λ = ±3 only, so the constant term is c0 = 4λ = ±12 (CT(h) = λ f_1 = 4λ, forced into 12Z by parity).
- Every nonconstant coefficient has absolute value at most 4; vertex coefficients are nonzero.
- All sixteen reflexive polygons, up to GL2(Z). The script's list has 49 entries because its deduplication is
  incomplete; grouping them by exact GL2(Z) equivalence gives the 16 classes (boundary points 3 to 9: 1, 3, 2, 4,
  2, 3, 1), so duplicates repeat work and nothing is missed.

Reproduce (about four minutes in all; each command exits 1 if a model is found):

```
python3 control2d.py                    # positive control: a planted series with c0 = 12 is recovered
python3 search2d_chunk.py 4 0 44        # the 44 smallest polygons
python3 search2d_chunk.py 4 44 48       # the four with eight boundary points
python3 search2d_chunk.py 4 48 49       # the triangle with nine boundary points (about three minutes)
```

`logs/` holds the runs of 25 October 2026 (chunks run in parallel): no model in any range.
