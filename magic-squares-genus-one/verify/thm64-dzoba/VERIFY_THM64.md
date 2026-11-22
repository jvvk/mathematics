# Independent check of Dzoba E1 Theorem 6.4 (genus-0 curves on the magic-square surface)

Date: 2026-10-25. Target: `claude/E1-DIFFERENTIALS.md` §6.3–6.4 in github.com/dzoba/magic-squares-of-squares
(commit aa23aa9). Written from their statement only; none of their code, caches or logs were used. Their
referee report for §6.4 (msq-e1-ref) is not in the public repo.

**Theorem 6.4.** Every curve of geometric genus 0 on the minimal resolution Y of V is one of the 256 exceptional
curves or one of Auel–Singer's 128 conics over u = 0 and v = 0. So V contains no rational curve with distinct entries.

> **Release note (22 November 2026).** This is the check of 25 October 2026, shipped with the genus-one paper.
> Rerunning it for the release: `eta_regular.py`, `curves.py`, `gaps.py`, `mutants.py` and `pari_check.gp` pass.
> `eta_space.py` is shipped only as the definitions `mutants.py` imports. Its own derivation of the node conditions
> (removed) left a regular space of dimension 0, rejecting even the ten reflexive forms (l.x)K(l) that vanish
> identically as differentials (`mutants.py` confirms the reflexive space has rank 1 as differentials), so that
> derivation was wrong, not eta. The regularity of eta at the nodes rests on `eta_regular.py`, and the dimension
> count in step 1 on `mutants.py`. Both now exit nonzero when an expected outcome fails. The mutant M3 in
> `mutants.py` turned out vacuous (the 8-line space equals the 9-line space, dimension 11), and is now asserted as
> that finding; M1 and M2 are rejected as intended. The target repository (github.com/dzoba/magic-squares-of-squares, commit aa23aa9) is no
> longer public and carries no licence, so it is cited, not included.

## Verdict: CONFIRMED

Every computational input reproduces exactly, by independent code, and the deduction has no gap that I could find.
This is a machine-assisted check, not a human referee report.

## The proof, step by step, and what was checked

1. **ω = π\*η is a regular section of S⁴Ω_Y.** Here η = det(x, ∇F(W), ∇G(W)) / ∏L, with W = x × dx,
   F = ℓ₁³ − ℓ₀²ℓ₁ and G = ℓ₂³ − ℓ₀²ℓ₂. Since Y is smooth, regularity only needs checking along divisors:
   - *Ramification curves over the 9 cell lines.* In a chart with L = y, the cover is z² = y. Terms dp^i dy^j
     with j < 2 must vanish on y = 0. `eta_regular.py`: all 9 pass.
   - *Exceptional curves over the 8 triple points.* Locally the cover is the A1 cone z₃² = z₁² + z₂². The minimal
     resolution chart is (X, w) ↦ (p, y) = (X²(w²−1)²/4, X²w²); this was checked to be birational, with all three
     square roots regular on it. The pulled-back coefficients have no pole along X = 0. `eta_regular.py`: all 8 pass.
   - Other divisors map étale to P² minus the lines, where η is polynomial. Points (the ordinary double points of
     the arrangement) need no check by Hartogs.
   - *Mutation test* (`mutants.py`). A random quartic fails all 9 lines and all 8 nodes. η·H/L₍₁,₁₎ (one extra pole)
     fails exactly line (1,1) and exactly its 3 triple points.
   - *Side result.* Among forms Q(x,W)/∏L with Q linear in x and quartic in ℓ, the line conditions cut 45
     dimensions to 11. Of these, 10 are forms (ℓ·x)K(ℓ), which vanish identically as differentials. The rank as
     differentials is 1: η is the unique such form, consistent with their h⁰ = 1. For simple-pole forms, the node
     condition follows from the line conditions (Q(P,·) has double roots at three lines through P). Their stronger
     stated condition "Q(p,·) ≡ 0" is satisfied by η but is not needed.
2. **Genus-0 curves are integral.** ω restricted to the normalisation of a genus-0 curve D is a section of K⁴ = O(−8),
   so it is zero. If D is not exceptional and C = π(D) is not a cell line, π is étale at a general point of D.
   Hence C is an integral curve of η. (Hand check.)
3. **Integral lines.** Q(x, ℓ) = x·q(ℓ) with q = ∇F × ∇G. A line ℓ₀ is integral iff ℓ₀ × q(ℓ₀) = 0. SymPy
   (Gröbner) and PARI (resultants over Q and Q(√3)) both find exactly 15 points. These are the 9 cell lines,
   u = 0, v = 0, and the 4 lines √3e ± u ± v = 0. (`curves.py`, `pari_check.gp`)
4. **Non-line integral curves.** By biduality, C\* is tangent to the vector field q, which is tangent to every
   member of the pencil F − cG (`curves.py`, check C). F/G is then constant on C\*, because q is nonzero modulo ℓ
   off a finite set, so C\* lies in a member Γ_c. The web degenerates only at 8 points, the triple points
   (`gaps.py`), so general points of C are fine.
5. **Pencil.** The singular members are exactly c ∈ {0, ∞, ±1} (all charts, `gaps.py`). c = 0 and c = ∞ are three
   concurrent lines, which dualise to points. c = ±1 is a line plus a conic, and the conics dualise to
   C_±: 4(u² ∓ uv + v²) = 3e². A smooth member has an elliptic dual normalisation, so no genus-0 curve can lie over it.
6. **Fibre genera.** Each candidate image C is P¹. Components of π⁻¹(C) come from the (Z/2)^r Kummer cover, with
   g = 1 − 2^r + B·2^{r−2}, computed exactly from root valuations (`curves.py`):

| Curve | Components | Genus |
|---|---:|---:|
| u = 0, v = 0 | 64 each | **0** |
| e = 0 (cell) | 16 | 1 |
| 4 corner cell lines | 8 each | 5 |
| 4 edge cell lines | 4 each | 17 |
| √3e ± u ± v = 0 | 4 each | 49 |
| C₊, C₋ | 32 each | 5 |

   This is identical to their table. Only u = 0 and v = 0 carry genus-0 curves: 2 × 64 = 128 conics. ∎

## Consequences

- Auel–Singer's Remark A.2 has a positive answer: the 128 conics are all the conics, and all the rational curves.
- PROOF.md's Propositions 1 and 2 (real families of degree ≤ 5, one sextic center) are special cases.
- Not affected: genus-1 curves (their §6.4 GAP), and isolated rational points. The integer problem stays open.

## Files

`eta_regular.py` (A), `mutants.py` with the definitions in `eta_space.py` (mutation and dimension), `curves.py` (B–E), `gaps.py`
(c = ∞, chart completeness, web degeneracy), `pari_check.gp` (second CAS for B). Run with
`python3 <file>` from this folder (SymPy 1.14); `gp -q pari_check.gp`. The scripts total under
15 minutes of CPU time.
