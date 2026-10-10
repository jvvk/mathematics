# Journal-ready audit: "Catching the centroid" (PAPER_STANDARD gates 2 and 3)

Audit 2026-10-10, redone after the J1 search found Stewart (1958). Verdicts are for the repository preprint
in jvvk/mathematics; a journal submission re-opens J6 and J7.

## Gate 2

| # | Item | Verdict | Evidence |
|---|---|---|---|
| J1 | Novelty | PASS | Searched 2026-10-10: the MSE thread (4 answers, all comments), MathOverflow (no cross-post), web searches for the centroid functional and for a centroid version of Kovner–Besicovitch, Feldman arXiv 2608.04516, Fáry–Rédei Math. Ann. 122 (scan), Grünbaum PJM 1960, Stein PJM 1956 (read in full), and every work citing Levi 1952 and Stein 1956 (OpenAlex). That citation sweep found B. M. Stewart, PJM 8 (1958) 335–337 (read in full): s(K) >= 2/3 at the centroid, which was our Conjecture 1. The note now quotes Stewart as the input of Theorem 1, credits Levi (2/5 at the centroid, as reported by Stein) for the Minkowski–Radon step, and presents Lemma 1 / Proposition 3 as a short proof of Stewart's inequality for three-sided regions, not as new. Lassak's centroid papers (arXiv 2202.01815, 2212.11609) concern a different quantity. Grünbaum's 1963 survey is lending-only at the Internet Archive and was not read; the primary sources it would cite (Besicovitch, Fáry–Rédei, Levi, Stein, Stewart) are now read or cited from a reading source. |
| J2 | Claims match the record | PASS | New: Proposition 1 (the identity), formula (3), Proposition 2 (the product bound) and hence Theorem 1 as a bound on P. Credited: Grünbaum, Stewart, Levi (via Stein), Minkowski–Radon (via Feldman), Kovner/Besicovitch/Fáry, Fáry–Rédei; the regular-polygon result and the 2/3 non-convex example to the MSE answers; Marco's Fourier series as close to Proposition 1. |
| J3 | References verified | PASS | Crossref metadata for every DOI (Besicovitch, Fáry–Rédei, Grünbaum, Levi, Stein, Stewart, Shephard, mathlib CPP); Stein and Stewart read from the MSP PDFs (lit/stein1956.pdf, lit/stewart1958.pdf); Levi's content as reported by Stein Theorem 3 and stated so in the text. |
| J4 | Independent recheck | PASS | `verify/recheck/recheck.py` shares no code with `verify/`: Table 1, the asker's values, the Figure 2 caption, the arithmetic of Theorem 1 and the 8/15 bound, the 2550/3000 count, Stewart's s >= 2/3 on 500 random polygons (T6), Monte Carlo agreement; 3/3 own mutants killed. `verify/searches.py stewart` checks Stewart's cap-by-cap inequality on 1500 polygons (max ratio 1 + 4e-8, quadrature error at triangles). |
| J5 | Referee read | PASS (self) | Cold read of the rebuilt PDF: Theorem 1's proof uses only Proposition 2 and the two quoted inequalities; "Both inequalities are equalities for every triangle" replaced an earlier wrong "tight"; Proposition 3's sign pattern matches Lean's. An outside read is still A1. |
| J6 | AI policy | PASS for the repository | Acknowledgement names Claude (Opus 5.5) and what it did, as in the other notes in the repository. No journal targeted. |
| J7 | Venue fit and format | PASS for the repository | Repository note, British spelling, 7 pages. Journal candidates if wanted later: Elemente der Mathematik, Mathematical Gazette. |
| J8 | Data and code availability | PASS (on push) | Folder in jvvk/mathematics with paper, Lean project, verify/ and recheck/; Zenodo or Software Heritage deposit optional. |
| J9 | Self-reference | PASS | No reliance on reputation or private correspondence. |

## Gate 3

| # | Item | Verdict | Note |
|---|---|---|---|
| A1 | Vamshi has read every proof and reference | OPEN | Waived for the repository release by Vamshi on 2026-10-10 ("if all the gates pass except my reading gate, push"). |
| A2 | Courtesy contacts | NOT BLOCKING | Dan and the answerers, via an MSE answer in Vamshi's own words linking the note. Courtesy contacts never block release. |
| A3 | Commitments honoured | PASS | Nothing in the register forbids release. |
