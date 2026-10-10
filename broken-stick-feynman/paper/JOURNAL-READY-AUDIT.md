# Journal-ready audit: "A broken stick and a Feynman diagram" (PAPER_STANDARD gates 2 and 3)

Audit 2026-10-10. Verdicts are for the repository preprint in jvvk/mathematics; a journal submission
re-opens J6 and J7.

## Gate 2

| # | Item | Verdict | Evidence |
|---|---|---|---|
| J1 | Novelty | PASS | Searched 2026-10-10 (STATUS.md, "Novelty check"): the MO thread live (one answer, Zare 2014; comments incl. Kirill's 1/79), MSE 351913 (Sasha's 2013 numerics), every work citing Verreault 2022 and the MacMahon-analysis paper (OpenAlex; all polygons only), Ionascu-Prajitura 2010, Wirth-Dreiding 2009/2013 (existence criteria), the tetrahedron vacuum literature (Kotikov's Gegenbauer method, Broadhurst 1999, Martin-Robertson 2016: integer or massless indices), Davydychev's geometric approach (one-loop, a different construction). No link between random-length simplices and Feynman integrals found; the mechanism (Schoenberg, Schwinger, Siegel, matrix-tree) is classical and is cited as such. |
| J2 | Claims match the record | PASS | New: Theorem 1 for all n, Corollary 1, p_3 to 12 digits, p_4, the correction of 1/79. Credited: Zare's 1/54 polytope, Sasha's 2013 unordered value (ours is consistent and tighter), the classical inputs. No novelty claimed for the unordered value. |
| J3 | References verified | PASS | Crossref metadata for every DOI (Verreault, Schoenberg, Liberti et al., Bogner-Weinzierl, Kirchhoff, Wirth-Dreiding checked); arXiv metadata for Ionascu-Prajitura, Amdeberhan et al., Broadhurst (abstract read: unit powers, masses 0 or 1); Devroye Chapter V Theorem 2.2 read from the author's PDF; Bogner-Weinzierl eqs. (7)-(9) and Section 4 read; Muirhead cited at section level for Siegel's integral (book not read; the constant is confirmed numerically for n = 2, 3, 4). MO/MSE links with access date. |
| J4 | Independent recheck | PASS | `verify/recheck/recheck.py` shares no code with `verify/`: direct Monte Carlo of p_3 (excludes 1/79), the simplex form with its own spanning-tree enumeration, the constants in mpmath, Zare's 1/54, p_4 with the 125 trees of K5, the unordered value over all 720 orders; 3/3 own mutants killed. `verify/check.py` asserts every stated number; `verify/mutants.py` 6/6. |
| J5 | Referee read | PASS (self) | Cold read of the built PDF: the change of variables (Jacobian 2^(n(n-1)/2), N - n(n-1)/2 = n, both in Lean), Tonelli for the interchange (positive integrands), L_t positive definite for t > 0 (K_{n+1} connected), the substitution and the collected powers (Lean for n = 3). Fixes after the read: "two methods that share nothing" (they share the exponential reduction), "only numbers from simulation" (Sasha's were numerical integration), figure labels. An outside read is still A1. |
| J6 | AI policy | PASS for the repository | Acknowledgement names Claude (Opus 5.5) and what it did, as in the other notes in the repository. No journal targeted. |
| J7 | Venue fit and format | PASS for the repository | Repository note, British spelling, 7 pages. Possible later venues: Experimental Mathematics, Mathematical Gazette, or a mathematical-physics letters journal. |
| J8 | Data and code availability | PASS (on push) | Folder in jvvk/mathematics with paper, Lean project, verify/ and recheck/. |
| J9 | Self-reference | PASS | No reliance on reputation or private correspondence. |

## Gate 3

| # | Item | Verdict | Note |
|---|---|---|---|
| A1 | Vamshi has read every proof and reference | OPEN | Not yet waived for this note. |
| A2 | Courtesy contacts | NOT BLOCKING | Dickman and Zare via the MO answer in Vamshi's own words (ANSWER.md drafted). |
| A3 | Commitments honoured | PASS | Register next step: "closed form for T, or publish the identity as is". |
