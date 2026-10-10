# Pedagogy check: "A broken stick and a Feynman diagram" (expository bar, all ten items)

Checked 2026-10-10 against the built PDF (7 pages). Each item PASS or FAIL with the place in the text.

| # | Item | Verdict | Evidence |
|---|---|---|---|
| 0 | Something worth showing | PASS | A child's geometric-probability question is a three-loop Feynman diagram (Theorem 1, Figure 2, Table 1); the same route gives the triangle's 1/4 back. |
| 1 | A question first | PASS | Section 1 opens with the problem (Figure 1) and "Stop and try it before reading on" on the triangle case. |
| 2 | Concrete before abstract | PASS | The triangle's 1/4 and Zare's polytope before Theorem 1; the triangle's Gram matrix and Heron before the general change of variables; "The triangle again" works the whole identity for n = 2; Table 1 lists n = 2, 3, 4. |
| 3 | Motivated definitions | PASS | U described in words with Figure 2 before the theorem; G arises as the Gram matrix of the vertices; L_t comes out of identity (4); Gamma_n is introduced by Siegel's integral, read as the matrix version of the integral of e^{-lambda g}. |
| 4 | Rediscoverable proofs | PASS | Each step is the natural next move: uniform pieces to exponential ones (scale invariance), lengths to the Gram matrix (Schoenberg), Gaussianise the weight (Lemma 1, proved by completing the square), integrate the Gaussian over the cone, read off the spanning trees. |
| 5 | Core ideas drawn | PASS | Figure 1 (pieces to edges), Figure 2 (K3 and K4 as vacuum diagrams with a spanning tree and its omitted edges), Figure 3 (the hinge behind the first numerical method). |
| 6 | Formulas parsed | PASS | (3) read in words ("integrate over all simplices ... with weight ..."); Lemma 1 called a Gaussian in disguise; (5) read as the matrix version of a one-variable integral; Theorem 1 read as a Feynman diagram in Section 4 and Corollary 1. |
| 7 | Honest simplification | PASS | Section 5 describes the two numerical methods without proofs and says so; the integer-relation search is called "weak evidence at this precision"; the quoted analytic inputs are listed in the Verification paragraph; no "obviously" or "clearly" (grep). |
| 8 | A person talking | PASS | Calm explanatory voice, varied sentences; house-voice checker: one HARD finding, a false positive in the preamble (`decorations.pathreplacing` / `\newtheorem`), no em-dashes. |
| 9 | A reason to care | PASS | Section 1: no closed form, and the note "shows instead why the number is hard, by identifying it with an object physicists have studied for decades". |
