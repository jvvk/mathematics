# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the original source commit, uncommitted overrides,
and hashes identifying the exact sources in this archive. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean

The root imports the growth limit, density bound, unconditional alternating
asymptotics, joint multiplicity/diagonal reduction, the Remark 3.4 lower
bound (LowerGap.lean) and Lemma 2.1 in both directions (GrowthForward.lean). The first command
retrieves the pinned dependency caches; the second compiles the local proofs;
the last prints the theorem statements and their axiom dependencies.

Stanley.beta is the actual joint permutation count. Its scaled character
inner-product identity and Cauchy-Schwarz inequality are unconditional.
Stanley.exists_diagonal_maximum proves a maximum occurs on the diagonal;
Stanley.gessel_bound_iff_diagonal reduces Gessel's conjectural bound to the
diagonal entries. It does not assert that the conjecture holds.
MultiplicityChecks.lean contains kernel-checked boundary and strict-inequality
examples; these use no native_decide. The larger f-values in the original
project's separate Values.lean are not included in this package.

The source graph was freshly compiled in an isolated build with the original
project cache excluded. See build-validation.log and axiom-validation.txt.
The checked general theorems use only propext, Classical.choice and Quot.sound.
No assertion that the dominance-interval conjecture is proved is made here.

Lemma 2.1 (2026-10-08): Stanley.Growth.mem_pairs_iff_words states that (S,T)
occurs iff two lattice row words of equal content have ascent sets S and T.
The backward direction is Growth.lean; the converse builds the forward growth
diagram of a permutation (Fomin's forward local rule) and shows it satisfies
the backward rule at every cell. No insertion algorithm is used.
Stanley.density_gap_lower is the bound 1 - f(n)/4^(n-1) >= (2^(n-1)-1)/4^(n-1).

Rate (2026-10-08, second update): Stanley.DensitySharp.density_ratio proves
1 - f(n)/4^(n-1) <= 6 e^(-n/150) for every n >= 1, the Theorem 1.1 now stated in the paper
(Density.lean's e^(-n/20000) version is kept). Stanley.f_add_three_pow_le proves
f(n) <= 4^(n-1) - 3^(n-1) + 1 from the consecutive-integer obstruction
(Stanley.not_mem_pairs_block), and Stanley.density_gap_lower_three is the ratio form in Remark 3.4.

Necessity (2026-10-08, third update): Stanley.Alt.beta_pos_implies_cross_dominance
(DominanceNecessity.lean, with Contingency.lean and MatrixCriterion.lean) proves that an occurring
pair satisfies both Gale-Ryser cross-dominance conditions, the necessary direction of Conjecture 5.1.

Theorem 3.6 and Corollary 3.7 (2026-10-08, fourth update): GaleRyserRate.lean. Stanley.Alt.grBad n
is the set of pairs violating (3.2). Stanley.Alt.gr_rate proves
(3^(n-1)-1)/4^(n-1) <= P_n <= (4n^3 + 2^(m-1) C(n,m)^2)(3/4)^(n-1) + 4n^m/2^n with
m = clog2(n^2) + 1, and P_n <= 1 - f(n)/4^(n-1); Stanley.Alt.gr_rate_asymp proves
(3/4)^(n+1) <= P_n <= (3/4)^(n - C log^2 n) for n >= 2 with an explicit C. Stanley.Alt.cor_rate
is Corollary 3.7: if (3.2) is sufficient, then 1 - f(n)/4^(n-1) = P_n. BlockObstruction.lean now
exposes the obstruction pairs as Stanley.blockPairs (Stanley.card_blockPairs), which both the
lower bound of Remark 3.4 and that of Theorem 3.6 use.
