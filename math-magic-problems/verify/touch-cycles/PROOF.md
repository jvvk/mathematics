# A computer-assisted solution of Friedman problem 24

27 September 2026

**Theorem.** There is no nonempty finite placement of three colours of king on
the integer square grid with cyclic neighbour counts
\((a,b,c)=(1,3,6),(1,4,5),(1,6,3)\), or \((2,3,4)\).
Thus the three cases (1,3,6), (1,6,3) and (2,3,4) listed in
[Friedman's problem 24](https://erich-friedman.github.io/mathmagic/unsolved.html) have negative answers
under the [March 2015 rules](https://erich-friedman.github.io/mathmagic/0315.html), and so does the
further case (1,4,5).

This is a computer-assisted proof. Its finite logical refutations are supplied
as explicit certificates and verified by a small Python checker. The argument
below reduces *arbitrarily large finite arrangements* to those finite formulas;
it is not an inference from searching boards up to some size. Independent
external review and any priority claim remain separate from this verification.

## 1. Definitions

At most one king occupies each point of \(\mathbb Z^2\). Two points are adjacent
when their difference is in \(\{-1,0,1\}^2\setminus\{(0,0)\}\).
An A must have exactly \(a\) B neighbours, a B exactly \(b\) C neighbours,
and a C exactly \(c\) A neighbours. Same-colour neighbours and the other
cross-colour counts are unrestricted. No connectedness assumption is made.
The arrangement is finite and nonempty. Since all prescribed counts are
positive, it then contains all three colours.

## 2. Reduction to a neighbourhood of an extreme king

Fix \(n=(n_x,n_y)\), either \((0,1)\) or \((1,1)\). In any nonempty finite
arrangement choose an occupied point maximizing the pair
\((n_xx+n_yy,x)\) in lexicographic order. Translate it to \((0,0)\).
Every occupied point now belongs to

\[
H_n=\{(x,y):n_xx+n_yy<0\}\;\cup\;
\{(x,y):n_xx+n_yy=0,\ x\leq0\}.
\]

For a positive integer \(r\), consider only
\(D_{n,r}=H_n\cap[-r,r]^2\cap\mathbb Z^2\).
Require at most one colour per point and require the origin to be occupied.
Impose the prescribed neighbour counts only at points satisfying
\(\max(|x|,|y|)<r\). **Do not impose neighbour counts on the outer square
boundary.** Those boundary kings may have further neighbours outside the patch.

Every neighbour of a constrained point lies inside the square. A neighbour
missing from \(D_{n,r}\) is outside \(H_n\), hence is necessarily empty.
Therefore restricting an actual arrangement to \(D_{n,r}\) satisfies all these
patch conditions. If this relaxed patch problem is impossible, so is every
finite arrangement of the corresponding type. This proves the reduction.

## 3. Exact propositional encoding

For each point \(p\in D_{n,r}\) and colour \(i\in\{0,1,2\}\), introduce
\(X_{p,i}\), indicating A, B, and C respectively. Empty means all three
variables are false. The next colour is \(i+1\pmod3\).

For each pair \(i\ne j\), include
\(\neg X_{p,i}\lor\neg X_{p,j}\), and include the origin clause
\(X_{0,0}\lor X_{0,1}\lor X_{0,2}\).

For an interior point \(p\), let \(Y_1,\ldots,Y_m\) be the next-colour
variables at its neighbours in \(D_{n,r}\), and let \(k\) be its required
count. The implication \(X_{p,i}\Rightarrow\sum_jY_j=k\) is encoded directly:

* For every subset \(U\subseteq\{1,\ldots,m\}\) of size \(k+1\), include
  \(\neg X_{p,i}\lor\bigvee_{j\in U}\neg Y_j\). These forbid too many.
* For every subset \(U\) of size \(m-k+1\), include
  \(\neg X_{p,i}\lor\bigvee_{j\in U}Y_j\). These forbid too few.
* If \(m<k\), include just \(\neg X_{p,i}\).

There are no auxiliary variables. Points are ordered by increasing y, then
increasing x; colour \(i\) at the zero-based point index \(j\) has variable
number \(3j+i+1\). `certify.py` implements this clause listing in `build`.

## 4. Certified contradictions

The supplied formulas have the following parameters. The last column counts
certificate additions, including the final empty clause.

| Counts | Supporting normal n | Radius r | Points | Variables | Clauses | Additions |
|---|---|---:|---:|---:|---:|---:|
| (1,3,6) | (0,1) | 6 | 85 | 255 | 10,025 | 72 |
| (1,4,5) | (0,1) | 4 | 41 | 123 | 4,512 | 24 |
| (1,6,3) | (0,1) | 6 | 85 | 255 | 10,025 | 37 |
| (2,3,4) | (1,1) | 8 | 145 | 435 | 26,362 | 586 |

For each row, `certificates/a-b-c.cnf` contains the input formula,
`a-b-c.drup` its refutation, and `a-b-c.json` the parameters. Glucose generated
the refutations; verification requires neither Glucose nor any other solver.

Each certificate line lists a clause followed by zero. To check an addition
\(C\), the verifier temporarily assumes the negation of every literal in
\(C\), then repeatedly applies unit propagation to the existing clauses.
It accepts the addition only if this produces a contradiction. Thus every
accepted clause is a logical consequence of the previous formula. Inductively
all additions follow from the original formula. Acceptance of the final empty
clause proves that formula unsatisfiable.

`verify_drup.py` verifies every addition, requires a verified empty clause,
and also checks that each input formula is exactly the encoding reconstructed
from its geometric parameters. It uses only the Python standard library.
All four certificates pass. Applying the reduction in section 2 proves the
theorem. **QED.**

## 5. Reproduction and additional checks

From this directory, run:

```sh
python3 -B verify_drup.py
```

On the machine used here this took about 22 seconds, predominantly for the
fourth certificate. To regenerate the certificates, install `python-sat` and
run `python3 -B certify.py` before running the checker.

An independently written Z3 formulation uses one integer in {0,1,2,3} per
point rather than the direct cardinality clauses. It also reports UNSAT for
all four exact patches in the table. Reproduce with
`python3 -B independent_z3.py` (requires `z3-solver`).

Positive finite controls for (1,1,6), (1,3,4), (1,6,2), and (2,3,3) were found
by a CP-SAT model and accepted by `check.py`, which counts actual neighbours
without importing a solver. Their coordinates are in `controls.json`.
The refutation checker also rejects an unjustified empty clause for each
original formula: none is already contradictory by initial unit propagation.

The supporting-line choice matters: for (2,3,4), the diagonal patch at radius
7 is satisfiable, while the radius-8 patch is not. Satisfiable relaxed patches
need not extend to full arrangements. Earlier bounded-board search results
in `boxes.jsonl` are exploratory evidence and are not needed for the proof.

## References

Erich Friedman, [Problem of the Month, March 2015](https://erich-friedman.github.io/mathmagic/0315.html),
three letters with king adjacency;
[Unsolved Problems from Math Magic, problem 24](https://erich-friedman.github.io/mathmagic/unsolved.html),
accessed 27 September 2026.
