# Formal scope

Lean compilation and axiom auditing are restricted to GitHub Actions. The first
CI validation of this repository is pending; earlier local receipts do not establish
a CI pass. The statements below describe the source-level proof scope and preserve
the inherited certificate separately from the open physical identification.

## Exact finite object

For a finite graph with each undirected edge listed once, the project defines

\[
Z_G(q,v)=\sum_{\sigma:V\to\{0,\ldots,q-1\}}
\prod_{\{i,j\}\in E}\left(1+v\,\mathbf1_{\sigma_i=\sigma_j}\right)
\in\mathbb N[v].
\]

`IsingCriticality/FinitePartition.lean` defines this natural-coefficient
polynomial, its real evaluation, and the actual positively oriented
nearest-neighbor edge set of a finite hypercubic box. The basic graph has
free boundary conditions; no periodic wrapping is introduced. Separate
`wiredStates` explicitly fixes every boundary spin to color zero.

The following are finite, exact identities:

- The polynomial evaluates to the finite spin partition sum.
- Substituting \(v=e^K-1\) gives one Boltzmann factor \(e^K\) for each
  agreeing edge.
- The coordinate \(p=v/(1+v)\) maps \([0,\infty)\) strictly increasingly
  into \([0,1)\), with inverse \(v=p/(1-p)\).
- Consequently \(p=1-e^{-K}\) for the Potts coupling. An Ising coupling
  in \(-K_I\sum s_i s_j\) corresponds to \(K=2K_I\).
- The probability-coordinate spin sum satisfies
  \(\widetilde Z_G(q,p)=(1-p)^{|E|}Z_G(q,p/(1-p))\).
- The finite partition sum is positive for integer \(q>0\) and \(v\ge0\).

For the actual box \(\{0,\ldots,2R\}^d\), the wired-spin construction uses
the center \((R,\ldots,R)\) and fixes every spin having a coordinate zero
or \(2R\) to color zero. Its exact observable is

\[
W_R(p)=\frac{q Z_{R,0}(p)/Z_R(p)-1}{q-1},\qquad
Z_R(p)=\sum_{\sigma\text{ boundary}=0}
\prod_{\{i,j\}\in E}\begin{cases}1&\sigma_i=\sigma_j,\\1-p&\sigma_i\ne\sigma_j.\end{cases}
\]

Here \(Z_{R,0}\) additionally restricts the center spin to zero. This
polynomial definition works at \(p=1\). The denominator is proved positive
for \(q>0\) and \(p\le1\), using the constant-zero assignment. The
activity-coordinate and probability-coordinate observables are proved
equal for \(p<1\).

For \(q>1\), the target equation \(W_R=1/(R+1)\) is equivalent, in
activity coordinates, to the exact polynomial equation

\[
(R+1)q\,Z_{R,0}(v)=(R+q)Z_R(v).
\]

The normalized spin observable has not yet been formally identified with
FK center-to-boundary connectivity by an Edwards–Sokal correspondence.
Its mathematical definition and algebraic identities are nevertheless
concrete and independent of any supplied decimal benchmark.

Expanding the probability-coordinate product selects subsets of open edges
and forces their endpoint colors to agree. The separate combinatorial
identity that the number of compatible colorings is \(q^{k(A)}\) is not
proved in this module. Accordingly, the module does not claim to have
formalized the complete random-cluster representation or an infinite-volume
limit.

## Inherited square-loop certificate

The attachment `PCD_Q3_8DIGIT_LEAN_v0_1_2_FIX2` contains genuine interval
proofs for a specific analytic approximation. Define

\[
r_d=2^{1/d},\quad
v_B(d)=\frac{2(r_d-1)}{2-r_d},\quad
t_B(d)=\frac{2(r_d-1)}{4-r_d},
\]
\[
\Delta_d=\frac{d-1}{2}\log(3/2)
\left(\frac{t_B(d)}{t_B(2)}\right)^4,\qquad
p_\square(d,3)=\frac{v_B(d)e^{\Delta_d}}{1+v_B(d)e^{\Delta_d}}.
\]

The definitions use natural-number `d`; in the original source `d-1` is
natural subtraction. All certified dimensions are at least three, so there
is no discrepancy with the displayed formula on the certified domain.

The source proves rational bounds for roots, logarithms and exponentials,
then propagates them through the formula to show nearest rounding to eight
decimal places for \(d=3,\ldots,11\). These are certified digits of
\(p_\square\), not certified digits of the physical critical probability.
No sampled numerical values are used as axioms.

The original Windows runner assumes a specific external Mathlib cache and
Lean binary; it is preserved as provenance, not used as the portable build.
The GitHub Actions build pins its own Lean/Mathlib environment. Its compiler
results and axiom audits are authoritative; an old expected-output file is
not evidence of a new successful run.

## Infinite-volume identification remains open

The intended physical object is

\[
p_c(d,q)=\inf\{p\in[0,1]:\theta_{d,q}(p)>0\},
\]

where \(\theta_{d,q}\) is the relevant infinite-volume random-cluster
percolation probability, with the infinite-volume measure and boundary
convention specified. Defining an unrelated symbol by this infimum does
not identify it with the square-loop formula.

A finite-volume route uses the concrete wired-spin observable above and
roots \(W_R(p_R)=1/(R+1)\). The repository indexes \(R=n+1\), so the target
is \(1/(n+2)\). To establish convergence to the physical \(p_c\), one must
prove, for the actual lattice measures:

1. Existence of each root and the required monotonicity in \(p\).
2. The relation between \(W_n\) and the specified infinite-volume measure.
3. Sufficient decay below \(p_c\), for example an
   \(O((n+2)^{-2})\) bound or exponential decay.
4. A positive limiting one-arm probability above \(p_c\).

`IsingCriticality/Identification.lean` formalizes the order-theoretic
convergence argument with these hypotheses explicitly exposed; it does
not prove the missing lattice estimates merely by packaging them as
assumptions. These physical inputs are not supplied by the attachment or
the finite polynomial identities. Even such a convergent exact construction would
still require a separate proof or controlled error estimate to identify a
particular closed square-loop expression with its limit.

Benchmark agreement is assessed numerically with explicit source
conventions and relative errors. It does not discharge these open proofs.
