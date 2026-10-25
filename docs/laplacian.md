# The finite object in Laplacian form

**Status:** exact mathematical reformulation. The graph/FK correspondence and
spectral identities below have not been formalized in the repository's Lean
modules. The existing Lean code defines the concrete wired spin polynomials
and proves finite-root convergence under explicit hypotheses.

## Wired graph and operator

Fix integers $q\ge1$, $d\ge1$, and $R\ge1$. Identify all boundary
vertices of the nearest-neighbor box $[-R,R]^d$ to one vertex $b$, keeping
the center $o$ distinct. Write the resulting **edge-labelled multigraph** as
$G_R^w=(V_R,E_R)$. Every original edge retains its own label, including
parallel edges and loops created by the boundary identification.

For $A\subseteq E_R$, orient its edges arbitrarily and let $B_A$ be the
real vertex-edge incidence matrix. A loop has a zero column. Define

$$
\boxed{
L_A=B_AB_A^{\mathsf T}
=\sum_{e=\{i,j\}\in A}(e_i-e_j)(e_i-e_j)^{\mathsf T},
\qquad \kappa_A=\dim\ker L_A.
}
$$

This is the finite **graph Laplacian**. Its quadratic form is

$$
f^{\mathsf T}L_Af=\sum_{\{i,j\}\in A}(f_i-f_j)^2.
$$

Consequently $\ker L_A$ consists precisely of functions constant on each
connected component of $(V_R,A)$, including isolated vertices. Thus
$\kappa_A$ is its number of components.

## Connectivity from the kernel and heat semigroup

Put $h=e_o-e_b$, and let $\Pi_A$ be the orthogonal projection onto
$\ker L_A$. Then

$$
\boxed{
\chi_A:=\mathbf1\{\Pi_Ah=0\}
=\mathbf1\{o\leftrightarrow b\text{ in }A\},
\qquad
\Pi_A=\lim_{t\to\infty}e^{-tL_A}.
}
$$

Indeed, the kernel is spanned by the indicator vectors of the components.
The vector $h$ is orthogonal to all these indicators exactly when $o$
and $b$ belong to the same component. The heat-semigroup limit follows
from the spectral decomposition of the finite symmetric positive-semidefinite
matrix $L_A$: positive eigenvalues decay, while zero eigenvalues remain.
More explicitly,

$$
\lim_{t\to\infty}h^{\mathsf T}e^{-tL_A}h
=\|\Pi_Ah\|^2
=\begin{cases}
0,&o\leftrightarrow b,\\[2pt]
|\mathcal C_o|^{-1}+|\mathcal C_b|^{-1},&o\not\leftrightarrow b.
\end{cases}
$$

Here $\mathcal C_o,\mathcal C_b$ denote the two distinct components in
the second case.

## Partition polynomial and finite root

For the activity $v=p/(1-p)$, with $0\le p<1$, define

$$
\boxed{
Z_R(q,v)=\sum_{A\subseteq E_R}q^{\kappa_A-1}v^{|A|},
\qquad
C_R(q,v)=\sum_{A\subseteq E_R}\chi_Aq^{\kappa_A-1}v^{|A|}.
}
$$

The exponent $\kappa_A-1$ fixes the boundary component to one color;
the other components each have $q$ choices. For integer $q\ge1$,
both expressions lie in $\mathbb Z[v]$, and $Z_R(q,v)>0$ for
$v\ge0$. Their ratio is the wired FK connection probability.

The finite crossing equation is therefore

$$
\boxed{
F_R(q,v):=(R+1)C_R(q,v)-Z_R(q,v)
=\sum_{A\subseteq E_R}
\bigl((R+1)\chi_A-1\bigr)q^{\dim\ker L_A-1}v^{|A|},
\quad F_R(q,v_R)=0,
\quad p_R=\frac{v_R}{1+v_R}.
}
$$

This is the same finite polynomial used in the
[Siegel–G formulation](siegel-g.md). The spectral expression specifies the
coefficients of the finite polynomial; it is not a claim that the FK
partition polynomial is a single determinant such as $\det(I+vL)$, or
that the critical probability is one Laplacian eigenvalue. Nor is this a
continuum Laplacian or a Laplace-transform representation.

## Relation to the implemented spin object

Let $Z_{R,0}(q,v)$ be the wired spin sum with the center additionally fixed
to the boundary color. Expanding the edge factors selects $A\subseteq E_R$
and forces each component to have a constant color. When $o\leftrightarrow
b$, there are $q^{\kappa_A-1}$ compatible colorings. Otherwise there
are $q^{\kappa_A-2}$ center-fixed colorings, since two distinct components
have fixed colors. Hence, for $q>1$,

$$
qZ_{R,0}-Z_R=(q-1)C_R,
\qquad
\frac{C_R}{Z_R}
=\frac{qZ_{R,0}/Z_R-1}{q-1},
$$
$$
F_R(q,v_R)=0
\iff (R+1)qZ_{R,0}(q,v_R)=(R+q)Z_R(q,v_R).
$$

The last equation is exactly the activity-coordinate equation in
[`wiredMagnetization_root_iff`](../IsingCriticality/FinitePartition.lean).
The expansion identifying the spin observable with FK connectivity is an
additional mathematical argument, not a Lean theorem currently supplied by
that file.

- At $q=1$, the direct Laplacian/FK definition $C_R/Z_R$ remains valid.
  The spin expression divided by $q-1$ cannot be used; the C++ spin
  enumerator supports $q=2,3$.
- Each boundary-to-boundary edge becomes a loop and contributes the same
  factor $1+v$ to both $Z_R$ and $C_R$. The C++ implementation
  omits these common factors, preserving normalized probabilities and positive
  roots. The Lean spin polynomial retains the original edges.
- Parallel edges must remain distinct. Collapsing them to a single edge with
  the same activity changes the polynomial.
- The alternative weight $q^{\kappa_A}$ multiplies both polynomials by
  $q$, preserving their ratio and root equation, but is not the
  boundary-fixed normalization used above.

The passage $p_R\to p_c(q,d)$ additionally requires the finite-volume
monotonicity, root, decay, and physical-identification inputs described in
[formal scope](formal-scope.md). The Laplacian reformulation alone does not
discharge those inputs or identify a closed approximation with the limit.
