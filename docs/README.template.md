# ISING_CRITICALITY

[![CI](https://github.com/randogelist/ISING_CRITICALITY/actions/workflows/verify.yml/badge.svg)](https://github.com/randogelist/ISING_CRITICALITY/actions/workflows/verify.yml)

Critical FK bond probability on the hypercubic lattice: **q=1** percolation, **q=2** Ising, **q=3** Potts.

```math
\boxed{\displaystyle
p_c(q,d)=\inf\bigl\lbrace p\in[0,1]:\theta_{q,d}(p)>0\bigr\rbrace,
\qquad p=\frac{v}{1+v}
}
```

**Graph-Laplacian form.** On the boundary-wired box, let $`o,b`$ denote its center and wired boundary, and $`B_A`$ the incidence matrix of open edges $`A`$.

```math
\begin{gathered}
L_A=B_AB_A^{\mathsf T},\qquad
\kappa_A=\dim\ker L_A,\qquad
\Pi_A=\mathrm{proj}_{\ker L_A},\\[4pt]
\boxed{\displaystyle
\mathcal F_R(v)=
\sum_{A\subseteq E_R}
\left[(R+1)\mathbf{1}_{\lbrace \Pi_A(e_o-e_b)=0\rbrace}-1\right]
q^{\kappa_A-1}v^{|A|}}
\end{gathered}
```

**Siegel–G form.** An admissible rational anchor $`u_R`$ selects an algebraic Siegel $`G`$-function $`\Phi_{R,u_R}`$:

```math
\boxed{\begin{gathered}
\mathcal F_R\!\left(\Phi_{R,u_R}(z)\right)
  =(1-z)\mathcal F_R(u_R),\\
\Phi_{R,u_R}(0)=u_R,\qquad
\Phi_{R,u_R}(1)=v_R.
\end{gathered}}
```

```math
\mathcal H_{\mathrm{FK}}\quad\Longrightarrow\quad
\boxed{\displaystyle
p_c(q,d)=p_{c,\mathrm{G\_FUNCTIONREPR}}(q,d)
=\lim_{R\to\infty}
\frac{\Phi_{R,u_R}(1)}{1+\Phi_{R,u_R}(1)}
}
```

$`\mathcal H_{\mathrm{FK}}`$ comprises the finite-root convergence and physical-identification hypotheses. Each finite branch is a $`G`$-function; no such classification is asserted for the limit. [Laplacian derivation](docs/laplacian.md) · [Siegel–G derivation](docs/siegel-g.md). These reformulations are mathematical documentation; their additional identities are not yet Lean-formalized.

<!-- ORIGINAL_TABLE -->

PCD uses GP4 for q=1,2 and the square-loop formula for q=3; d=2 is exact. Literature values use inverse quoted-error-squared weights. Δ = 100(PCD/literature − 1); — means unavailable. The average is descriptive, with no pooled accuracy claim.

[Sources, weights & computation](literature/) · [All numerical estimators](docs/numerical-comparison.md) · [Irrationality: proofs & scope](docs/irrationality.md) · [Reproduce](docs/setup.md)

Lean certifies formula digits and conditional convergence; equality with physical p_c remains open. [Proof scope](docs/formal-scope.md). Lean verification runs exclusively in CI.
