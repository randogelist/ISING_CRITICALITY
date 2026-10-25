# ISING_CRITICALITY

[![CI](https://github.com/randogelist/ISING_CRITICALITY/actions/workflows/verify.yml/badge.svg)](https://github.com/randogelist/ISING_CRITICALITY/actions/workflows/verify.yml)

Critical FK bond probability on the hypercubic lattice: **q=1** percolation, **q=2** Ising, **q=3** Potts.

$$p_c(q,d)=\inf\{p\in[0,1]:\theta_{q,d}(p)>0\},\qquad p=\frac{v}{1+v}.$$

<!-- ORIGINAL_TABLE -->

PCD uses GP4 for q=1,2 and the square-loop formula for q=3; d=2 is exact. Literature values use inverse quoted-error-squared weights. Δ = 100(PCD/literature − 1); — means unavailable. The average is descriptive, with no pooled accuracy claim.

[Sources, weights & computation](literature/) · [All numerical estimators](docs/numerical-comparison.md) · [Reproduce](docs/setup.md)

Lean certifies formula digits and conditional convergence; equality with physical p_c remains open. [Proof scope](docs/formal-scope.md). Lean verification runs exclusively in CI.
