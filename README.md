# ISING_CRITICALITY

[![CI](https://github.com/randogelist/ISING_CRITICALITY/actions/workflows/verify.yml/badge.svg)](https://github.com/randogelist/ISING_CRITICALITY/actions/workflows/verify.yml)

Critical FK bond probability on the hypercubic lattice: **q=1** percolation, **q=2** Ising, **q=3** Potts.

$$p_c(q,d)=\inf\{p\in[0,1]:\theta_{q,d}(p)>0\},\qquad p=\frac{v}{1+v}.$$

| q | d | PCD | Weighted literature | Δ (%) |
|---:|---:|---:|---:|---:|
| 1 | 2 | 0.50000000 | 0.5000000000 | 0 |
| 1 | 3 | 0.25024000 | 0.2488118350 | +0.57399 |
| 1 | 4 | 0.15666092 | 0.1601312200 | -2.16716 |
| 1 | 5 | 0.11664888 | 0.1181714500 | -1.28844 |
| 1 | 6 | 0.09365356 | 0.0942016500 | -0.58182 |
| 1 | 7 | 0.07847711 | 0.0786752300 | -0.25183 |
| 1 | 8 | 0.06763062 | 0.0677084181 | -0.11491 |
| 1 | 9 | 0.05946233 | 0.0594960034 | -0.05660 |
| 1 | 10 | 0.05307663 | 0.0530925842 | -0.03004 |
| 1 | 11 | 0.04794152 | 0.0479496837 | -0.01703 |
| 2 | 2 | 0.58578644 | 0.5857864376 | 0 |
| 2 | 3 | 0.35742444 | 0.3580912456 | -0.18621 |
| 2 | 4 | 0.25771005 | 0.2587279411 | -0.39342 |
| 2 | 5 | 0.20336817 | 0.2037403589 | -0.18268 |
| 2 | 6 | 0.16842847 | 0.1685601873 | -0.07814 |
| 2 | 7 | 0.14389230 | 0.1439433335 | -0.03545 |
| 2 | 8 | 0.12565949 | 0.1256810163 | -0.01713 |
| 2 | 9 | 0.11155704 | 0.1115669625 | -0.00890 |
| 2 | 10 | 0.10031559 | 0.1003198790 | -0.00427 |
| 2 | 11 | 0.09114064 | — | — |
| 3 | 2 | 0.63397460 | 0.6339745962 | 0 |
| 3 | 3 | 0.42473310 | 0.4233762468 | +0.32048 |
| 3 | 4 | 0.32233576 | — | — |
| 3 | 5 | 0.26065061 | — | — |
| 3 | 6 | 0.21906526 | — | — |
| 3 | 7 | 0.18902489 | — | — |
| 3 | 8 | 0.16627150 | — | — |
| 3 | 9 | 0.14842644 | — | — |
| 3 | 10 | 0.13405008 | — | — |
| 3 | 11 | 0.12221782 | — | — |

PCD uses GP4 for q=1,2 and the square-loop formula for q=3; d=2 is exact. Literature values use inverse quoted-error-squared weights. Δ = 100(PCD/literature − 1); — means unavailable. The average is descriptive, with no pooled accuracy claim.

[Sources, weights & computation](literature/) · [All numerical estimators](docs/numerical-comparison.md) · [Irrationality: proofs & scope](docs/irrationality.md) · [Reproduce](docs/setup.md)

Lean certifies formula digits and conditional convergence; equality with physical p_c remains open. [Proof scope](docs/formal-scope.md). Lean verification runs exclusively in CI.
