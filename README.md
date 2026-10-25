# ISING_CRITICALITY

[![Verify Lean and C++](https://github.com/randogelist/ISING_CRITICALITY/actions/workflows/verify.yml/badge.svg)](https://github.com/randogelist/ISING_CRITICALITY/actions/workflows/verify.yml)

A Lean 4 and C++ research project for the critical bond probability of the nearest-neighbor ferromagnetic Fortuin–Kasteleyn model on the hypercubic lattice:

$$p_c(q,d)=\inf\{p\in[0,1]:\theta_{q,d}(p)>0\},\qquad p=\frac{v}{1+v}.$$

Here **q=1** is bond percolation, **q=2** is FK–Ising, and **q=3** is the three-state Potts model. The exact finite object is the partition polynomial

$$Z_G(q,v)=\sum_{A\subseteq E}q^{k(A)}v^{|A|},\qquad (R+1)C_R(q,v_R)=Z_R(q,v_R),\qquad r_R=\frac{v_R}{1+v_R},$$

where $C_R$ restricts the wired-box sum to configurations connecting the center to the boundary. The numerical finite-box implementation uses the equivalent integer-spin representation for q=2,3.

**Proof scope:** The Lean sources cover finite partition identities, the odds conversion, exact rounding of the approximation formulas, and a finite-root convergence theorem **under explicitly stated monotonicity, decay and threshold assumptions**. The FK infinite-volume facts and equality of the approximation formulas with physical $p_c$ remain open in this repository. Eight certified decimals of a formula do not certify eight physical decimals. See [formal scope](docs/formal-scope.md). **CI validation is pending** until the linked GitHub Actions run passes; earlier local receipts are historical evidence only.

## Numerical front page

Original PCD approximation: GP4 for q=1,2; the attached square-loop formula for q=3. The d=2 rows use the known exact square-lattice threshold. Relative difference is $100(\widehat p/p_{\rm ref}-1)$. Displayed reference uncertainties are published numerical uncertainties, not mathematical bounds. **— means no independent benchmark was verified**, not agreement.

| q | d | Original model | Dlog–Padé (Ising) | Published / exact reference | Original difference |
|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 0.50000000 | — | [0.5000000000 (exact)](https://arxiv.org/abs/1006.5073) | 0 (anchor) |
| 1 | 3 | 0.25024000 | — | [0.2488118500 ± 1e-07](https://arxiv.org/html/1310.5399v2) | +0.57399% |
| 1 | 4 | 0.15666092 | — | [0.1601312200 ± 6e-08](https://arxiv.org/pdf/1806.08067) | -2.16716% |
| 1 | 5 | 0.11664888 | — | [0.1181714500 ± 3e-08](https://arxiv.org/pdf/1806.08067) | -1.28844% |
| 1 | 6 | 0.09365356 | — | [0.0942016500 ± 2e-08](https://arxiv.org/pdf/1806.08067) | -0.58182% |
| 1 | 7 | 0.07847711 | — | [0.0786752300 ± 2e-09](https://arxiv.org/pdf/1806.08067) | -0.25183% |
| 1 | 8 | 0.06763062 | — | [0.0677084181 ± 3e-10](https://arxiv.org/pdf/1806.08067) | -0.11491% |
| 1 | 9 | 0.05946233 | — | [0.0594960034 ± 1e-10](https://arxiv.org/pdf/1806.08067) | -0.05660% |
| 1 | 10 | 0.05307663 | — | [0.0530925842 ± 2e-10](https://arxiv.org/pdf/1806.08067) | -0.03004% |
| 1 | 11 | 0.04794152 | — | [0.0479496837 ± 8e-11](https://arxiv.org/pdf/1806.08067) | -0.01703% |
| 2 | 2 | 0.58578644 | — | [0.5857864376 (exact)](https://arxiv.org/abs/1006.5073) | 0 (anchor) |
| 2 | 3 | 0.35742444 | 0.3581028414 | [0.3580913351 ± 6e-09](https://arxiv.org/abs/1806.03558) | -0.18624% |
| 2 | 4 | 0.25771005 | 0.2588485281 | [0.2587279411 ± 1e-08](https://arxiv.org/pdf/2209.05292) | -0.39342% |
| 2 | 5 | 0.20336817 | 0.2037381381 | [0.2037403557 ± 3e-08](https://arxiv.org/pdf/1502.07613) | -0.18268% |
| 2 | 6 | 0.16842847 | 0.1685804187 | [0.1685602148 ± 5e-07](https://arxiv.org/pdf/1502.07613) | -0.07816% |
| 2 | 7 | 0.14389230 | 0.1439483714 | [0.1439420444 ± 1e-06](https://arxiv.org/pdf/1502.07613) | -0.03456% |
| 2 | 8 | 0.12565949 | 0.1256826349 | [0.1256810163 ± 2e-06](https://arxiv.org/pdf/1209.3592) | -0.01713% |
| 2 | 9 | 0.11155704 | 0.1115675483 | [0.1115669625 ± 2e-06](https://arxiv.org/pdf/1209.3592) | -0.00890% |
| 2 | 10 | 0.10031559 | 0.1003207833 | [0.1003198790 ± 2e-06](https://arxiv.org/pdf/1209.3592) | -0.00427% |
| 2 | 11 | 0.09114064 | 0.0911433699 | — | — |
| 3 | 2 | 0.63397460 | — | [0.6339745962 (exact)](https://arxiv.org/abs/1006.5073) | 0 (anchor) |
| 3 | 3 | 0.42473310 | — | [0.4233760742 ± 6e-06](https://arxiv.org/pdf/hep-lat/9612008) | +0.32053% |
| 3 | 4 | 0.32233576 | — | — | — |
| 3 | 5 | 0.26065061 | — | — | — |
| 3 | 6 | 0.21906526 | — | — | — |
| 3 | 7 | 0.18902489 | — | — | — |
| 3 | 8 | 0.16627150 | — | — | — |
| 3 | 9 | 0.14842644 | — | — | — |
| 3 | 10 | 0.13405008 | — | — | — |
| 3 | 11 | 0.12221782 | — | — | — |

The order-32 Dlog–Padé calculation for q=2, d=3 gives **0.3581028414**, versus **0.3580913351** (+0.00321%). For d=4,…,11 the table uses the published order-20 susceptibility series. These are extrapolations from published coefficients; no benchmark threshold or critical exponent enters the calculation.

The [full numerical comparison](docs/numerical-comparison.md) includes HJ9, BP12, Dlog–Padé, original source values and uncertainties, and every located alternative benchmark. The high-dimensional series can perform poorly at small d. Inputs are published series coefficients, never the benchmark thresholds. This project does **not** currently match every benchmark to its quoted uncertainty.

## Reproduce

```sh
make test                     # C++ compilation, numerical tests, table reproduction
./build/pcd --q 3 --d 3
./build/pcd --method dlog-pade
./build/pcd --pade-details
./build/pcd --method hj9
./build/pcd --method bp12
./build/pcd --finite 2 2 3    # genuine finite wired-box root, not infinite-volume pc
```

**Lean compilation and axiom auditing run exclusively in [GitHub Actions](https://github.com/randogelist/ISING_CRITICALITY/actions/workflows/verify.yml).** Push a change, open a pull request, or select **Run workflow** there. The runner installs Lean **4.33.0**, retrieves the compatible Mathlib cache pinned to **db584cd6d46c92f209a44c0f1c829460d327499d**, and uploads proof and numerical receipts. The workflow's result and attached receipts establish the status of that commit.

Local work is limited to source edits and C++ numerical checks. On Windows, `run.cmd` runs the numerical workflow and points to CI for Lean. See [setup](docs/setup.md).

## Contents and provenance

- [FinitePartition.lean](IsingCriticality/FinitePartition.lean): exact finite spin polynomials, hypercubic boxes, wired observables, normalization.
- [Identification.lean](IsingCriticality/Identification.lean): infimum threshold and conditional finite-root convergence.
- [Approximants.lean](IsingCriticality/Approximants.lean) and [PCD](PCD): GP4 derivation and q=3 rational/Taylor certificates.
- [C++ engine](numerics/pcd.cpp), [coefficient sources](docs/literature-series.md), and [Dlog–Padé method](docs/dlog-pade.md).
- [Original attachment](vendor/PCD_Q3_8DIGIT_LEAN_v0_1_2_FIX2): preserved source package; the active Q3Defs import list is narrowed for faster Linux compilation, with its definitions and proof bodies unchanged.

Benchmark coverage was reviewed **25 October 2026**: 21 selected benchmarks and 8 alternatives for q=1,2,3 and d=2,…,11. This is a sourced research snapshot, not an exhaustive literature claim. All dimensional extensions concern integer-dimensional hypercubic lattices.
