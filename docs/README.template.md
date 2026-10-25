# ISING_CRITICALITY

[![Verify Lean and C++](https://github.com/randogelist/ISING_CRITICALITY/actions/workflows/verify.yml/badge.svg)](https://github.com/randogelist/ISING_CRITICALITY/actions/workflows/verify.yml)

A Lean 4 and C++ research project for the critical bond probability of the nearest-neighbor ferromagnetic Fortuin–Kasteleyn model on the hypercubic lattice:

$$p_c(q,d)=\inf\{p\in[0,1]:\theta_{q,d}(p)>0\},\qquad p=\frac{v}{1+v}.$$

Here **q=1** is bond percolation, **q=2** is FK–Ising, and **q=3** is the three-state Potts model. The exact finite object is the partition polynomial

$$Z_G(q,v)=\sum_{A\subseteq E}q^{k(A)}v^{|A|},\qquad (R+1)C_R(q,v_R)=Z_R(q,v_R),\qquad r_R=\frac{v_R}{1+v_R},$$

where $C_R$ restricts the wired-box sum to configurations connecting the center to the boundary. The numerical finite-box implementation uses the equivalent integer-spin representation for q=2,3.

**Proof scope:** The Lean sources cover finite partition identities, the odds conversion, exact rounding of the approximation formulas, and a finite-root convergence theorem **under explicitly stated monotonicity, decay and threshold assumptions**. The FK infinite-volume facts and equality of the approximation formulas with physical $p_c$ remain open in this repository. Eight certified decimals of a formula do not certify eight physical decimals. See [formal scope](docs/formal-scope.md). **[CI verified](https://github.com/randogelist/ISING_CRITICALITY/actions/runs/40174368336):** all 17 Lean modules compiled, the axiom audit passed with standard axioms only, and the C++ tests and numerical table reproduction passed for source commit `6938db28d6b01da3dd1037a58d42bdf00b7dda3d`. See the [CI proof receipt](audit/build-receipt.json).

## Numerical front page

Original PCD approximation: GP4 for q=1,2; the attached square-loop formula for q=3. The d=2 rows use the known exact square-lattice threshold. Relative difference is $100(\widehat p/p_{\rm ref}-1)$. Displayed reference uncertainties are published numerical uncertainties, not mathematical bounds. **— means no independent benchmark was verified**, not agreement.

<!-- ORIGINAL_TABLE -->

<!-- PADE_SUMMARY -->

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
