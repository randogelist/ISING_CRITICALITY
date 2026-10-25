# Ising susceptibility estimators for dimensions 3–11

The optional `dlog-pade` method uses the published coefficients of the reduced susceptibility
$\chi(v)=\sum_n c_n v^n$, with $v=\tanh K$, then transforms the estimated singularity by
$p=2v/(1+v)$. It takes neither a benchmark critical coupling nor a critical exponent as input.

The integer data are in [ising3d_susceptibility.json](../data/ising3d_susceptibility.json).
All 33 entries were compared with the primary table on PDF page 7 of the
[Fujiwara–Arisue author slides](https://www2.ccs.tsukuba.ac.jp/workshop/H14nendo/proceedings/arisue.pdf);
PDF page 5 fixes the expansion variable. The
[Arisue–Fujiwara–Tabata follow-up](https://arxiv.org/abs/hep-lat/0309158)
confirms the susceptibility expansion through order 32. The coefficient data are literature inputs;
this repository does not derive them in Lean.

For dimensions 4–11, the method uses orders 0–20 from
[Butera–Pernici Table I](https://arxiv.org/abs/1209.3592), evaluated at coordination
number $z=2d$. See [the exact integer table](../data/ising_susceptibility_ht20.csv)
and [coefficient polynomials](../data/ising_susceptibility_ht20_polynomials.json).
In that paper the symbol q denotes coordination number; it is not the FK cluster weight.
The numerical estimator here always has FK cluster weight 2.

## Fixed computation and selection rule

1. Set $x=(2d-1)v$, so the rescaled coefficients are $c_n/(2d-1)^n$. This is only numerical conditioning.
2. Compute the formal series of $d\log\chi(x/(2d-1))/dx$ through degree 31 for d=3, or 19 for d=4–11 by series division.
3. Form every $[L/M]$ Padé approximant with $24\le L+M\le31$ and $|L-M|\le2$.
   Thus the d=3 ensemble uses susceptibility orders 25 through 32. For d=4–11 use
   $14\le L+M\le19$ with the same near-diagonal rule (susceptibility orders 15–20).
4. Solve each linear system with partial pivoting using GCC `__float128` arithmetic
   (113 binary significand bits, about 34 decimal digits). Reject a pivot smaller than $10^{-30}$
   or a normalized equation residual above $10^{-22}$.
5. Numerically isolate real denominator and numerator roots on $0<x<2d-1$, using derivative
   subdivision and bisection. Discard a denominator root with nonpositive inferred exponent
   $-P(x)/Q'(x)$, or a real numerator root within $10^{-4}\max(1,|x|)$.
   Select the first remaining positive pole. This is a heuristic pole-selection rule.
6. Return the median of the accepted FK values. Report the full minimum–maximum spread and every row.

No step compares a candidate with a published critical threshold. The conditioning, truncation,
and pole filters are stated explicitly so that the method can be evaluated independently.
The root routine detects simple real poles; it is not certified complex-root isolation, and its
cancellation filter does not examine complex numerator roots.

## Result and verification

For d=3, the 20 accepted approximants give
$$
\widehat p=0.3581028414187471,\qquad
[\min\widehat p_i,\max\widehat p_i]
=[0.3580959922061563,\,0.3581231930773669].
$$
The spread is an estimator-stability diagnostic, **not** a confidence interval or rigorous error bound.
These approximants do not match the Monte Carlo reference within its quoted uncertainty.
More arithmetic precision cannot remove finite-series extrapolation error.

For d=4–11 there are 15 accepted approximants per dimension. Their medians are:

| d | Dlog-Padé FK median |
|---:|---:|
| 4 | 0.2588485280928644 |
| 5 | 0.2037381380646224 |
| 6 | 0.1685804187159023 |
| 7 | 0.1439483713701727 |
| 8 | 0.1256826349167669 |
| 9 | 0.1115675482991348 |
| 10 | 0.1003207833408800 |
| 11 | 0.0911433699195104 |

These displayed digits describe reproducible numerical outputs, not certified physical decimals.

The C++ self-test recovers the exact pole and exponent for
$\chi(x)=(1-2x)^{-2}$ and checks a cubic with three known roots.
[check_pade.py](../scripts/check_pade.py) independently solves the actual Padé linear systems
for all nine dimensions with exact Python fractions and refines each reported pole with 80-digit decimal arithmetic.
The saved [audit receipt](../audit/pade-oracle.json) records the comparison and source hashes.
That audit checks arithmetic consistency; it is not a Lean proof of the estimator or its physical accuracy.

```sh
./build/pcd --method dlog-pade --q 2 --d 3
./build/pcd --pade-details --d 4
python3 scripts/check_pade.py
```

The method requires compiler support for `__float128` (the tested compiler is GCC 13).
Other numerical methods remain available when that extension is absent; requesting this method
then produces a clear unsupported-operation error.
