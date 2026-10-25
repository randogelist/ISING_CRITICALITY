# Numerical engine

Build with a C++17 compiler; the standard library is the only dependency:

```sh
g++ -std=c++17 -O2 -Wall -Wextra -Wpedantic numerics/pcd.cpp -o pcd
./pcd --self-test
./pcd > data/model_values.csv
./pcd --q 2 --d 3
./pcd --finite 2 2 3
./pcd --method hj9 --d 8
./pcd --method bp12 --d 8
./pcd --method dlog-pade
./pcd --pade-details --d 4
```

The default CSV evaluates the original GP4 estimator for `q=1,2` and the
attached Lean package's square-loop estimator for `q=3`, over dimensions 2–11.
The two-dimensional rows use the exact square-lattice anchor
`sqrt(q)/(1+sqrt(q))`; GP4 is only used for `d>=3`. No benchmark file is read,
and no parameters are fitted to the comparison table. Printed digits measure
floating-point evaluation precision, not agreement with the physical threshold.

Optional literature-input methods leave the original default unchanged:

| CLI method | Domain | Numerical input |
|---|---|---|
| `hj9` | q=1,2; d>=3 | Hellmund–Janke inverse-dimension expansion through sigma^-9 |
| `bp12` | q=2; d>=3 | Butera–Pernici inverse-coordination expansion through z^-12 |
| `dlog-pade` | q=2,d=3–11 | 32nd-order susceptibility series in d=3, 20th order in d=4–11; median of a predefined near-diagonal Dlog-Padé ensemble |

See [literature-series.md](../docs/literature-series.md),
[dlog-pade.md](../docs/dlog-pade.md), and the source headers
for provenance and truncation conventions. Higher asymptotic order can make
low-dimensional estimates worse; the engine does not select a method using
the benchmark results. Dlog-Padé requires a compiler with `__float128`, such as
the tested GCC. It uses 113-bit arithmetic with no extra library dependency.
Other methods remain available when that compiler extension is absent.
`--method dlog-pade` defaults to all dimensions 3–11; `--d` selects one row.
`--pade-details --d N` exposes every approximant, diagnostic residual and
rejection reason for dimension N (default 3). The ensemble range is not a
rigorous confidence interval.

## Finite-volume calculation

`--finite d R q` computes a different object: the root of

$$
W_R(p)=\frac1{R+1}
$$

in the nearest-neighbor wired box `[-R,R]^d`, for integer `q=2,3`. All boundary
spins are fixed to color zero. The code enumerates all `q^((2R-1)^d)` interior
spin assignments and records integer histograms by the number of disagreeing
edges. Boundary-to-boundary edges contribute a common factor and are omitted.
With `y=1-p`, the histograms are polynomials in `y`; the connection probability
is calculated using the Edwards–Sokal identity

$$
W_R(p)=\frac{q\Pr(\sigma_0=0)-1}{q-1}.
$$

Histogram coefficients are exact integers. Polynomial evaluations and bisection
are floating-point calculations. The finite root is not the infinite-volume
critical threshold, and the code supplies no certified convergence rate.
Enumeration is deliberately limited to 24 interior vertices and at most
`2^24` assignments. This allows, for example, `d=2,R=2,q=2` (512 assignments)
and `d=2,R=2,q=3` (19,683 assignments). The `q=1` spin representation is
degenerate and is rejected; no independent bond enumerator is implemented.

The self-test checks all nine q=3 rounded values against the attached Lean
certificate, exact q=1/q=2 rational examples, probability-coordinate conversions,
and finite roots against a separately derived one-free-spin formula:

$$
r_1(d,q)=1-(q+1)^{-1/(2d)}.
$$

It also checks histogram counts and an R=2 root residual. These runtime checks
include an independent enumeration of all FK bond subsets of a small wired
one-dimensional box, and exact synthetic rational-function Padé examples.
They
do not formally verify the C++ compiler, its library functions, or the
Edwards–Sokal correspondence.
