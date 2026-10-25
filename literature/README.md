# Weighted literature reference

The front page uses a **descriptive weighted mean** of the recorded literature
estimates for each $(q,d)$. It is not a new critical-threshold calculation or
a pooled accuracy claim. Model predictions never enter the weights.

For converted probabilities $p_i$ and quoted error scales $u_i>0$,

$$
w_i=u_i^{-2},\qquad a_i=\frac{w_i}{\sum_jw_j},\qquad
\bar p=\sum_i a_i p_i.
$$

The calculation uses Python's standard-library `Decimal` at 50-digit working
precision. Printed source values are read directly from
[benchmarks.json](../data/benchmarks.json); previously rounded converted values
are not used. Many displayed arithmetic digits do not imply physical accuracy.

| Source variable | Conversion to FK probability |
|---|---|
| $p$ | unchanged |
| Ising $K$, BB2007 $\beta$ | $1-e^{-2K}$, $1-e^{-2\beta}$ |
| Potts $K$ | $1-e^{-K}$ |
| Ising $T$ | $1-e^{-2/T}$ |
| Potts $T$ | $1-e^{-1/T}$ |

For a printed input $x\pm\delta$ and its conversion $f$, use
$p_i=f(x)$ and
$u_i=|f(x+\delta)-f(x-\delta)|/2$. The converted interval endpoints are
retained in the audit. Exact square-lattice values
$\sqrt q/(1+\sqrt q)$ take precedence at $d=2$, avoiding an infinite
inverse-error weight. A single eligible estimate remains unchanged; missing
references remain missing.

## Source policy

[policy.json](policy.json) makes the exclusions explicit:

- **BB2007, q=3, d=3:** use Eq.14's conventional equal-height estimate once.
  Eq.24 analyzes the same paper's data differently; it is retained as a
  substitution sensitivity, not an additional independent source.
- **W2014, q=3, d=3:** exclude the value because the paper explicitly states
  that the accessible bond dimensions are not yet in the convergent regime.
- **W2014, q=2, d=3:** include the published value. Its tiny quoted convergence
  error receives about **99.04%** of the nominal weight. Omitting that source
  gives the Monte Carlo-only reference, recorded in the diagnostics.

All other uncertainty-bearing entries in the curated input are included,
regardless of the old `selected` flag. Two surviving entries from one paper
for the same target cause an error instead of silently receiving extra weight.
No policy choice depends on agreement with this repository's formula.

Monte Carlo errors, high-temperature-series spread and HOTRG convergence
diagnostics are not necessarily comparable standard deviations. Distinct papers
can also share authors, data or methods. Consequently **no pooled ± uncertainty,
confidence interval or significance claim is reported**. Shared series inputs
also mean that comparison with a series-based model need not be independent
validation. The mean summarizes the recorded estimates using nominal weights;
it is not an assertion of literature consensus or an exhaustive bibliography.

## Reproduce and inspect

```sh
python3 literature/average.py
python3 literature/average.py --check
python3 -m unittest discover -s literature -p 'test_*.py'
```

- [averages.csv](averages.csv): all 30 target rows, status and source counts.
- [weights.csv](weights.csv): original inputs, conversions, individual weights,
  exclusion reasons, source links and locations.
- [averages.json](averages.json): complete source metadata, input/policy hashes,
  leave-one-source-out means, and the BB2007 Eq.24 substitution calculation.
- [average.py](average.py): deterministic implementation; no Lean compilation.

`exact`, `single`, `weighted` and `missing` distinguish the reference types.
Sensitivity calculations are alternative descriptive means, not error bounds.
