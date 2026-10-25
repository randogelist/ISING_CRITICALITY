# Irrationality: proofs and scope

| Object | Result | Proof |
|---|---|---|
| q=3 square-loop approximation, integer d≥3 | Transcendental, hence irrational | [Classical proof](irrationality-square-loop.md), using Gelfond–Schneider; not Lean-formalized |
| Square-lattice anchor, natural q | Irrational exactly when q is not a square | [Lean arithmetic](../IsingCriticality/Irrationality.lean) |
| GP4 approximation, rational q,d | Rational | Same Lean module |
| Higher-dimensional physical p_c | No unconditional irrationality proof established here | Conditional criterion below |

## Exact planar values

Define

$$
p_{\mathrm{plane}}(q)=\frac{\sqrt q}{1+\sqrt q}.
$$

The rational map $v\mapsto v/(1+v)$ preserves irrationality. For
$v\ne-1$, its inverse is $p\mapsto p/(1-p)$; the exceptional
input $v=-1$ and its totalized Lean image $0$ are both rational.
Together with the square-root criterion this gives

$$
p_{\mathrm{plane}}(q)\notin\mathbb Q
\quad\Longleftrightarrow\quad q\text{ is not a perfect square}.
$$

In particular,

$$
p_{\mathrm{plane}}(2)=2-\sqrt2\notin\mathbb Q,\qquad
p_{\mathrm{plane}}(3)=\frac{3-\sqrt3}{2}\notin\mathbb Q,
\qquad p_{\mathrm{plane}}(1)=\frac12.
$$

The module proves `squareLatticeAnchor_irrational_iff`, the explicit
q=2,3 irrationality statements, and q=1 rationality.
Identification of this formula with the physical square-lattice threshold is
[Beffara–Duminil-Copin, Theorem 1](https://arxiv.org/abs/1006.5073).
That percolation theorem is an external mathematical input; it is not
formalized in this repository. The Lean results certify the arithmetic of
the exact formula.

## Rational GP4 values

GP4 uses only rational field operations on q,d. The Lean theorem
`gp4_ratCast` exhibits the rational value, and
`gp4_ratCast_not_irrational` excludes irrationality for every rational input.
For example,

$$
\widehat p_{\mathrm{GP4}}(1,3)=\frac{782}{3125},\qquad
\widehat p_{\mathrm{GP4}}(2,3)=\frac{272}{761}.
$$

Neither formula is identified with the higher-dimensional physical threshold.
The arithmetic of an approximation does not determine the arithmetic of its
target or of a limiting construction.

## Conditional higher-dimensional route

The earlier factorial-cell proposal is formalized as
`irrational_of_eventual_factorial_cells`:

$$
\left[
\exists N\ \forall n\ge N\ \exists A_n\in\mathbb Z:
\frac{A_n}{n!}<x<\frac{A_n+1}{n!}
\right]
\quad\Longrightarrow\quad x\notin\mathbb Q.
$$

**Proof.** If $x=a/b$, with $b>0$, choose
$n\ge\max(N,b)$. Then $b\mid n!$, so $n!x$ is an integer.
Multiplying the strict cell inequalities by $n!>0$ gives
$A_n<n!x<A_n+1$, impossible for integers. ∎

This is a proved implication with an explicit universal premise. The
repository does not construct these cells for physical p_c in d≥3.
Finite decimal agreement, convergence of finite-volume roots, or a
G-function representation does not supply this premise. No finite accepted
witness or unconditional higher-dimensional irrationality result is claimed.

## Verification

[CI run 40176094806](https://github.com/randogelist/ISING_CRITICALITY/actions/runs/40176094806)
passed for source commit `afe998c18dd8137c373982f7b6c7f944145af573`: 18 modules,
3 compiled and 15 reused with matching fingerprints. The new arithmetic theorems
use only `propext`, `Classical.choice`, and `Quot.sound`.
The [proof receipt](../audit/build-receipt.json) records the exact source hashes.

The new Lean module is included in the normal build and every public theorem
above is included in [Audit.lean](../Audit.lean). Compilation and axiom checking
run only in [GitHub CI](https://github.com/randogelist/ISING_CRITICALITY/actions/workflows/verify.yml).
The square-loop transcendence argument remains mathematical documentation;
it is not introduced as a Lean axiom.
