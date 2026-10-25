# Irrationality of the square-loop formula

**Status:** mathematical proof using the Gelfond–Schneider theorem; **not
Lean-formalized**. The result concerns the approximation defined in
[`PCD/Q3Defs.lean`](../PCD/Q3Defs.lean). It does not identify that approximation
with the physical critical probability.

## Theorem

For every integer $d\ge3$, the real number `PCD.pSquare d` is
**transcendental**, hence irrational.

Put

$$
r=2^{1/d},\qquad s=\sqrt2,\qquad
t_d=\frac{2(r-1)}{4-r},\qquad
v_B=\frac{2(r-1)}{2-r},
$$
$$
\alpha_d=\frac{d-1}{2}\left(\frac{t_d}{t_2}\right)^4,
\qquad V_d=v_B(3/2)^{\alpha_d},
\qquad p_\square(d,3)=\frac{V_d}{1+V_d}.
$$

These are the repository's definitions: `deltaSquare d` is
$\alpha_d\log(3/2)$, and the positive real power satisfies
$(3/2)^{\alpha_d}=\exp(\alpha_d\log(3/2))$.
On $d\ge3$, the natural subtraction in the Lean definition of $d-1$
agrees with the displayed subtraction.

## Proof

We have $1<r<s<2$. Both $r$ and $s$ are algebraic, and

$$
\frac1{t_2}
=\frac{4-s}{2(s-1)}
=\frac{2+3s}{2}.
$$

Consequently, with

$$
R=\frac{(r-1)(2+3s)}{4-r},
\qquad \alpha_d=\frac{d-1}{2}R^4,
$$

the exponent $\alpha_d$ is algebraic. We prove it is irrational by
exhibiting a field automorphism fixing $\mathbb Q$ that moves it.

### Odd dimension

The polynomial $X^d-2$ is irreducible over $\mathbb Q$ by Eisenstein
at the prime $2$. Thus
$[\mathbb Q(r):\mathbb Q]=d$. Since $d$ is odd,
$s\notin\mathbb Q(r)$: otherwise the tower formula would make $2$
divide $d$.

The quadratic extension $\mathbb Q(r,s)/\mathbb Q(r)$ therefore has
an automorphism fixing $r$ and sending $s$ to $-s$. It changes
$\alpha_d$, because

$$
(2+3s)^4-(2-3s)^4=1056s\ne0,
$$

and the remaining multiplier
$\frac{d-1}{2}((r-1)/(4-r))^4$ is nonzero. Every rational number is
fixed by this automorphism, so $\alpha_d\notin\mathbb Q$.

### Even dimension

Write $d=2m$. Irreducibility of $X^d-2$, together with
$\mathbb Q(-r)=\mathbb Q(r)$, gives a $\mathbb Q$-automorphism
$\sigma$ of $\mathbb Q(r)$ with $\sigma(r)=-r$.
Moreover $s=r^m$, so $\sigma(s)=(-1)^m s$.

If $m$ is even, then

$$
\sigma(R)=-\frac{(r+1)(2+3s)}{4+r},
$$
$$
\frac{r+1}{4+r}-\frac{r-1}{4-r}
=\frac{8-2r^2}{16-r^2}>0.
$$

Thus $|\sigma(R)|>R>0$, and $\sigma(\alpha_d)>\alpha_d$.

If $m$ is odd, then

$$
\sigma(R)=\frac{(r+1)(3s-2)}{4+r}>0,
$$
$$
\sigma(R)-R
=\frac{6s(4-r^2-sr)}{16-r^2}>0.
$$

The final inequality follows from $r<s$ and $s^2=2$, which imply
$r^2+sr<4$. Again $\sigma(\alpha_d)>\alpha_d$.
Hence $\alpha_d\notin\mathbb Q$ in both even cases.

### Transcendence and the probability coordinate

We have proved that $\alpha_d$ is real algebraic and irrational.
The **Gelfond–Schneider theorem** now implies that
$(3/2)^{\alpha_d}$ is transcendental: its base $3/2$ is algebraic,
positive, and different from $1$.

The factor $v_B$ is nonzero algebraic, so $V_d$ is transcendental.
Also $V_d>0$, and therefore $0<p_\square(d,3)<1$. If
$p_\square(d,3)$ were algebraic, closure of algebraic numbers under field
operations would make

$$
V_d=\frac{p_\square(d,3)}{1-p_\square(d,3)}
$$

algebraic, a contradiction. Thus $p_\square(d,3)$ is transcendental. ∎

## External theorem and formal scope

A primary research proof of the real Gelfond–Schneider theorem used here is
J. Pila, *Geometric and Arithmetic Postulation of the Exponential Function*,
[Theorem 3.2](https://people.maths.ox.ac.uk/pila/Nex.pdf).
The conjugation argument above applies that theorem to this repository's
specific exponent.

This proof is mathematical documentation, not a new Lean axiom or an audited
Lean theorem. The existing eight-decimal certificates concern numerical
rounding and do not formalize this transcendence argument. A transfer to
physical $p_c(3,d)$ would additionally require a proof that
$p_c(3,d)=p_\square(d,3)$, which the repository does not provide.
