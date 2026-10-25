# The Siegel–G representation

Fix integer $q\ge1$, dimension $d\ge2$, and radius $R\ge1$. Let
$Z_R,C_R\in\mathbb Z[v]$ be the exact wired FK partition and
center-to-boundary connectivity polynomials, with the wired component
assigned weight one. Set

$$
\boxed{\quad F_R(v)=(R+1)C_R(v)-Z_R(v),\qquad
p=\frac{v}{1+v}.\quad}
$$

A selected positive root $v_R$ therefore solves
$C_R(v_R)/Z_R(v_R)=1/(R+1)$. For $q>1$, the finite spin identity
$C_R=(qZ_{R,0}-Z_R)/(q-1)$ makes this the same root equation as
$(R+1)qZ_{R,0}=(R+q)Z_R$ in the Lean source. The FK–spin
correspondence itself remains outside the current Lean proof; see
[formal scope](formal-scope.md).

## Exact algebraic germ

For rational $u$ with $F_R'(u)\ne0$, the implicit function theorem gives
a unique analytic germ at zero:

$$
\boxed{\quad
F_R\!\left(\Phi_{R,u}(z)\right)=(1-z)F_R(u),
\qquad \Phi_{R,u}(0)=u.
\quad}
$$

Lagrange inversion gives every coefficient explicitly:

$$
\Phi_{R,u}(z)=u+\sum_{n\ge1}c_nz^n,
\qquad
c_n=\frac{[-F_R(u)]^n}{n}
[t^{n-1}]
\left(\frac{t}{F_R(u+t)-F_R(u)}\right)^n\in\mathbb Q.
$$

The quotient at $t=0$ has the removable value $1/F_R'(u)$.
Thus coefficient extraction takes place in $\mathbb Q[[t]]$, and
the displayed defining equation makes $\Phi_{R,u}$ algebraic over
$\mathbb Q(z)$.

## Why it is a Siegel G-function

A rational-coefficient series is a Siegel G-function when it satisfies a
nonzero linear differential equation over $\mathbb Q(z)$ and both its
coefficients and their common denominators grow at most exponentially.
Algebraic power series satisfy these conditions; see
[Garoufalidis–Bellissard, §2.1, Definition 2.2 and Theorem 2(b)](https://arxiv.org/html/0708.4234v4#S2.SS1),
and [Beukers, §4.1, Theorem 4.1.1](https://swc-math.github.io/aws/2008/08BeukersNotesDraft.pdf).
Here the verification is particularly direct.

Write $t(z)=\Phi_{R,u}(z)-u$. Its equation has the form

$$
t=az+\sum_{j=2}^{m}b_jt^j,
\qquad
a=-\frac{F_R(u)}{F_R'(u)},\qquad
b_j=-\frac{F_R^{(j)}(u)}{j!F_R'(u)},
\qquad m=\deg F_R.
$$

Choose a positive integer $D$ clearing the denominators of $u,a,b_2,
\ldots,b_m$. Substituting $t(z)=D\,T(z/D^2)$ gives

$$
T(x)=Da\,x+\sum_{j=2}^{m}D^{j-1}b_jT(x)^j
\quad\Longrightarrow\quad T\in\mathbb Z[[x]].
$$

The implication follows by coefficient induction, since $T(0)=0$ and
every nonlinear term uses only lower coefficients. Consequently
$D^{2n+1}c_k\in\mathbb Z$ for $0\le k\le n$, with $c_0=u$;
this supplies the exponential common-denominator bound. Analyticity near
zero supplies the coefficient bound by Cauchy's estimate. Finally, the
derivatives of $\Phi_{R,u}$ belong to the finite extension
$\mathbb Q(z,\Phi_{R,u})/\mathbb Q(z)$, so finitely many are linearly
dependent over $\mathbb Q(z)$. This proves the required differential
equation and hence

$$
\boxed{\quad \Phi_{R,u}\in\mathcal G_{\mathrm{Siegel}}\cap
\overline{\mathbb Q(z)}.\quad}
$$

## Reaching the chosen root

The condition $F_R'(u)\ne0$ alone does not guarantee convergence of the
Taylor series at $z=1$. Assume the selected root is simple:
$F_R(v_R)=0$ and $F_R'(v_R)\ne0$. There is an analytic local inverse
$\psi$ of $F_R$ on a disk $|w|<\varepsilon$, with $\psi(0)=v_R$.
Choose rational $u>0$ in its inverse neighborhood, sufficiently close to
$v_R$ that, for some $\eta>0$,

$$
\psi(F_R(u))=u,
\qquad (2+\eta)|F_R(u)|<\varepsilon.
$$

Such rational points exist by density and continuity. Then

$$
\Phi_{R,u}(z)=\psi\!\left((1-z)F_R(u)\right)
\qquad (|z|<1+\eta),
\qquad \Phi_{R,u}(1)=v_R.
$$

This proves the existence of an admissible rational base point and
absolute convergence at the endpoint. The simple-root hypothesis is
explicit; the current Lean convergence assumptions do not establish it.

## An explicit finite example

At $R=1$, after cancelling the common boundary-loop factors, the wired
graph has the center and boundary vertex joined by $M=2d$ parallel edges.
Its reduced polynomials are

$$
Z_1(v)=(1+v)^M+q-1,\qquad C_1(v)=(1+v)^M-1,
\qquad F_1(v)=(1+v)^M-(q+1).
$$

For $q\in\{1,2,3\}$ and $d\ge2$, the rational base point $u=1$ gives

$$
\Phi_{1,1}(z)=2\left[1-\left(1-\frac{q+1}{2^M}\right)z\right]^{1/M}-1,
\qquad
p_1=\frac{\Phi_{1,1}(1)}{1+\Phi_{1,1}(1)}
=1-(q+1)^{-1/M}.
$$

The binomial branch at zero has rational coefficients and Taylor radius
$\bigl[1-(q+1)/2^M\bigr]^{-1}>1$. Cancelling loop factors changes the
chosen polynomial homotopy but preserves its positive root. This is an
exact finite-volume value, not the infinite-volume critical probability.

## Limit and proof boundary

With a selected simple positive root and an admissible $u_R$ for each
radius, define, whenever the limit exists,

$$
\boxed{\quad
p_{c,\mathrm{G\_FUNCTIONREPR}}(q,d)
:=\lim_{R\to\infty}
\frac{\Phi_{R,u_R}(1)}{1+\Phi_{R,u_R}(1)}
=\lim_{R\to\infty}\frac{v_R}{1+v_R}.
\quad}
$$

Identification with the physical $p_c(q,d)$ requires the stated
finite-root convergence and physical-identification hypotheses in
[formal scope](formal-scope.md). Each finite germ is a Siegel G-function;
this does not assert that the infinite limit is itself one G-function,
or that it is irrational. These analytic and arithmetic constructions
are mathematical documentation, not yet Lean formalizations.
