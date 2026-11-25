# When a drop would count

Christopher Daniel Pang and Hearthline, 25 November 2026. Pang’s PAL question is whether the next step makes measurable progress on the same object. Here the list, update and measurement are all fixed in advance. [Construction, attribution and four worked sizes](the-balanced-newton-handoff.md)

**If a zeta zero lies to the right of $1/2$, every sufficiently late squaring step in this construction increases its total squared error.** Thus infinitely many steps at which the error stays level or falls would imply RH. A finite number of falls can occur on either hypothesis. The result applies to the prescribed sequence starting at $H=4$ and updating to $H^2/2$ each time.

## What sets the direction

Let $\Theta$ be the supremum of $1/2$ and the real parts of the nontrivial zeros of $\zeta$. For the true tapered, balanced coefficients $a_H$ and their all-row error $E_H$,

$$
\lim_{H\to\infty}\frac{\log(1+E_H)}{\log H}=2\Theta-1. \tag{1}
$$

Write $K=H^2/2$ along the prescribed sequence. Since $\log K/\log H\to2$, subtracting two instances of (1) gives

$$
\lim \frac{\log((1+E_K)/(1+E_H))}{\log H}=2\Theta-1. \tag{2}
$$

If the right side is positive, the ratio inside the logarithm eventually exceeds $H^c$ for each fixed $0<c<2\Theta-1$. Conversely, under RH the ratio grows or shrinks by at most $H^\epsilon$ in either direction for every fixed $\epsilon>0$, at sufficiently large steps. Equation (2) leaves the individual signs under RH open. It gives a course of action with a consequence for the original problem. Proving infinitely many nonincreases is sufficient. More generally it suffices, for every $\epsilon>0$, to produce arbitrarily late steps with $(1+E_K)/(1+E_H)\le H^\epsilon$.

## A finite arithmetic test at both ends

For the same list, retain only the rows through $H^2$ and call their rational cost $P_H$. The head contributes at most $H$ to $\sum_d|a_H(d)|$, and the outer strip contributes at most $2H$. Hence $|F_H(k)|\le2H$ at every row by the centered census bound. For $H\ge1$ the whole squared error beyond the square obeys
$
0\le E_H-P_H\le\frac{(1+2H)^2}{H^2+1}\le9 .
$
Consequently $\log(1+E_H)$ and $\log(1+P_H)$ differ by at most $\log 10$. Equations (1) and (2) hold verbatim with $P$ in place of $E$. In particular, **infinitely many nonincreases of the finite rational numbers $P_H$ on this single sequence would suffice**. Even occasional bounded-factor increases suffice if they recur arbitrarily late. Each individual comparison uses the original finite list, the six-step census and at most $K^2$ numbered rows. Its truth at infinitely many steps is an additional mathematical claim. The first three finite comparisons all decrease. [Bounds and numbers](the-balanced-newton-handoff.md#what-the-list-measures)

## Proof of the exponent

Extend $F_H(x)=\sum_d a_H(d)C(x/d)$ to real $x\ge1$. It is constant between consecutive integers. Let $e_H(x)=1-F_H(x)$, $A_H(s)=\sum_d a_H(d)d^{-s}$, and $G(s)=(1-2^{-s})(1-3^{-s})\zeta(s)$. The balance $A_H(1)=0$ and $|C(x)-x/3|\le2/3$ imply $e_H$ is bounded for each fixed $H$. For $\Re s>1$, termwise integration of the census gives
$$
\int_1^\infty e_H(x)x^{-s-1}\,dx=\frac{1-G(s)A_H(s)}s .
$$
Both sides extend holomorphically to $\Re s>0$, with the singularity of $G A_H$ at 1 removable. Squared error is $\int_1^\infty |e_H(x)|^2x^{-2}\,dx$. Substituting $x=e^y$ and applying Fourier Plancherel to $e_H(e^y)e^{-y/2}$ on $y\ge0$, extended by zero to $y<0$, gives
$$
E_H=\frac1{2\pi}\int_{-\infty}^\infty
\frac{|1-G(1/2+it)A_H(1/2+it)|^2}{1/4+t^2}\,dt . \tag{3}
$$

**Lower bound.** For a zero $\rho$ of real part $\beta>1/2$, the first integral equals $1/\rho$. The error vanishes through the entire interval $1\le x<H+1$. Cauchy–Schwarz on $[H+1,\infty)$ gives
$$
E_H\ \ge\ \frac{2\beta-1}{|\rho|^2}(H+1)^{2\beta-1}.
$$
This holds at every $H$. Take the supremum over such zeros. The nonnegativity of $\log(1+E_H)$ handles $\Theta=1/2$. [General exact-head lower bound](what-the-next-octave-costs.md)

**Upper bound.** First suppose $\Theta<1$ and fix $\Theta<b<1$. For any small $\eta>0$, the Balazard–Saias partial-sum estimate implies, uniformly in $X\ge1$ and $t\in\mathbb R$,
$$
\left|\sum_{n\le X}\mu(n)n^{-b-it}\right|\ll_{b,\Theta,\eta}(1+|t|)^\eta .
$$
Indeed the half-plane $\Re s>\Theta$ is zero-free by the definition of $\Theta$. Use their estimate at $s=b+it$ and at cutoff 2 to bound $1/\zeta(s)$ by the same quantity. For the rough marks $m$ the bound transfers by convolving $\mu$ with the indicator of the integers $2^i3^j$, $i,j\ge0$. Their absolute $b$-weighted sum is finite. [Balazard–Saias estimate reproduced as Lemma 2.1 in Báez-Duarte](https://arxiv.org/pdf/math/0202141)

At $t=0$ the bounded partial sums of $m(n)n^{-b}$ imply $\sum_{n>h}m(n)/n=O_b(h^{b-1})$ by summation by parts. The total sum is zero. To see its value, the convergent Dirichlet series equals $1/G(s)$ for real $s>1$, and bounded partial sums at $b$ give locally uniform convergence near 1. The reciprocal tends to zero at 1. Therefore $U(h)=O_b(h^{b-1})$, and its average $s_H(m)$ satisfies the same bound at $H$.

At $s=1/2+it$ apply summation by parts once more, to the finite weights $n^{b-1/2}w_H(n)$. Their supremum and total variation are $O_b(H^{b-1/2})$, since the taper is bounded and monotone and the power increases. The compensating strip $B_H(s)=\sum_n b_H(n)n^{-s}$ has absolute size $O(\sqrt H)$. Combining the tapered sum and $-s_H(m)B_H(s)$ gives
$$
|A_H(1/2+it)|\ll H^{b-1/2}(1+|t|)^\eta .
$$

In (3) the remaining squared weight $|G(1/2+it)|^2(1+|t|)^{2\eta}/(1/4+t^2)$ is integrable for small $\eta$. For instance the unconditional critical-line bound $|\zeta(1/2+it)|\ll(1+|t|)^{1/6}\log(2+|t|)$ suffices. Thus $E_H\ll_b H^{2b-1}$. Let $b$ decrease to $\Theta$ to get the desired upper exponent. If $\Theta=1$, the proved coefficient bound $|a_H(n)|\le2$ directly gives $|A_H(1/2+it)|\ll\sqrt H$. The same integral gives $E_H\ll H$, which is exactly the endpoint required. Together with the lower bound this proves (1). [Hiary, Patel and Yang, Theorem 1.1](https://arxiv.org/pdf/2207.02366)

The analytic exponent (1) and its application to this arithmetic family are paper proofs. The [Lean source](PALRH/TaperedNewton.lean) includes the elementary limiting implication used in (2), the finite recurrence and the conditional deduction from subpower physical costs to bare Mathlib RH.

## Following the signed term through the update

The finite identity also supplies a formula for the next polynomial from the two earlier polynomials. Write $s=\sigma+it$ with $1/2\le\sigma<b<1$. The Mellin weight of the continuous plateau and taper $w(x)=1$ through 1, $2-x$ through 2 and zero thereafter is
$$
W(z)=\int_0^\infty w(x)x^{z-1}\,dx=\frac{2^{z+1}-1}{z(z+1)}
\quad(\Re z>0).
$$
The apparent singularity at $-1$ is removable. For admissible old sides $H,J$ and new side $K$, the same output satisfies
$$
\begin{aligned}
A_K(s)=A_H(s)+A_J(s)-\frac1{2\pi i}\int_{\Re u=b}
 &G(u)A_H(u)A_J(u)K^{u-s}\\
 &{}\times\big[W(u-s)-B_K(s)K^{s-1}W(u-1)\big]\,du . \tag{4}
\end{aligned}
$$

On a vertical line to the right of 1 this is just Mellin inversion of the two finite taper readings of $a_H*a_J*g$. Move the line to $b$. The pole of $W(u-s)$ lies to its left. At $u=1$ there can be one pole from $G$ and one from $W(u-1)$, and the two old lists supply the two actual zero factors $A_H(1)=A_J(1)=0$. On the horizontal segments $W=O(|\Im u|^{-2})$. For fixed $b>0$ and a fixed right edge, the one-term Euler summation remainder cut at $N=\lceil|\Im u|\rceil+1$ bounds $\zeta(u)$ by $O_b((1+|\Im u|)^{1-b}+\log(2+|\Im u|))$ at large height on this strip. The Dirichlet polynomials are bounded there for fixed sides. This justifies the shift and absolute convergence.

For example, put $V_{H,J}(t)=\int |G(b+iv)A_H(b+iv)A_J(b+iv)|\,dv/(1+(v-t)^2)$. Since $|B_K(s)|\ll_\sigma K^{1-\sigma}$, the magnitude of the correction in (4) is at most $C_{b,\sigma}K^{b-\sigma}\{V_{H,J}(t)+V_{H,J}(0)\}$. This is an upper bound on a specific part of the update. The signs in (4) still matter for a decrease in (3).

A global frequency average alone loses that information. For fixed $b>1/2$ the infinite-time mean of $|A_H(b+it)|^2$ equals $\sum |a_H(n)|^2/n^{2b}\le4\zeta(2b)$ by direct integration of the finite polynomial. A bounded, balanced list can nonetheless have large values on a fixed interval near frequency zero. For even $H$, set a comparison list equal to 1 on $H<n\le3H/2$ and $-c_H$ on $3H/2<n\le2H$, choosing $c_H$ so its reciprocal sum is zero. Divide all coefficients by $\max(1,c_H)$. The ratios $c_H$ tend to $\log(3/2)/\log(4/3)$. At any fixed $1/2<b<1$, the weight of $n^{-b}$ relative to $n^{-1}$ increases strictly with $n$. Thus the two half-intervals have unequal limiting $b$-weighted readings. More precisely their normalized Riemann sums for $H^{b-1+it}A_H(b+it)$ converge uniformly for $t$ in a compact interval about zero to a continuous function nonzero at zero. On a smaller fixed interval the absolute size is therefore $\gg_b H^{1-b}$. This comparison uses assigned coefficients. The arithmetic challenge concerns the actual lists generated from $4$.

Literal squaring of the physical error also fails as an all-scale rule. We have measured $E_8<1$. If $E_{H^2/2}\le E_H^2$ at every ensuing step, iteration would give $E_H\le H^{-c}$ along this sequence for some $c>0$. The classical distance lower bound gives $E_H\gg1/\log(12H)$ for these measurements. To apply it, replace $x$ by its reciprocal. Each actual reading is a combination of the standard fractional-part functions of moduli at most $12H$, and its balance makes its extension to the region above 1 zero, just like the target. This is the same squared norm as (3). [Báez-Duarte, equation (1.2) and the cited lower-bound authors](https://arxiv.org/pdf/math/0202141)

## Unresolved

Find a reason in the signs of (4), or directly in the same physical rows, that forces nonincrease for arbitrarily late updates or the weaker relative growth bound following (2). The recurrence constructs both endpoints. Establishing the direction on arbitrarily late steps is the remaining arithmetic work.
