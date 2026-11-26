# What the least successful cutoff measures

Christopher Daniel Pang and Hearthline · 26 November 2026

Write $N(n,c)=(n!)^n\prod_{c<p\le n}p^{2(n-p)}$ and $B_n=n^{n^2}$. For the minimum $d(n)=\min\{c:N(n,c)\le B_n\}$, the set is nonempty because $n!\le n^n$. Demand decreases weakly in $c$. At a positive, minimal successful cutoff the label being removed must actually have dials. In particular $d(n)=0$ or $d(n)$ is prime. For an arbitrary Boolean selection rule, the corresponding statement holds with “admitted label” in place of “prime.” [Finite Lean theorems and the damaged-frame control](PALRH/HorizonCut.lean)

## A power saving has a precise meaning

Fix $1/2\le a<1$ and let $Z(a)$ mean that every nontrivial zero of the ordinary zeta function has real part at most $a$. Then
$$
 Z(a)\quad\Longleftrightarrow\quad
 d(k^4)\le \lfloor(k^4)^a\rfloor\quad\text{for all sufficiently large integers }k.
$$
In the forward direction the fit also holds at *every* sufficiently late integer size and pays the explicit paired encoder.

**From a cutoff to a region.** Put $I_\theta(x)=\sum_{p\le x}(x-p)\log p$ and use $I_\psi$ with the von Mangoldt weights. Omitting the dials up to $c=\lfloor n^a\rfloor$ costs at most $2n\theta(c)=O(n^{1+a})$. The original logarithmic margin is $n^2-2I_\theta(n)-nH_n$ with $1\le H_n\le1+\log n$. The assumed fit therefore bounds $I_\theta(n)-n^2/2$ from above by $O(n^{1+a})$ at the fourth powers. Convex chord interpolation costs $O(x^{3/2})$ between knots. Adding the repeated powers costs $O(x^{3/2})$ as well. Hence
$$
 V(x)=I_\psi(x)/x-x/2\le Cx^a \quad(x\ge1).
$$
The finite alternating-divisor proof generalizes directly. Put $F(x)=Cx^a-V(x)\ge0$ above 1 and extend by zero below it. The alternating sum of $V(x/r)$ is $O(1+\log x)$ from the exact divisor computation. The alternating sum of $(x/r)^a$ has magnitude at most $x^a$. For $b>a$ the alternating transform is thus absolutely integrable against $x^{-b-1}\,dx$. With $J(X)=\int_1^X F(x)x^{-b-1}\,dx$, the first pair in the integrated sum pays $(1-2^{-b})J(X)$ and all later pairs are nonnegative. Thus $\int_1^\infty |V(x)|x^{-b-1}dx<\infty$. Its Mellin transform is holomorphic for $\Re s>a$ and agrees on $\Re s>1$ with $-\zeta'(s)/(s(s+1)\zeta(s))-1/[2(s-1)]$. A zero in $\Re s>a$ gives a nonremovable pole. [Finite divisor calculation](the-prime-board-and-its-signed-area.md#why-a-bound-in-one-direction-reaches-zeta) · [Fourth-power chord](fourth-power-boards-and-their-funded-intervals.md)

**From a region to a cutoff.** Write $\rho=\beta+i\gamma$ and $S=\sum_\rho1/|\rho(\rho+1)|$, counting multiplicities. We need the coefficient $S<1$, because the cutoff has leading constant one. For the completed function $\xi$, subtract its logarithmic derivatives at 0 and 1, taking the value at 1 first. The classical product and reflection give
$$
 T=2+\gamma_E-\log(4\pi)=2\sum_\rho \Re(1/\rho).
$$
All summands on the right are nonnegative. Since $0<\beta<1$,
$\Re(1/\rho)\ge\beta/(1+\gamma^2)$. Pair the multiset of zeros under $\rho\mapsto1-\bar\rho$ to obtain $\sum_\rho (1+\gamma^2)^{-1}\le T$. Each $u=(1+\gamma^2)^{-1}$ is at most $T$. Consequently
$$
 S\le\sum_\rho\gamma^{-2}=\sum_\rho u/(1-u)\le T/(1-T)<1 .
$$
The last inequality follows already from $T<1/2$. Our independent rational bounds give $T<(\log2)/15$. The identity for $T$ uses $\xi(1-s)=\xi(s)$, the Laurent expansion at 1 and the gamma logarithmic derivative at $1/2$. [Completed-product calculation](the-dyson-response-and-prime-squares.md) · [Riemann’s original paper](https://www.claymath.org/wp-content/uploads/2023/04/Wilkins-translation.pdf) · [Arithmetic for the constants](../receipt-archives/check_pal_horizon_pairs.py)

Under $Z(a)$ the ordinary integrated explicit formula gives
$$
 |I_\psi(x)-x^2/2|\le Sx^{1+a}+O(x).
$$
Indeed each zero contributes $-x^{1+\rho}/[\rho(1+\rho)]$ and the other terms are $O(x)$ for $x\ge2$. This use of the formula needs only the stated upper bound on real parts. Since $I_\theta\le I_\psi$, an upper estimate for $I_\theta$ follows. The discarded prime dials pay
$$
2\sum_{p\le c}(n-p)\log p\sim 2 n^{1+a},
$$
by $\theta(c)\sim c$, $c\sim n^a$, and $c=o(n)$. The factorial charge $nH_n$ is $o(n^{1+a})$. The retained records have logarithmic margin at least $(2-2S+o(1))n^{1+a}$, which also pays the at-most-$n$ cost of pairing. [Integrated explicit formula, Johnston, proof of Lemma 2.6](https://arxiv.org/pdf/2201.06184)

## The outside number and the limit

Let $\beta_*=\sup_\rho\Re\rho$ and let $L=\limsup_{k\to\infty}\log(1+d(k^4))/\log(k^4)$. Then
$$
\boxed{\ \beta_*=\max(1/2,L)\ }.
$$
Every $a>\max(1/2,L)$ below 1 eventually admits the required fit and hence bounds $\beta_*$. Conversely apply the forward implication from $Z(a)$ at $a=\beta_*$ if $\beta_*<1$. When $\beta_*=1$, the bound $d(n)\le n$ suffices in this direction. A critical-line zero is available independently, so $\beta_*\ge1/2$. Under RH the all-prime board fits at every size and $d(n)=0$. If RH fails then $L=\beta_*>1/2$. The strict distinction between a fixed power saving and a logarithmic saving persists however large the finite range used for testing.

The all-size explicit cutoff currently in this program is $\lceil3n/b^3\rceil$ with $b$ the binary length of $n$. Its exponent tends to 1. It supplies an actual decoder, while the exponent formula above explains exactly what a stronger asymptotic bound would earn. [Known funding and unresolved band](the-factorial-frame-for-prime-distances.md#funding-the-upper-distances-at-every-size)
