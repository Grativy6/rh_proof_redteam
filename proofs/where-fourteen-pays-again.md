# Fourteen pays in long runs near every large scale

Christopher Daniel Pang and Hearthline · 26 November 2026

**For every fixed $A>0$ and every sufficiently large integer $K$, the interval**
$$
 [\,K,\ 2K(\log(2K))^{1/4}\,]
$$
**contains at least $\lfloor(\log K)^A\rfloor$ consecutive indices at which the actual fourteen-copy prime comparison holds.** The prime weights, the cutoff $n^{7/8}<p\le2n$, and the clock at $n=k^4$ are exactly those in the [independently fixed RH criterion](../pal-rh/checks/doubled-ruler/RulerChallenge.lean). Since thirteen fails from index 512, the minimum is exactly fourteen throughout each sufficiently late run.

This is an unconditional paper theorem. The uniform localization uses the Jacobi theta identity and ordinary integer factorization. The transfer to consecutive fourth powers uses the unconditional prime number theorem in short intervals. The starting threshold depends on $A$ and is not made numerical here. The separate finite result pays for **every** index through $2^{36}$. The open question is whether every sufficiently late index pays with fourteen. [Finite range](one-seventh-at-the-boundary.md) · [Thirteen and fifteen](thirteen-fourteen-and-fifteen-prime-copies.md)

## A second way to move the endpoint

Set $b(u)=e^{-\pi u^2}$, $B(z)=\sum_{m\ge1}b(m/z)$ for $z>0$. Jacobi’s transformation gives
$$
 B(z)=(z-1)/2+zB(1/z),\qquad B''(z)=z^{-3}B''(1/z).
$$
For $0<z\le1$ each term of $B''(z)$ is $z^{-2}(4a^2-6a)e^{-a}$ with $a=\pi m^2/z^2\ge\pi$. All are positive. The reciprocal identity gives positivity for $z\ge1$. The differentiated series are locally uniformly convergent. In particular
$$
 0\le B''(z)\ll
 \begin{cases}
 z^{-6}e^{-\pi/z^2},&0<z\le1,\\
 z^3e^{-\pi z^2},&z\ge1 .
 \end{cases}
$$
For the first bound, factor out $e^{-\pi/z^2}$ and bound the remaining Gaussian series by $\sum m^4e^{-\pi(m^2-1)}$. The second follows by reciprocity. This kernel appeared earlier in the program’s [omitted-label experiment](../pal-rh/what-the-first-omitted-label-sees.md). Probability laws associated with the theta and xi transforms have classical treatments. [Jacobi transformation](https://dlmf.nist.gov/20.7.E32) · [Biane, Pitman and Yor](https://arxiv.org/abs/math/9912170) · [Nakamura](https://arxiv.org/abs/1504.03438)

Put $M_\ell=\int_0^\infty z^{2-\ell} B''(z)\,dz$. The behavior of $B$ and $B'$ at zero and infinity gives $M_2=1/2$ and $M_1=1/2$. In fact $B(z)\sim (z-1)/2$ with exponentially small additive remainder at infinity by the reciprocal formula. The substitution $z\mapsto1/z$ gives $M_0=M_3$. Integrate by parts twice and use positivity:
$$
 M_3=2\int_0^\infty z^{-3}B(z)\,dz
    =\sum_{m\ge1}\frac1{\pi m^2}=\frac\pi6.
$$
Take $z$ with probability density $z^2 B''(z)/M_0$, put $c=\pi/3$, and move the head from $X$ to $XY$, where $Y=c/z$. Then $\mathbb EY=1$ and $\mathbb EY^2=\pi/3$. [Basel sum](https://dlmf.nist.gov/25.6.E1)

## Price the average in ordinary logarithms

Write $I(y)=\sum_{d\le y}(y-d)\Lambda(d)$ and $e(y)=I(y)-y^2/2$. For any positive integer $d$ put $v=cX/d$. Integrating $z(v-z)B''(z)$ from 0 to $v$ by parts twice gives $vB(v)-2\int_0^v B(z)\,dz$. Substituting the defining series and grouping $m=dj$ yields
$$
 \mathbb E I(XY)=\frac{cX}{M_0}\sum_{m\ge1}q(m/(cX))\log m,\qquad
 q(u)=b(u)-2u\int_u^\infty b(t)\,\frac{dt}{t^2}.
$$
The grouping uses $\sum_{d\mid m}\Lambda(d)=\log m$. All resulting series at each fixed $X$ are absolutely convergent by Gaussian decay.

Integration by parts gives $q(u)=-b(u)+4\pi u\int_u^\infty b(t)dt$. Since $2\pi u\int_u^\infty b(t)dt\le b(u)$, we have $|q(u)|\le b(u)$. Interchanging the absolutely integrable terms in the defining integral gives $\int_0^\infty q=0$ and $\int_0^\infty q(u)\log u\,du=\frac12\int_0^\infty b=1/4$. For $T=cX\ge1$, compare the sum of $q(m/T)\log m$ with its integral. The omitted part from 0 to 1 has absolute value at most 1. On $[1,\infty)$ the unit-grid error is bounded by the integral of the absolute derivative. We have $\int|q'|\le3$ and $\int u|q'|\le1$ from $q'=4\pi\int_u^\infty b-2\pi u b$, using $\int t^2 b(t)dt=1/(4\pi)$ over the positive half-line. The $q'$ part of the variation is therefore at most $3\log T+1$. The remaining part is at most $\int_{1/T}^\infty b(u)du/u\le\log T+1/2$. Consequently
$$
 \left|\mathbb E I(XY)-\frac{\pi X^2}{6}\right|
 =|\mathbb E e(XY)|\le 2X[4\log(cX)+3].
 \tag{1}
$$
This all-scale centered price uses no input about the zeros of the zeta function. [Independent finite numerical illustrations and exact constants](../receipt-archives/check_pal_gaussian_quartics.py)

The comparison also prices a piece of the original ledger at every large head. Convexity gives $I(n)\le\mathbb E I(nY)$. Subtract this upper bound from the compact doubled-ruler reading, which is at least $4n^2/7-4n$ for $2n\ge1000$. The coefficient of $n^2$ in this difference is $4/7-\pi/6$. In passing to the original retained primes, the initial primes cost less than $n^{3/2}/4$ by the cubic bound and $\theta(t)\le t\log4$. Repeated powers cost at most $(5n/32)\,14\sqrt{2n}<4n^{3/2}$. Indeed $\psi(t)-\theta(t)\le(\log4)[\sqrt t+(\log_2 t)t^{1/3}]\le14\sqrt t$ for $t\ge1$, using $\sup_{t\ge1}(\log_2t)t^{-1/6}=6/(e\log2)$. Thus the normalized return of the actual retained primes satisfies
$$
 \frac{\log G_n}{(2n)^5}\ge
 (4/7-\pi/6)n^2-5n^{3/2}-[10+8\log(2n)]n .
$$
For **every $n\ge2^{32}$ this exceeds two thirds of the original charge $n^2/14$**. The positive margin comes from
$$
 4/7-\pi/6-1/21=\tfrac16(22/7-\pi)
 =\tfrac16\int_0^1\frac{u^4(1-u)^4}{1+u^2}\,du .
$$
Restrict the integral to $[1/3,2/3]$ to get a lower bound $(2/9)^4/[18(1+4/9)]$ on the margin. Already at $n=2^{32}$ it exceeds $5/\sqrt n+[10+8\log(2n)]/n$, which subsequently decreases. These estimates use the elementary Chebyshev upper bound. [Original return and square clock](../pal-rh/why-the-doubled-ruler-keeps-seven-eighths.md)

## Find a head on the correct side in every late window

Let $L=\log X$. In (1) restrict to $1/\sqrt L\le z\le\sqrt L$, or
$$
 cX/\sqrt L\le XY\le cX\sqrt L.
 \tag{2}
$$
The omitted part contributes $o(X^{3/2})$ even if the prime reading there takes either sign. Indeed $|e(y)|\ll y^2$ for all $y>0$ by the elementary Chebyshev bound $\psi(y)\ll y$. Multiplication of the density by $Y^2$ cancels its $z^2$. The two tail integrals of $B''$ above are $O(L^2e^{-\pi L})$. The omitted cost is therefore $O(X^{2-\pi}L^2)$.

For any fixed $\eta>0$, every sufficiently large window (2) contains a real $y$ with $e(y)\le\eta y^{3/2}$. Otherwise its retained mean would exceed $\eta X^{3/2}\mathbb E[Y^{3/2}\mathbf1_{\rm window}]$. This last expectation tends to $\mathbb EY^{3/2}>0$, contradicting (1) and the tail estimate. Choose $\eta=1/100$. Rounding $y$ to $m=\lfloor y\rfloor$ changes $e$ by $O(y)$, since $e'(t)=\psi(t)-t$ away from the integer corners. Thus $e(m)\le m^{3/2}/80$ for sufficiently large $X$.

## Follow the side selected by the real prime count

Fix $B>0$ and take $H=\lfloor m^{3/4}(\log m)^B\rfloor$. At integer $v$, the exact one-step change in $e$ is
$$
 s(v)=e(v+1)-e(v)=\psi(v)-v-1/2 .
$$
We need only its variation across $[m-H,m+H]$:
$$
 H\sup_{|v-m|\le H}|s(v)-s(m)|=o(m^{3/2}).
 \tag{3}
$$
For completeness, Guth and Maynard’s Corollary 1.3 gives an error $O(h\exp(-(\log a)^{1/4}))$ in the prime count relative to $h/\log a$ for $a^{17/30+\epsilon}\le h\le a^{0.99}$. Here take $\epsilon=1/20$. For subintervals of length $m^{2/3}\le h\le H$ with endpoints in this neighborhood the hypotheses hold for all sufficiently large $m$. Multiplying by $\log a$ and replacing the individual prime weights by their logs costs at most $O(H^2/m)$ using the trivial count $h+1$. Powers above the first contribute $O(\sqrt m\log^2 m)$. Shorter differences have size $O(m^{2/3})$ by monotonicity and comparison with an adjacent interval of length $2m^{2/3}$. Uniformly, the supremum in (3) is at most a constant times
$$
 H\log m\, e^{-(\log m)^{1/4}/2}+H^2/m+m^{2/3}.
$$
After multiplication by $H$, all three terms are $o(m^{3/2})$ for each fixed $B$. [Guth and Maynard, Corollary 1.3 and §13.2](https://arxiv.org/pdf/2405.20552v2#page=2)

If $s(m)\ge0$, move left. If $s(m)\le0$, move right. In the selected direction the term $(v-m)s(m)$ is nonpositive. The discrepancy from that line is at most the left side of (3), by summing actual one-step differences. Thus **every integer** on the chosen side through width $H$ satisfies $e(v)\le v^{3/2}/20$ for sufficiently large $m$. At 32 and 33 the accumulated prime-power weight is the same. The two drifts have opposite signs because the real reference advances by one. [Formal one-sided transfer and consecutive quartic addresses](../pal-rh/PALRH/QuarticReturnBlocks.lean)

For any fourth power $n$ in this interval, the earlier sharp omission costs put the clock in range. The normalized cost is at most
$$
 1/20+1/24+\tfrac23(\sqrt{8/7}-1)+o(1)<1/7 .
$$
The terms come from the raw upper error, the discarded $p\le n^{7/8}$, and repeated prime powers. The ordinary-log quadrature costs $o(1)$ in these units. This proves payment at **fourteen** on the actual interval of quartic indices. [Exact transfer to the integer product](../pal-rh/why-the-doubled-ruler-keeps-seven-eighths.md#which-primes-may-be-removed)

Finally take $X=4K^4\sqrt{\log(2K)}/c$. For all sufficiently large $K$, its logarithm lies between $3\log(2K)$ and $5\log(2K)$. Window (2) then starts above $4K^4/\sqrt5$ and ends below $4\sqrt5 K^4\log(2K)$. Including the $o(m)$ shift by $H$ still leaves every chosen head between $K^4$ and $16K^4\log(2K)$. The number of consecutive fourth powers on the selected side is bounded below by a positive constant times $H/m^{3/4}$ by the mean value theorem. Choose $B=A+1$ to absorb the constant and endpoint rounding. This gives the asserted search window and block length.

Pang’s two-direction rule and his insistence on comparing the same physical head led to the drift choice. Hearthline derived the Gaussian factorization price, the window and its transfer to the fixed fourteen-copy condition. The Jacobi identity, Basel sum and short-interval prime theorem are independent classical or cited inputs. Lean proves the discrete slope, choice of side, and passage to consecutive quartic labels under the local slope bound. The analytic estimate (3) and the full recurrence theorem are proved on paper. [Scope and reproduction](../receipt-archives/2026-11-26-pal-gaussian-quartics.json)

## Unresolved

The search windows leave room for failures between successful blocks. For example, the smooth comparison $y^2/2+y^{1+\beta}\cos(\log y)$, $1/2<\beta<1$, is eventually convex and has long regions on both sides of the quadratic. This example concerns extrapolation from blocks alone. It is not a prime count. The unbounded obligation is to rule out *every* sufficiently late failure of the actual fourteen-copy comparison.
