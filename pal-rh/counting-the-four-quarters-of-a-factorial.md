# Counting the four quarters of a factorial

Christopher Daniel Pang and Hearthline · 26 November 2026

A factorial supplies a simple test case for a signed arithmetic reading. Put
$$
D(y)=\lfloor4y\rfloor-4\lfloor2y\rfloor+4\lfloor y\rfloor,\qquad
F(X)=\sum_{q\le4X}\Lambda(q)D(X/q).
$$
On the four successive quarters of a unit interval $D$ takes the values $0,1,-2,-1$. The entire part of $y$ cancels. Count multiples of each prime power in a factorial to get the independent expression
$$
e^{F(X)}=\frac{\lfloor4X\rfloor!\,(\lfloor X\rfloor!)^4}{(\lfloor2X\rfloor!)^4}.
$$

## Move the cut by one quarter

At a whole head $m$ the ratio is $R_m=\binom{4m}{2m}/\binom{2m}m^2\ge1$. Vandermonde’s identity includes $\binom{2m}m^2$ as its middle term. Cancellation of consecutive factorials gives
$$
\frac{R_{m+1}}{R_m}
=\frac{(4m+1)(4m+3)(m+1)}{2(2m+1)^3}
=(1+1/q)\bigl(1-1/(4q^2)\bigr),\qquad q=2m+1.
$$
At $q=3$ the second factor is $35/36$. The two neighbors of 6 multiply to 35. The infinite product of these factors over positive odd $q$ is $\cos(\pi/4)=1/\sqrt2$ by the cosine product. Stirling gives $R_m\sim\sqrt{\pi m/2}$.

For $X=m+\delta$ the four successive ratios, in order of increasing $\delta$, are
$$
R_m,\quad (4m+1)R_m,\quad \frac{4R_{m+1}}{(m+1)(4m+3)},\quad \frac{4R_{m+1}}{m+1}.
$$
The last is strictly decreasing for $m\ge0$, since its successive ratio is bounded by $(1+1/(2m+3))(m+1)/(m+2)<1$. It drops below 1 between $m=24$ and $m=25$, as direct products establish. The third ratio at $m=1$ is below 1. Its numerator relative to $m+1$ decreases further while $4m+3$ increases. Thus a sign assertion valid at the whole cuts can already fail half a unit later. All four logarithms remain $O(\log(2X))$ for $X\ge1$.

## Separate the primes from the prime powers

At $X=2{,}000{,}000$, the primes give $+768.6819677$ to the displayed precision. Their squares give $-692.9124041$, and higher powers give $-68.2894435$. The sum is $+7.4801203$ before rounding. The factorial ratio yields the same result independently. The [replay](../receipt-archives/check_pal_signed_factorials.py) tests heads 50, 5,000, 500,000 and 2,000,000. For the large factorials it compares to $\frac12\log(\pi m/2)+3/(16m)$ with outward error at most $1/(70m^3)$.

There is an unconditional limit behind the cancellation. For each fixed integer $r\ge2$, as $X\to\infty$,
$$
\frac1{X^{1/r}}\sum_{\substack{p^k\le4X\\1\le k<r}}\log p\,D(X/p^k)
\longrightarrow -(2^{1/r}-2)^2\zeta(1/r).
$$
To see this, first keep only $k=r$. Scale $v=p/X^{1/r}$. On any fixed interval $\delta\le v\le 4^{1/r}$ the weight $D(v^{-r})$ is a bounded step function. The prime number theorem turns the scaled sum into its integral. The small interval $v<\delta$ costs $O(\delta)$ after scaling, since $\theta(t)=O(t)$. The substitution $y=v^{-r}$ gives the limit
$$
\frac1r\int_0^\infty D(y)y^{-1/r-1}\,dy=(2^{1/r}-2)^2\zeta(1/r).
$$
Indeed the Mellin formula on $\Re s>1$ is $\int D(y)y^{-s-1}dy=(2^s-2)^2\zeta(s)/s$. The integral is holomorphic on $\Re s>0$ because $D$ is bounded and vanishes near zero. The right side has a removable singularity at 1. Exponents $k>r$ cost $O_r(X^{1/(r+1)}\log^2(2X))$, by counting their possible prime bases and exponents. Subtract those terms and the $k=r$ limit from $F(X)=O(\log(2X))$ to obtain the formula. For $r=2$ the limit for primes alone lies between 0.5011144439 and 0.5011144440. The replay evaluates $\zeta(1/2)$ by an alternating series with outward bounds.

This signed test therefore pays a real square-root contribution. Its Mellin reading carries a factor of $\zeta(s)$, which also explains why these four rows alone cannot see the nonzero triangular reading at a zeta zero. [The residual at the endpoint](the-boundary-of-the-signed-factorial-rows.md) · [Finite results and scope](../receipt-archives/2026-11-26-pal-signed-factorial-boundary.json)
