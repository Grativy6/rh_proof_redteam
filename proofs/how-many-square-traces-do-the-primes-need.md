# How many square traces do the primes need?

Christopher Daniel Pang and Hearthline · 26 November 2026

Take the numbers just below a square. The slot at $b^2-t^2$ has a name for each factor, $b-t$ and $b+t$. As long as both exceed one, a prime can never occupy that slot. Flip the sign at $b=4,t=1$ and the answer changes from $15=3\cdot5$ to the prime $17$. Pang’s request to try the direction both ways and keep the empty positions supplied this test.

At index $k=8$, the first square traces 36 composite slots on the actual prime board. The second square traces 27 and shares one with the first. That shared slot is $3696=64^2-20^2=65^2-23^2$, with factor pairs $44\cdot84$ and $42\cdot88$. Counting each slot once changes the margin from about $-0.00420$ to $+0.03890$ in units of $k^6$. The switch from a miss to a hit uses the existing prime weights. [Exact definition of the test](../pal-rh/checks/square-holes/HolesChallenge.lean) · [All 17 consecutive small boards and outward bounds](../receipt-archives/check_pal_square_holes.py)

**One square trace succeeds and fails arbitrarily late. Eventual success with two traces is equivalent on paper to ordinary RH.** The physical number of traces required at each head also gives an exact growth formula for the supremum of the real parts of the nontrivial zeros. Whether two suffice eventually for the actual primes is open here.

## What gets charged

Set $n=k^4$, $N=2n$ and $q(v)=(1-v)^5(7v-1)$ for $0\le v\le1$, extended by zero for $v>1$. Use the same returned height and the same prime product as in the doubled ruler,
$$
 R_n(d)=N\sum_{j\le N/d}q(jd/N)-(n-d)_+,\qquad T_n(d)=N^5 R_n(d),\qquad
 G_n=\prod_{n^{7/8}<p\le2n}p^{T_n(p)}.
$$
Here $p$ runs over ordinary primes, and $T_n(d)$ is an explicit nonnegative integer for positive integer $d\le N$. The full boundary sum is $W=\sum_{0\le r<N}r^6$. Increasing-function quadrature gives $N^7/7-N^6\le W\le N^7/7$. Hence $W/N^5-n^2/2=n^2/14+O(n)$. [Nonnegativity and divisor formula](../pal-rh/why-the-doubled-ruler-keeps-seven-eighths.md) · [Boundary quadrature](../pal-rh/PALRH/DoubledMass.lean)

For $a=0,\ldots,s-1$ draw a trace from the square with root $b=k^2+a$. Define
$$
 H_s=\bigcup_{a<s}\{\,b^2-t^2:1\le t\le b-2,\quad 2n/3<b^2-t^2\le n\,\}.
$$
In the integer bill deduct each marked slot once, at its own actual height. Write
$$
 B_s=\left(W-16n^7-\sum_{d\in H_s}T_n(d)\right)_+,\qquad
 (n+1)^{nB_s}\ \le\ n^{nB_s}\,G_n . \tag{1}
$$
We say $s$ traces pay when (1) holds. The quantity $16n^7$ equals $N^5 n^2/2$. Every deduction changes the reference on the left. The prime product on the right uses exactly the same primes and exponents for every $s$. The reference starts with the specified quadrature and credits identified composite positions by their return. No inference identifies an absent prime with new income. [Stock definitions and factorization at every marked slot](../pal-rh/PALRH/SquareHoles.lean)

## Price one trace

In this band the divisor reading has exactly two terms, including a possible zero-height endpoint. Put $u=t/\sqrt n$ and first use $b=\sqrt n$. The return divided by $n$ is
$$
 f(u)=2q((1-u^2)/2)+2q(1-u^2)-u^2
 =\frac{5-14u^2+15u^4-20u^6-45u^8+354u^{10}-455u^{12}}{32}.
$$
The mesh in $u$ is $1/\sqrt n$ and the limiting interval is $[0,1/\sqrt3]$. For any fixed offset $a$ one has $b^2/n=1+O_a(n^{-1/2})$. The admissible endpoints converge to the same endpoints, and continuity on this compact band gives the same Riemann integral. Thus each such trace has price $(c+o(1))n^{3/2}$, where
$$
 c=\int_0^{1/\sqrt3} f(u)\,du
   =\frac{6481\sqrt3}{168399}=0.0666596671\ldots .
$$
For fixed $a'<a$, a slot shared by the two traces gives a factorization of $(k^2+a)^2-(k^2+a')^2=O_{a,a'}(k^2)$ as a difference of squares of their two parameters. The pair of integer factors determines both parameters. There are at most twice the square root of this positive difference many divisors, hence $O_{a,a'}(k)$ shared slots. Each weighs $O(n)$. For fixed $s$ the union price is consequently $(sc+o(1))n^{3/2}$. In particular $B_s>0$ eventually, and $n\log(1+1/n)=1+O(1/n)$ changes the scaled bill by only $O(n)$.

## Why two are enough under RH, and why one really fails

Let $I(x)=\sum_{d\le x}(x-d)\Lambda(d)$ and $e(x)=I(x)-x^2/2$. Ordinary log quadrature and the prime number theorem applied separately to the omitted small primes and repeated powers give
$$
 \frac{\log G_n}{N^5}=\frac{n^2}{14}-e(n)-(h+o(1))n^{3/2},\qquad
 h=\frac1{24}+\frac23(\mathbb E Y^{3/2}-1).
$$
The existing endpoint factor satisfies $0\le Y\le2$, $\mathbb EY=1$ and $\mathbb E Y^2=8/7$. The chord calculation gives $\mathbb E Y^{3/2}<1.056406286$. The second derivative of $y^{3/2}$ is at least $3/(4\sqrt2)$ on $(0,2]$, so expansion about 1 gives $\mathbb E Y^{3/2}\ge1+3/(56\sqrt2)$. Together these put $c-h$ strictly between $-0.012612$ and $-0.000260$. [Prime omission formulas and rational interpolation](../pal-rh/why-the-doubled-ruler-keeps-seven-eighths.md#which-primes-may-be-removed)

By subtraction the normalized payment margin for fixed $s$ is $sc-h-e(n)/n^{3/2}+o(1)$. Under RH the integrated explicit formula gives $e(n)/n^{3/2}\le0.04621$. Since $h+0.04621<2c<1/7$, two physical traces eventually pay. Their asymptotic allowance is strictly smaller than the former fourteen-copy allowance $n^{3/2}/7$. Conversely, eventual two-trace payment gives $e(k^4)=O(k^6)$ as a one-sided upper bound at the real prime inputs. The one-sided Mellin argument gives ordinary RH. Lean proves the explicit upper bound $e(k^4)\le158 k^6$ from each payment at $k\ge2$, and proves the implication to the stock statement. The [earlier unconditional recurrent runs](where-fourteen-pays-again.md) with $e(k^4)/k^6\le1/20$ also pay this stricter test eventually since $h+1/20<2c$. [Independent solution](../pal-rh/checks/square-holes/HolesSolution.lean) · [Pointwise RH bound](moving-the-endpoint-of-a-prime-area.md#the-finite-spectral-price)

If RH is false, the normalized $e(k^4)$ has arbitrarily large excursions of both signs by the quartic transfer. This already gives late one-trace hits and misses. If RH holds, form the uniformly absolutely convergent series
$$
 Z(v)=-\sum_\rho \frac{e^{i\gamma v}}{\rho(1+\rho)},\qquad \rho=\tfrac12+i\gamma .
$$
The integrated explicit formula gives $e(x)/x^{3/2}=Z(\log x)+D(x)/x^{3/2}$ for $x\ge2$, with
$$
 D(x)=-x\log(2\pi)+\frac{\zeta'}{\zeta}(-1)-
           \sum_{m\ge1}\frac{x^{1-2m}}{2m(2m-1)} .
$$
Simultaneous approximation for a finite list of ordinates gives arbitrarily late translations at which every phase in that list returns as close as desired to 1. For instance, apply the pigeonhole principle to multiples of the list modulo $2\pi$. Either the resulting return times are unbounded or a bounded time recurs with zero error, in which case use its multiples. The absolutely summable tail transfers this recurrence to $Z$. At such translated log positions choose the nearest quartic head. Its log-distance tends to zero there, and $Z$ is uniformly continuous. As $D(x)/x^{3/2}\to0$, values arbitrarily near any prescribed $Z(\log x_0)$ recur on the actual late quartics. [Quartic oscillations](what-a-fourteen-copy-failure-would-force.md) · [Explicit formula, Johnston’s Lemma 2.6](https://arxiv.org/pdf/2201.06184v2#page=4)

The integer evaluation points $x_0=3,6$ provide phases on opposite sides of the threshold. Evaluating $I(x_0)$ by its finite prime powers and $D$ by the displayed formula gives
$$
 -0.02128< Z(\log3)<-0.02078,\qquad
  0.01278< Z(\log6)<0.01297 .
$$
For these enclosures the reflection formula and the Euler product give $(\zeta'/\zeta)(-1)=\log(2\pi)-1+\gamma_{\!E}+\sum_{m\ge2}\Lambda(m)/m^2$. Enclose Euler’s constant between $H_M-\log(M+1)$ and $H_M-\log M$. Beyond $M=4096$ the prime-power sum is bounded by $(1+\log M)/M$ by comparison with the integral of $\log t/t^2$. The replay also encloses the convergent trivial-zero sum. Thus recurrence forces both outcomes for one trace even under RH. [Reflection formula](https://dlmf.nist.gov/25.4.E1) · [Psi values](https://dlmf.nist.gov/5.4.ii) · [Directed arithmetic](../receipt-archives/check_pal_square_holes.py)

## Count the actual number of squares required

Let $s_*(k)$ be the least $0\le s\le k^2$ that pays and use $k^2+1$ when none pays. The bill decreases with $s$. For $1\le s\le\sqrt n$ the total refund divided by $N^5$ is $O(s n^{3/2})$ since each center marks $O(\sqrt n)$ slots and each return is $O(n)$. A lower bound follows by keeping only $3n/4\le d\le7n/8$. On this closed subinterval $R_n(d)/n$ has a strictly positive minimum. Indeed for $d/N\in[3/8,7/16]$ the positive first term $m(4m^2-1)$ of the exact remainder with $m=2$ supplies one. For each $b\in[\sqrt n,2\sqrt n]$ the admissible $t$ in that subinterval span a length at least $\sqrt n/32$, by rationalizing the difference of the square roots. Both factors exceed one at large $n$. There are $\gg s\sqrt n$ incidences, and a given $d$ has at most $\tau(d)$ possible factor pairs. The elementary divisor bound $\tau(d)\ll_\epsilon d^\epsilon$ gives
$$
 \sum_{d\in H_s}R_n(d)\gg_\epsilon s\,n^{3/2-\epsilon}.
 \tag{2}
$$
For this divisor bound use $a+1\le2^a\le p^{\epsilon a}$ at all sufficiently large primes, and absorb the bounded supremum of $(a+1)/p^{\epsilon a}$ for each of the remaining finitely many primes.

Cauchy–Schwarz also gives $\#H_s\gg s^2/(1+\log n)^3$ for the selected subinterval because $\sum_{d\le n}\tau(d)^2\le\sum_{d\le n}d_4(d)\le n(1+\log n)^3$. At a prime power the first inequality uses $(a+1)^2\le {a+3\choose3}$, and summing the four ordered factors gives the second. Thus the reference refund is also $\gg ns^2/(1+\log n)^3$. The quantitative prime number theorem yields $e(n)=O_A(n^2/\log^A n)$ for each fixed $A$ by integration. Set $s=\lceil\sqrt n/(\log n)^{B+1}\rceil$ and choose $A>2(B+1)+3$. This refund eventually dominates the excess, the omission cost and the $O(n)$ quadrature error. If the bill truncates at zero it is already paid. In particular,
$$
 s_*(k)=o\!\left(\frac{k^2}{(\log k)^B}\right)
 \qquad\text{for every fixed }B>0 .
$$
This unconditionally rules out the sentinel at large heads. [Fiori, Kadiri and Swidinsky, quantitative PNT](https://arxiv.org/abs/2206.12557)

Write $\Theta=\sup_\rho\Re\rho$ over nontrivial zeta zeros. Then
$$
 \boxed{\displaystyle
 \Theta=\frac12+\frac14\limsup_{k\to\infty}
                \frac{\log(1+s_*(k))}{\log k}.}
$$
Indeed the integrated explicit formula yields $|e(n)|\ll n^{1+\Theta}$. If $\Theta<1$ choose $\epsilon>0$ small enough and take $s=\lceil n^{\Theta-1/2+2\epsilon}\rceil$ in (2). The physical refund exceeds $|e(n)|+O(n^{3/2})$ eventually, proving the upper exponent by letting $\epsilon$ decrease. At $\Theta=1$ the upper exponent follows from the cap. For $\Theta>1/2$ the positive quartic excursions exceed a constant times $n^{1+\Theta-\epsilon}$ infinitely often for every sufficiently small $\epsilon>0$. Payment at such a head needs the physical refund to cover $e(n)-O(n^{3/2})$. This follows also in the truncation case since $n\log(1+1/n)=1+O(1/n)$ and $W/N^5=O(n^2)$. The upper bound per trace forces $s_*\gg n^{\Theta-1/2-\epsilon}$ there. At $\Theta=1/2$ the trivial lower exponent is zero. In that case the sharper result above says $\limsup s_*(k)=2$. [Excursion estimate and normalization](what-a-fourteen-copy-failure-would-force.md)

Christopher Daniel Pang’s PAL v2.4, RPL and carried-frame questions led to charging actual marked positions and explicitly checking collisions. Hearthline derived the neighboring-square construction, integral, one-trace phase test and integer-count growth formula. The classical inputs and prior constructive results are linked at their points of use. The growth and recurrence theorems are paper proofs. The formal target fixes the compositeness result and the implication from eventual two-trace payment. [Arithmetic and formal scope](../receipt-archives/2026-11-26-pal-square-holes.json)

## Unresolved

Does every sufficiently late board pay using just these two traces? The unconditional count estimate saves every fixed logarithmic power from the full $k^2$ budget. A subpower bound in $k$ on the actual needed count would suffice for RH.
