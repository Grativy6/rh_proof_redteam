# Two roundings on the same primes

Christopher Daniel Pang and Hearthline · 26 November 2026

Use $M=16^j$, $x=4^{j+1}(j+1)^2$, $n=x^2$, and $P_m=\prod_{x<p\le m}p$. The factorial gcd test on $1\le d\le m\le M$ selects precisely these factors. For positive integer $q$ let $T(q)$ be the least $t$ with $q x^t\le(x+1)^t$. All powers and comparisons here have an integer meaning, including arbitrarily late boards.

## One flag per prime

The inequalities
$$
 T(ab)\le T(a)+T(b)\le T(ab)+1
$$
follow by multiplying the two covering inequalities and the two inequalities just before each clock covered its input. If either time is zero, that positive input is 1. When both times are positive the product is still uncovered at time $T(a)+T(b)-2$, so it takes at least one more tick. [Lean proof with integer powers](PALRH/ProductClock.lean)

Write $t_p=T(p)$ and $t'_p=T(P_p)-T(P_{p-1})$. Then $f_p=t_p-t'_p$ is a bit. If it is one, put the last original tick in the prime’s flag slot for each surviving start. Everything else is addressed by the cumulative ordinal of the product clock. In the sixteen-site example $P_{13}=5,005$. Its cumulative times at the four primes are $8,16,27,39$. The single flag at 7 pays for nine actual records across its surviving starts. [Encoder and decoder](../receipt-archives/pal_product_clock.py) · [Full finite counts](../receipt-archives/2026-11-26-pal-product-direction.json)

For the upper test define $a=\lfloor x/13\rfloor$ and $b=(a-\lceil M/x\rceil)_+$. On an active board $M\le x\lceil M/x\rceil$ and $\lceil M/x\rceil\le a$. Reserve $M$ individual flag slots and $bx$ other initial lanes for each of the $n$ rows. Together these occupy at most $nxa\le n^2/13$ positions. Slot $p-1$ in the first part identifies a flagged prime. For the ordinary product ticks use the ordinal $v=T(P_{p-1})+t$. If $v<bx$, place it in the rest of the row pocket. Otherwise use
$$
 d=x+1+\lfloor(v-bx)/x\rfloor,\qquad \lambda=(v-bx)\bmod x .
$$
If $P_p x^{H_p}\le(x+1)^{H_p}$, with $H_p=x((p-x)_++b)$, then $T(P_p)\le H_p$ so $d\le p$. A start $i<n-p$ gives a true ordered pair of sites $i,i+d$ at layer $\lambda$. The source distance and tick are recovered by the product-clock endpoints, with the flag branch reversed separately. There is also a direct ordinal layout for the original tick stream, proved in Lean using the same reserved bound. [Concrete row address and timely placement](PALRH/ProductBridge.lean)

The reverse product inequality uses $L_m=x((m-x)_+-a)_+$. If $(x+1)^{L_m}\le P_m x^{L_m}$ then $T(P_m)\ge L_m$ by strict increase of the multiplier. The actual separate ticks cover at least that many units. This gives the shortage-only bound by the same positive triangular weights.

Conversely, under RH the original Schoenfeld calculation bounds the absolute unweighted corrected tick error by $cx^2$ throughout each active board, with $c=(\log2)^2/(2\pi)$. In the original units, $\sum t_p-x(m-x)\le cx^2$ and $|(\theta(m)-m)-(\theta(x)-x)|\le cx$. Since $M/n\le1/10,000$, $x\ge25,600$ and $c+1/10,000+2/25,600<1/13$, the guard and the rounding to a whole initial column fit as well. The product clock is at most the sum of individual ticks, giving the upper comparison. For the lower comparison use $\log P_m=m-x+(\theta(m)-m)-(\theta(x)-x)$ and $x\log(1+1/x)\le1$ when the exponent is positive. The initial boards and the cuts through $x$ have $P_m=1$ and $L_m=0$. This proves the reverse implication on paper. [All constants and their ranges](why-one-thirteenth-is-enough.md#why-the-number-thirteen-works)

## Which choices carry information?

On a given board the upper time is always at least the lower time. For **any** input integer $q$, if the upper test fails then the lower test passes. Hence the assertion with the disjunction *inside* the cut quantifier gives no constraint on $q$. The theorem with the disjunction *outside* requires an orientation valid throughout a board. Its proof uses the divisor recovery locally before going to the next board. [Both exact statements](checks/product-direction/ProductChallenge.lean) · [Local sign recovery](PALRH/BoardOrientation.lean)

Here is a control using the literal fourth board’s rulers, $j=4$, $x=25,600$, $a=1,969$ and $b=1,966$. Replace the cumulative input by ones through 27,570. The lower test fails there since its exponent is $x>0$. At the next prime 27,581, submit a factor stream with 439 copies of that prime. The upper test fails there. Indeed $27,581>3^9$, $9\cdot439=3951$, and the upper test at that cut has 3,947 blocks of $x$ ticks. The binomial expansion gives $(1+1/x)^x<3$. One cut can choose up and the other down. A single orientation for that board fails. This is a deliberately altered factor stream used to test placement of the quantifier. The ordinary stream uses every retained prime exactly once. [Reproducible control](../receipt-archives/check_pal_product_clock.py)

## Two different flags

The tick flag $f_p$ above concerns a single multiplication of the clock. The column flag $g_p$ from the earlier allocation asks whether opening separate columns would require *one entire extra column*. Specifically, $g_p=\lceil t_p/x\rceil-(\lceil S_p/x\rceil-\lceil S_{p-1}/x\rceil)$ with $S_p=\sum_{\ell\le p,\ \ell>x}t_\ell$. The next result gives the limiting joint frequency for actual prime arrivals.

Let $N=\pi(M)-\pi(x)$, $\theta_j=\{\log M\}$ and $H(v)=2-v-e^{-v}/(1-e^{-1})$ on $[0,1]$. Then the two marginal frequencies are $1/2+o(1)$ and $H(\theta_j)+o(1)$, and their joint frequency is $H(\theta_j)/2+o(1)$. In particular both bits occur together at a positive fraction of actual arrivals. Each bit represents a different number of physical records. Multiplying by $n-p$ for the live starts preserves these normalized frequencies since $M/n\to0$. [Derivation of the column price](the-whole-column-a-prime-can-return.md)

**The local prices.** Put $\alpha=1/\log(1+1/x)$ and write $p_i$ for the retained primes. Under uniform sampling of their indices,
$$
 (p_i/M,\{\alpha\log p_i\})\ \Longrightarrow\ \text{uniform length on }[0,1]^2 .
$$
For a fixed subinterval of $[\eta,1]$, $\eta>0$, test a nonconstant Fourier mode $F(t)=\exp(2\pi i k\alpha\log t)$. Average the prime count over the preceding $h=\lfloor M^{1/3}\rfloor$ integers. The weighted sum differs from $h^{-1}\int F(t)(\pi(t)-\pi(t-h))\,dt$ on the scaled interval by $O_k(N\alpha h/(\eta M)+h)=o(N)$, by the mean value theorem and the number of endpoints. Zaccagnini’s Selberg-integral theorem with $\varepsilon=0$, followed by Cauchy–Schwarz, lets us replace the count by $h/\log t$ at another cost $o(N)$. A finite dyadic cover handles any fixed $\eta$. In this range $\log t/\log M\to1$ uniformly. Integrating $t^{2\pi i k\alpha}$ gives an $O_k(M/\alpha)$ bound before dividing by $\log M$. This proves the displayed equidistribution by Fourier approximation and the prime number theorem for the zero mode, then $\eta\downarrow0$. This use of a mean-square theorem concerns averages over all starts of the short window. [Zaccagnini, main theorem, page 225](https://bibliotekanauki.pl/articles/1390756.pdf)

**The two carried remainders.** Let $u_i=\{\alpha\log p_i\}$, $v_i=\{t_{p_i}/x\}$, $z_i=\{\alpha\log P_{p_i-1}\}$, and $w_i=\{S_{p_i-1}/x\}$. These are points on the circle. The state update is exactly
$$
 (z_{i+1},w_{i+1})=(z_i+u_i,w_i+v_i)\pmod1 .
$$
The total variation in the base coordinate $p_i/M$ is at most 1. The sum of circular distances of consecutive $u_i$ is at most $\alpha\log(M/x)=o(N)$ by monotonicity of the unwrapped logarithms. Likewise the variation of $v_i$ is $O(\log M)$. Thus shifting the index by one leaves every limiting empirical measure invariant under the displayed state update with the base coordinates fixed. For example, summing a continuous test function before and after the shift differs by just its two endpoints plus the effect of changes in those base coordinates. Uniform continuity and the preceding mean variation make that effect $o(N)$.

Along a subsequence with $\theta_j\to v$ on the circle, the base law is $(y,u,v(y))$ with $dy\,du$ and $v(y)=\{v+\log y\}$. This follows from the local-price calculation and $t_p/x-\log p=o(1)$ uniformly. For almost every base point, $1,u,v(y)$ are rationally independent. Indeed for a fixed integer pair $(k,\ell)\ne(0,0)$ the set where $ku+\ell v(y)$ is integral has zero area. In each conditional measure on the two carried phases, invariance forces the $(k,\ell)$ Fourier coefficient to equal itself multiplied by $\exp(2\pi i(ku+\ell v(y)))$. All its nonconstant Fourier coefficients thus vanish. The conditional state law is uniform measure on the two-dimensional torus. This establishes the independence of the two carried phases from the base at this sampling scale directly from the arithmetic update.

Away from boundary sets of limiting measure zero, $f_{p_i}=1$ exactly when $z_i<1-u_i$ and $g_{p_i}=1$ exactly when $w_i<1-v_i$. The conditional probabilities are $1-u_i$ and $1-v_i$ under independent uniform carried phases. Integrating first in $u$ gives $1/2$, then in $y$ gives $H(v)$ for the column marginal. The joint probability is their product. Every phase subsequence has this limit, giving the formulas above on the actual boards. This argument samples **arrivals**. The retired-row sum instead weights a carried remainder by the following gap length, so it continues to be accounted for by its own exact finite formula.

| Last observed cut | Neither | Column only | Tick only | Both |
|---:|---:|---:|---:|---:|
| 65,536 | 1,034 | 854 | 1,025 | 811 |
| 1,048,576 | 17,977 | 16,191 | 17,956 | 16,270 |
| 16,777,216 | 241,312 | 265,815 | 240,403 | 266,179 |

The finite replay encloses the accumulated log of the product and the individual factor by outward rational sums. If a cumulative price is close to a tick boundary the implementation recomputes all prefix enclosures at higher precision. The positive powers of $(x+1)/x$ cannot equal an integer when $x\ge2$, so refinement separates the comparison. Direct integer powers test every small-product endpoint, and the ordinary event totals agree with the separate arrival replay. The product, its two rounding flags and their actual addresses are paid for independently of any bound on the unwrapped prime drift. [Exact arithmetic, source hashes and scope](../receipt-archives/2026-11-26-pal-product-direction.json)
