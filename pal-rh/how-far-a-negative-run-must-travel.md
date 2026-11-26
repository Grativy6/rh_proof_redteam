# How far a negative run would have to travel

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). Pang’s PAL carry-and-return question led to the fourth-power test. RPL asks which earlier scale pays for a return. APCI asks whether two candidate directions were measured at the same input. This paper compares the two directions there, then uses the same arithmetic twice to price a long run. [Corpus roles](CORPUS-ROUTES.md) · [The original fourth-power deduction](what-the-first-omitted-label-sees.md#one-rational-sign-at-each-fourth-power-suffices)

**A zero off the critical line would force almost full-length runs of each sign, in the sense of power exponents.** Fix any integer $k\ge1$. Inspect the same first square pass at $x=j^k$. Let $L_+(J)$ and $L_-(J)$ count the longest run of consecutive strictly positive and strictly negative root indices in $[J^\eta,J]$, for any fixed $0<\eta<1$. Then
$$
 \lim_{J\to\infty}\frac{\log(1+L_+(J))}{\log J}=1
 \quad\hbox{unconditionally},\qquad
 \lim_{J\to\infty}\frac{\log(1+L_-(J))}{\log J}=1
 \quad\hbox{if RH fails}. \tag{1}
$$
Thus even at twelfth powers it suffices to exhibit arbitrarily late panels on which every negative run has length at most $J^{0.99}$. Any one fixed exponent below 1 works. The estimate in (1) permits a run occupying a fraction of the panel that tends to zero.

## The two readings at the same input

Write $m(d)=\mu(d)\mathbf1_{(d,6)=1}$, $w(t)=\max(0,\min(1,2-t))$ and $S_0(x)=\sum_d m(d)w(d/x)/d$. For an integer $p\ge2$ put $C_p(x)=\sum_{a\ge0}p^{-a}S_0(x/p^{2a})$. Using $p=2$ and $p=3$ together gives the first pass $S_1$. All these sums at a physical side are finite because $S_0$ vanishes through $1/2$. In log coordinates put $F(u)=e^{u/2}S_1(e^u)$ and $E_p(u)=e^{u/2}C_p(e^u)$. Direct cancellation gives
$$
 E_3(u)=F(u)-F(u-\log4),\qquad E_2(u)=F(u)-F(u-\log9). \tag{2}
$$
At each input one may take the better direction. Suppose for each $\epsilon>0$ the amount by which **both** returns are negative is at most $C_\epsilon e^{\epsilon u}$, throughout the late range. Follow the more favorable predecessor. Each backward step divides $x$ by at least 4. The accumulated debt is at most $C_\epsilon x^\epsilon/(1-4^{-\epsilon})$, plus a bounded initial cost. Hence $F(u)\ge-O_\epsilon(e^{\epsilon u})$. The bounded signed rectangle of the first pass and the four-row inverse then imply RH by the finite zero bill. [Area and inverse](how-many-square-passes-the-sign-needs.md) · [Two-direction theorem](PALRH/ClockRoutes.lean)

Only simultaneous rational readings on half-rows are required. At $x=n/2$ let $d_n=\max(0,-\max(C_2(n/2),C_3(n/2)))$. One finite arithmetic condition is that, for every positive integer $q$, there be a positive integer $A$ with $n^q d_n^{2q}\le A n$ on every sampled head. Taking roots gives the needed exponent. Between half-rows the individual clocks have relative variation at most $4(y-x)/x$ for $y\ge x>0$. That pays the rounding even if the selected direction changes. Under RH, partial summation as below gives the subpower bound for each clock separately, so the condition is also necessary on paper.

## Use the same exponent for a reading and its slope

Let $\Theta$ be the supremum of $1/2$ and the real parts of the nontrivial zeta zeros. For $\Theta<1$ and $\Theta<b<1$, the Balazard–Saias estimate implies $\sum_{n\le y}\mu(n)=O_b(y^b)$. Specifically their estimate on any line $\Re s=b$ bounds the partial sums of $\mu(n)n^{-b}$ at imaginary part zero, and ordinary partial summation gives the stated bound. Its zero-free hypothesis is satisfied by the definition of $\Theta$. The case $\Theta=1$ uses the elementary bound $y$ with $b=1$. The analytic input applies at the supremum determined by the actual zeros. [Balazard and Saias, 1998](https://doi.org/10.1006/aima.1998.1760) · [Balazard–Saias, Lemma 2 as reproduced by Báez-Duarte, Lemma 2.1](https://arxiv.org/pdf/math/0202141#page=3)

The same estimate holds for the partial sums of $m$, since $m$ is the convolution of $\mu$ with the indicator of $2,3$-smooth integers. The absolute $b$-weighted mass of that indicator is finite. For the first pass,
$$
 a_1(p^2d)=p\,m(d),\qquad p=2^i3^l,\quad(d,6)=1 ,
$$
with zero on the remaining labels. The partial sum $M_1(x)=\sum_{n\le x}a_1(n)$ therefore obeys $|M_1(x)|\ll_b x^b\sum_p p^{1-2b}\ll_b x^b$. Each single clock obeys the same bound. When $b<1$, the reciprocal partial sum has zero limit and error $O_b(x^{b-1})$. This follows by partial summation. At 1 the rough reciprocal series tends to zero and the added square factors are finite. Averaging the reciprocal partial sum gives $|S_1(x)|+|C_2(x)|+|C_3(x)|\ll_b x^{b-1}$. When $b=1$ the seed's unit bound and the geometric weights give the same assertion.

Away from half-row corners the exact derivative of $S_1$ is $[M_1(2x)-M_1(x)]/x^2$. Piecewise integration works across the corners because the readings are continuous. Consequently each of $\sqrt x S_1(x),\sqrt x C_2(x),\sqrt x C_3(x)$ has absolute derivative at most $O_b(x^{b-3/2})$ for $x\ge1$ away from those corners. This is where the signed counts improve the earlier absolute variation price.

Suppose a zero has real part $\beta>1/2$. Write $\tau=\beta-1/2$. The existing all-head lower bill, the inverse with price 4, and the first pass's signed rectangle between 0 and $O((1+\log H)^2)$ imply, for **both signs** and all sufficiently large $H$,
$$
 \int_{-\log2}^{\log H} (\pm F(v))_+\,dv\ge c_\rho H^\tau. \tag{3}
$$
Indeed $1/5\le g\le1$ on the measured rectangle, so its signed bound forces each sign to pay a fixed fraction of gross area once that area dominates the squared logarithm. [Original finite zero bill](what-the-two-signs-cost-together.md#what-a-zero-would-have-to-pay-at-every-cutoff)

Choose $0<\lambda<\tau$. At a maximum of $e^{-\lambda v}(\pm F(v))_+$ through $\log H$, write $u=\log y$. Integrating its constant upper bound against $e^{\lambda v}$ in (3) shows that the maximum is at least $c_\rho\lambda H^{\tau-\lambda}$. The global upper bound above then gives
$$
 y\gg H^{(\beta-1/2-\lambda)/(b-1/2-\lambda)},\qquad
 \pm F(u)\gg y^{\beta-1/2}. \tag{4}
$$
The maximizing value is positive. Both predecessors in (2) lie below the same tilted maximum for the chosen sign, including predecessors in the initial zero region. Subtracting shows **both** directed increments have that sign and magnitude at least $(1-e^{-\lambda h})\,c\,y^{\beta-1/2}$, with $h=\log4$ or $\log9$ as in (2).

For either sign the preceding interval of physical length $c' y^{1+\beta-b}$ keeps all three signs, by the derivative bound on $[y/2,y]$, taking the constant small enough. If RH fails, take $\lambda=(\Theta-1/2)/2$, choose $\beta$ sufficiently close to $\Theta$, and choose $b$ sufficiently close above it (or $b=1$ at the endpoint). For **any** fixed $0<\eta,\delta<1$, both exponents in (4) and in this interval estimate can be made arbitrarily close to 1. Choose them with strict slack. For all large $H$ there are then two intervals inside $[H^\eta,H]$, each of length at least $H^{1-\delta}$. On one interval all three readings are positive and on the other all three are negative. The constants may depend on the exponents and the chosen zero. Approaching the supremum suffices.

If RH holds, the earlier Gaussian localization gives, at every sufficiently large $H$, a $y$ with $cH/(1+\log H)\le y\le H/2$ and $\sqrt y S_1(y)\gg\log H$. Here $b$ may be arbitrarily close to $1/2$. The derivative bound preserves that positive sign on a subsequent interval of length at least $H^{1-\delta}$, still inside $[H^\eta,H]$. This proves the unconditional positive statement in both cases. Under RH this argument is for $S_1$. One also gets unbounded simultaneous positive records of the two directed increments by taking record highs of $F(v)-c'v$ with $c'$ smaller than the guaranteed positive growth rate. [All-scale positive localization](what-the-first-omitted-label-sees.md#positive-rows-at-arbitrarily-large-sides-after-one-pass)

Finally apply the physical conclusion at $H=J^k$. The spacing of consecutive $k$th powers through that head is at most $kJ^{k-1}$. Choose the physical loss exponent smaller than $\delta/k$ to get at least $J^{1-\delta}$ consecutive root indices of the required sign. This proves (1), including both directions simultaneously in the failure case. The direct proof for arbitrary fixed powers uses the cited analytic upper estimate. The Lean result gives the two-direction and localized-remainder implications.

## A rational statistic for simultaneous failure

At $x=j^k$ define the joint deficit as $\max(0,-\max(E_2(\log x),E_3(\log x)))$. Let $B_-(J)$ be its maximum over $J^\eta\le j\le J$. Then the following equality holds in both cases:
$$
 \lim_{J\to\infty}\frac{\log(1+B_-(J))}{k\log J}=\Theta-\tfrac12. \tag{5a}
$$
For the upper bound use $O_b(x^{b-1/2})$ for the two normalized clocks. For the lower bound when $\Theta>1/2$, the common negative interval proved above retains at least a fixed fraction of the amplitude in (4). It contains a $k$th power. The exponent of $y$ relative to $H=J^k$ can be made arbitrarily close to one while $\beta$ tends to $\Theta$. When $\Theta=1/2$, the numerator is nonnegative and the upper exponent is arbitrarily small.

For $k=12$ the normalization is simply the integer $j^6$. With, for example, $\eta=1/2$, the indices in each panel satisfy $j^2\ge J$ and $j\le J$. An equivalent paper criterion asks, for each positive integer $q$, for arbitrarily large $J$ with $B_-(J)^q\le J$. Each root contributes just two rational sums. One clock can be arbitrarily negative at a successful root if the other direction pays. The power-exponent argument, including (1) and (5a), uses the stated analytic estimate on the actual source. The every-half-row route in Lean establishes its own sufficiency independently of that estimate.

## A square clock which fails even on the critical line

A tempting shortcut is that making the square clock positive-weighted should make its own reading eventually nonnegative. Here the scales themselves can defeat that shortcut. For $z$ the log-coordinate Laplace variable, put $s=1/2+z$ and
$$
 A(z)=\frac{2^s-1}{s(s-1)(1-2^{-s})(1-3^{-s})\zeta(s)} .
$$
This is the seed transform. The single-clock transform is $A(z)/(1-e^{-h z})$, $h=2\log p$. Its pole at zero gives the positive mean coefficient $A(0)/h$. At a simple critical-line zero $\rho=1/2+i\gamma$, write $R=\operatorname{Res}_{z=i\gamma}A(z)$. The oscillatory pole has modulus $B_p=|R|/|1-e^{-i\gamma h}|$ if the denominator is nonzero. Then
$$
 \liminf_{u\to\infty} E_p(u)\le A(0)/h-B_p,\qquad
 \limsup_{u\to\infty} E_p(u)\ge A(0)/h+B_p. \tag{5}
$$
For the first bound, assume $E_p\ge -L$ eventually. Add $L$ on the positive ray and correct its bounded initial part to obtain a nonnegative function. Its transform is regular on the positive real axis, hence its integral converges for every $\Re z>0$ by the nonnegative Laplace argument. At $\sigma+i\gamma$ its modulus is bounded by its value at $\sigma$. Multiply by $\sigma$ and send $\sigma$ to zero. The latter side tends to $A(0)/h+L$, the former to $B_p$. An arbitrarily small slack handles the liminf. Apply the same argument to the opposite sign. If the clock denominator vanishes at $i\gamma$, the nonreal pole has higher order and neither one-sided bound can be finite. [Nonnegative Laplace argument](what-the-last-two-rows-carry.md)

A finite rational computation encloses a unique simple zero on the critical line within $10^{-7}$ of $1/2+14.13472514i$. It gives $9<A(0)<10$ and $0.00561<|R|<0.00574$. At the following primes (5) forces strict negative excursions of the actual arithmetic.

| Square clock root $p$ | Upper bound for its normalized liminf |
| ---: | ---: |
| 3,727 | $-0.141$ |
| 4,657 | $-0.344$ |
| 22,063 | $-2.34$ |

For example, the square clock rooted at 3,727 goes negative at unbounded fourth powers. Under RH, its strict normalized dip and the slope bound with $b$ near $1/2$ give unbounded negative intervals of length $y^{1-\delta}$. If RH fails, this single clock has the same finite inverse estimate with factor 2, a signed rectangle of size $O(1+\log H)$, and the identical power-exponent argument. The same conclusion applies on every fixed power grid. A direct Möbius sum gives a finite example at side $(3727^2+1)/2=6{,}945{,}265$. The newly admitted smaller input is just over $1/2$ and contributes exactly $2/[3727(3727^2+1)]>0$. The resulting single-clock reading is still below $-5\times10^{-7}$. The first frequency tested gives no negative upper bound for 2, 3, 577 or 2,663. For any $p$ with $\log p>1800$, (5) or exact resonance forces negative values since $|R|>1/180$ and the circular chord is at most two.

For the numerical enclosure, Euler–Maclaurin at 64 with six correction terms encloses $\zeta$ at the center and at its two real offsets $10^{-6}$. The absolute remainder is bounded by $4(15\cdot16\cdots26)/(6^{12}\cdot11\cdot64^{11})$ there. On the concentric quarter-radius disk the same bounds give $|\zeta|<100$. Cauchy's estimate on the eighth-radius interior gives $|\zeta''|\le12800$. A central difference bounds the first derivative, and on the $10^{-7}$ circle the linear term dominates the constant and quadratic remainder. Rouché gives one zero counted with multiplicity. Conjugation and the functional equation reflect it within that same disk, fixing its real part. The receipt gives the enclosures before the clock comparison. [Integer interval replay](../receipt-archives/check_pal_clock_resonance.py) · [Euler–Maclaurin formula](https://dlmf.nist.gov/25.2#iii) · [Functional equation](https://dlmf.nist.gov/25.4)

## Unresolved

Earn a fixed power saving in the longest negative run in arbitrarily late panels, or control the simultaneous debt of both directions. Across 901 clock-grid visits to 663 distinct physical sides the two actual directions both paid. At side 432 billion two different primes, 929,501 and 929,507, each admit one genuine positive earlier return yet both resulting single-clock readings are negative. The particular phase and the retained arithmetic matter. The [reflected-cell calculation](what-a-reflected-remainder-carries.md) isolates the signed part of that arithmetic on the actual label grid. [Finite evidence](../receipt-archives/2026-11-25-pal-reflected-cells.json)
