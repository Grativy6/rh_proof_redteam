# Why the doubled ruler keeps seven eighths

Christopher Daniel Pang and Hearthline · 26 November 2026

The [reader edition](../proofs/one-seventh-at-the-boundary.md) gives the integer test and a four-mark example. Here $t_+=\max(t,0)$ and $I_\psi(x)=\sum_{d\le x}(x-d)\Lambda(d)$.

## The returned height is nonnegative

Put $q(u)=(1-u)^5(7u-1)$ for $0\le u\le1$ and zero beyond 1. For $0<v\le1$ put $z=1/v$, $m=\lfloor z\rfloor$, $a=z-m$, and $w(v)=\sum_{j\le z}q(jv)$. Write
$$
 E=\sum_{j=1}^m(z-j)^5(7j-z)-z^6/2+z^5 .
$$
Then $w(v)=1/2-v+v^6 E$. Finite polynomial summation gives
$$
 6E=m(4m^2-1)+12am^2+15ma^2(1-a^2)+6ma^5(3-a)+3a^5(2-a).
 \tag{1}
$$
Every displayed term is nonnegative for $m\ge1$. Another expansion, with $b=a(1-a)$, gives
$$
 \tfrac23 z^3-E
 =m(1/6-b^2/2-b^3)+a^3\bigl(1/6+(1-a)(1+a-a^2)/2\bigr).
 \tag{2}
$$
It lies between zero and $m/6+2/3$ since $0\le b\le1/4$ and $0\le a\le1$. Both identities can be proved by induction on $m$ holding the real $z$ fixed. Thus $w(v)=1/2-v+(2/3)v^3+O(v^5)$ at zero. A mark $0<d\le n$ on the board $N=2n$ has extra height $R_n(d)=Nw(d/N)-(n-d)_+$ satisfying
$$
 0\le R_n(d)\le\frac{2d^3}{3N^2},\qquad
 R_n(d)=\frac{2d^3}{3N^2}+O(d^5/N^4).
 \tag{3}
$$
For $n<d\le N$ only the first $q$ term remains, and its argument is at least $1/2$. Past $N$ the extra height is zero. [Polynomial counting identities](PALRH/DoubledRuler.lean) · [Leading cubic and its remainder](PALRH/DoubledMass.lean)

To recover an actual distribution with these readings, differentiate on $0<v<1$. The endpoint at 1 has more than two vanishing orders, so there are no derivative jumps at $v=1/j$. Because $q''(u)=30(1-u)^3(7u-3)$, the sign of $w''(v)$ is the sign of
$$
 \sum_{j=1}^m j^2(z-j)^3(7j-3z)
 =\frac{m(m+1)}6\bigl[(m-1)(1-6a^2(1-a)^2)+3a^3(4-3a)\bigr].
$$
The equality follows by polynomial summation. Its sign uses $a(1-a)\le1/4$. The convex extension has limiting slope $-1$ at 0 by (2), and slope zero at 1. Integrating the density $w''$ now gives a probability law for $V\in[0,1]$ with $\mathbb E(V-v)_+=w(v)$. This can first be done on $[\delta,1]$ with $\delta>0$, followed by monotone convergence at 0. In particular $\mathbb EV=1/2$. The cutoff integral in the reader edition gives $\mathbb EV^2=2\int_0^1 w(v)dv=2/7$. Put $Y=2V$, so $\mathbb EY=1$, $\mathbb EY^2=8/7$, and $0\le Y\le2$. A finite sum of row integrals at zero misses the mass described in the reader edition. [Curvature and reciprocal-mesh bracket in Lean](PALRH/DoubledMass.lean)

As a function of the mark $d$, $R_n(d)=\mathbb E(nY-d)_+-(n-d)_+$ increases up to $n$ and decreases thereafter. This follows by taking one-sided derivatives of the two ramps. It vanishes at 0 and at $2n$ and reaches $R_n(n)=5n/32$. Its total variation is $5n/16$.

## Price the moved reading with ordinary integers

At an integer $N=2n$ set $J_N(m)=(N-m)^5(7m-N)$. The numerator of the extra height is
$$
 T_n(d)=\sum_{j\le N/d}J_N(dj)-N^5(n-d)_+ .
$$
This integer equals $N^5R_n(d)$. Regrouping $m=dj$ and using $\sum_{d\mid m}\Lambda(d)=\log m$ yields the exact equality
$$
 F_N:=\mathbb E I_\psi(nY)=\frac1{N^5}\sum_{m=1}^N J_N(m)\log m
     =I_\psi(n)+\sum_{d\le N}R_n(d)\Lambda(d).
 \tag{4}
$$
No infinite interchange occurs here.

For $G(m)=m(N-m)^6$ and $a=N-m$, subtract $G(m-1)-G(m)$ from $J_N(m)$. The result is $6ma^5-(m-1)[(a+1)^6-a^6]$. It is between $-30N^5$ and $6N^5$ because $6a^5\le(a+1)^6-a^6\le6(a+1)^5$ and $(a+1)^5-a^5\le5(a+1)^4$. Summation by parts gives
$$
 \sum_{m=1}^N [G(m-1)-G(m)]\log m
 =\sum_{m=1}^{N-1}(N-m)^6 m\log(1+1/m).
$$
Use $m/(m+1)\le m\log(1+1/m)\le1$. The sum of sixth powers of the integers from 0 to $N-1$ is between $N^7/7-N^6$ and $N^7/7$ by integral comparison. The harmonic correction costs at most $N^6\log N$. This proves
$$
 \frac{N^2}{7}-32N(1+\log N)\le F_N
 \le\frac{N^2}{7}+6N\log N . \tag{5}
$$
The upper bound and the exact labelled identity are proved in the pinned Lean project. [Elementary upper estimate](PALRH/DoubledPrice.lean)

We use a tighter elementary quadrature for the smaller numerical heads. For $N\ge1000$, $|F_N-N^2/7|\le2N$. Indeed, $F_N/N=\sum_{m=1}^N f(m)$ with $f(t)=q(t/N)\log t$. Its integral from 0 to $N$ is $N/7$ by $\int q=0$ and integration by parts against $\log u$ using $q=-[u(1-u)^6]'$. The integral over the missing first half-cell has absolute value at most $(1+\log2)/2$. Compare each remaining cell $[m-1/2,m+1/2]$ with its midpoint, extending $q$ by zero above 1. The error per cell is at most $\sup|f''|/24$ by the second-order Taylor bound. The polynomial gives $|q|\le1$, $|q'|\le30$, $|q''|\le120$. The first bound also follows from the unique interior maximum at $2/7$. Since $t\ge m/2$, summing the three derivative terms costs at most
$$
 \sum_m\sup|f''|\le 8+240(1+\log N)/N.
$$
Here $\sum m^{-2}\le2$ and $\sum_{m\le N}m^{-1}\le1+\log N$. These prices give the stated bound.

## Which primes may be removed?

Write $D=\lfloor n^{7/8}\rfloor$. The ordinary prime number theorem and partial summation give $\sum_{p\le D}p^3\log p\sim D^4/4$. For $D\to\infty$, $D=o(n)$, (3) then gives
$$
 \sum_{p\le D} R_n(p)\log p
    =\frac{D^4}{24n^2}(1+o(1)).
 \tag{6}
$$
The error from the $d^5/N^4$ term is $O(D^6/N^4)$ using $\theta(D)=O(D)$.

Let $I_{\rm rep}=I_\psi-I_\theta$ count all but the first powers of primes. The squares give $\psi(t)-\theta(t)\sim\sqrt t$ by the prime number theorem, while the remaining powers have total weight $O(t^{1/3}\log^2(2t))$. Integration gives $I_{\rm rep}(t)\sim(2/3)t^{3/2}$. The law of $Y$ is fixed and bounded. Dominated convergence in the identity $\sum_{a\ge2,p}R_n(p^a)\log p=\mathbb E I_{\rm rep}(nY)-I_{\rm rep}(n)$ therefore gives a returned repeat cost of
$$
 \left[\tfrac23(\mathbb EY^{3/2}-1)+o(1)\right]n^{3/2}.
 \tag{7}
$$
Cauchy–Schwarz gives $\mathbb EY^{3/2}\le\sqrt{8/7}$. A sharper finite price appears below.

Now let $G_n$ be the prime product in the reader edition, $n=k^4$, $N=2n$ and $A=N^5 n(n-k^2)^2$. The log of $G_n$ divided by $N^5$ is the sum of the retained first-power returns. If $(n+1)^A\le n^A G_n^{14}$ at all sufficiently late $k$, this return is at least $n(n-k^2)^2\log(1+1/n)/14=n^2/14-O(n^{3/2})$. All omitted returns are nonnegative. Equations (4) and (5) imply $I_\psi(n)\le n^2/2+O(n^{3/2})$ at those fourth powers. The earlier one-sided implication gives ordinary RH. The formal proof establishes a single constant 52 for this last area bound under the integer premise. [Fixed challenge](checks/doubled-ruler/RulerChallenge.lean) · [Submitted implication](checks/doubled-ruler/RulerSolution.lean) · [From area to ordinary zeros](how-one-sided-prime-area-reaches-rh.md)

Conversely assume RH. The integrated explicit formula gives $I_\psi(n)-n^2/2\le0.04621n^{3/2}$ for $n\ge2$, using the reciprocal-square sum and the nonpositive elementary remainder. Subtract this bound, (6) and (7) from the lower estimate in (5). The resulting three costs in $n^{3/2}$ units total at most
$$
 0.04621 + 1/24 + (2/3)(\sqrt{8/7}-1)+o(1)<1/7 .
$$
The right side of the required log comparison, viewed as a demand on the retained returns, is $n^2/14-n^{3/2}/7+O(n)$. Thus the prime product pays eventually under RH. The cited explicit-formula argument is used here in the direction *from* RH. [Elementary remainder and two-sided ordinate normalization](../proofs/moving-the-endpoint-of-a-prime-area.md#the-finite-spectral-price) · [Brent, Platt and Trudgian, Corollary 1](https://maths-people.anu.edu.au/brent/pd/rpb276-MC-preprint.pdf)

For any fixed $\alpha$ strictly between $7/8$ and 1, cutting at $n^\alpha$ costs asymptotically $n^{4\alpha-2}/24$ by (6). This exceeds every constant times $n^{3/2}$. If RH holds, the full return is $n^2/14+O(n^{3/2})$ by the two-sided integrated explicit formula and (5), so the stronger clock fails eventually. If RH fails, eventual payment for the stronger clock would imply payment for the original one and hence RH. Thus the stronger clock fails at arbitrarily late fourth powers in either case. A cutoff with exponent at least one removes at least as many labels.

### One extra copy settles all sizes

Use the same $A$, the same labels and the same $G_n$, and vary only the number of copies on the right. **Fifteen copies fund every quartic head. Thirteen copies fail at every $k\ge512$.** Thus at every such head the minimum number of copies is either 14 or 15. It is 14 throughout $512\le k\le2^{36}$.

Here is the unbounded part of that assertion. The continuum price is $\int_0^{2n}R_n(t)\,dt=n^2/14$ by the second moment of $Y$. For $n\ge2^{36}$, the bound $|\theta(t)-t|\le0.002t$ above $2^{26}$, proved in the finite-range section below, gives $\sup_{t\le2n}|\theta(t)-t|\le0.004n$. Below $2^{26}$ the elementary bound $|\theta(t)-t|\le t$ suffices. Integration by parts and the total variation $5n/16$ put the first-prime return within $n^2/800$ of its continuum price. By (3), cutting the small primes costs at most $2D^3\theta(D)/(3N^2)\le(\log4)n^{3/2}/6<n^{3/2}/4$. Consequently, for $L_n=(\log G_n)/N^5$,
$$
 \frac1{14}-\frac1{800}-\frac1{4\sqrt n}\ \le\ \frac{L_n}{n^2}\
 \le\ \frac1{14}+\frac1{800}.
$$
At $n\ge2^{36}$ the lower price times 15 exceeds one. The upper price times 13 is below $0.95$. The clock demand in the same $n^2$ units is between $[n/(n+1)](1-1/\sqrt n)^2>0.99$ and 1. Below this range 15 copies are enough by the direct and finite 14-copy results. These unconditional comparisons are on paper.

## Every fourth power through index $2^{36}$

The finite part combines independent arithmetic at small heads with the published zero height $3\cdot10^{12}$ and the unrestricted-tail estimate at large heads. It uses no assumption about later zeros. To bound $\mathbb EY^{3/2}$ by elementary rational arithmetic, interpolate the convex function $v^{3/2}$ by chords on $(i/96)^2$ for $0\le i\le96$. Every chord slope is rational. Its averaged piecewise-linear envelope is the first slope times $\mathbb EV$ plus successive slope differences times $w((i/96)^2)$. Multiplying by $2\sqrt2$ gives $\mathbb EY^{3/2}<1.056406286$. [Outward numerical replay](../receipt-archives/check_pal_doubled_ruler.py)

It suffices that the raw excess $I_\psi(n)-n^2/2$, the repeated-power return, the removed first-prime return, and the lower quadrature error plus $n/14$ total less than $n^{3/2}/7$. Indeed $n\log(1+1/n)\le1$, so the clock requires at most $(n-k^2)^2/14$ per $N^5$.

| Fourth-power index | How every head is covered | Upper cost in $n^{3/2}$ units |
|---:|---|---:|
| $1$ through $24$ | Direct outward log comparison of the integer products | All pass, equality at 1 |
| $25$ through $512$ | Direct repeated powers and a cubic prime moment | $0.137062$ |
| $512$ through $2^{30}$ | Uniform cumulative bounds on each source | $0.141322$ |
| $2^{30}$ through $2^{36}$ | Finite-height area and uniform prime-power prices | $0.138353$ |

The following details specify the bounds so that the recorded finite computations can be rerun. [Arithmetic and source hashes](../receipt-archives/2026-11-26-pal-doubled-ruler.json)

1. The pointwise 21-move area estimate previously proved in this program bounds the raw excess through $2^{120}$ by $0.04622n^{3/2}$, and through $2^{144}$ by $0.058396n^{3/2}$. It includes a tail above the finite height with unrestricted real parts. [Formula and source conditions](../proofs/when-crossed-prime-powers-pay-the-tenth.md#returning-the-prime-dials-to-a-pascal-row) · [Finite height](https://arxiv.org/abs/2004.09765)
2. For $25\le k\le512$, direct sieving supplies all $p^a\le2n$ with $a\ge2$. Use the exact integer $T_n(p^a)$ and outward logs. For primes through $D$, (3) costs at most $2\sum_{p\le D}p^3\log p/(3N^2)$. Use an exact sieve with outward logs up to the chosen prefix of at least $2^{19}$. Beyond that prefix partial summation bounds the cubic moment divided by $D^4$ by $1/4+(13/7)(\log D)^2/(24\lfloor\sqrt D\rfloor)+2\log D/D+3(599/D)^4$. This follows from Johnston’s finite $\theta$ estimate for $u\ge599$ with an extra $\log u$ for endpoint conventions. Below 599 use $|\theta(u)-u|\le u$ from the elementary bound $\theta(u)\le u\log4$. The midpoint bound in (5)’s refinement costs at most $4n$. [Johnston, Corollary 3.3](https://link.springer.com/article/10.1007/s11139-022-00616-x)
3. For $2^{36}\le n\le2^{120}$, integration by parts against the variation $5n/16$ prices the difference between the prime-square return and $(2/3)n^{3/2}(\mathbb EY^{3/2}-1)$. Its absolute value is at most $(5n/16)\sup_{u\le\sqrt{2n}}|\theta(u)-u|$. The supremum in $\sqrt n$ units is at most the larger of $599/2^{18}$ and $(6/5)13^2/(24\cdot512)+13/2^{18}$. For $u\ge599$ use Johnston at $\sqrt{2n}$, bounding the growing numerator there. After normalization the expression decreases with $n$ on this range. Higher powers cost at most $5n(\log4)[(2n)^{1/3}+(2n)^{1/4}+\log_2(2n)(2n)^{1/5}]/32$. Divided by $n^{3/2}$ these costs are largest at $2^{36}$. For the removed small-prime moment, $|\theta(t)-t|\le0.002t$ above $2^{26}$. Johnston gives this up to $10^{26}$ and the Fiori–Kadiri–Swidinsky row at $e^{50}$ covers later inputs. Below $2^{26}$ use $|\theta(t)-t|\le t$. Here $D\ge2^{31}$, so the moment divided by $D^4$ is at most $1/4+(7/4)0.002+3/2^{20}$. [Authors’ relative prime-count bounds, Table 2](https://www.cs.uleth.ca/~fiori/Docs/PrimeCountingTables.pdf#page=3) · [Uniform interpretation, Definition 5](https://arxiv.org/pdf/2206.12557v2#page=5)
4. For $2^{120}\le n\le2^{144}$ use $|\psi(t)-\theta(t)-\sqrt t|\le\sqrt t/2000$ throughout $2^{80}\le t\le2^{145}$. The square error in units of $\sqrt t$ is at most $28^2/(24\cdot2^{20})$ plus the endpoint correction $\log(\sqrt t)/\sqrt t$ if that convention is used. Both terms decrease across this range. Cubes and higher powers add at most $(7/5)(2^{-13}+80/2^{20})$ in the same units. Below $2^{80}$ the crude integrated error is at most $2^{135}$ using $(145^2+1)\sqrt t$ for the pointwise error on $1\le t\le2^{80}$ and $\sqrt t$ below 1. Thus (7) has upper error at most $(2/6000)(\mathbb EY^{3/2}+1)n^{3/2}+2^{136}$. For $D\ge2^{105}$ the relative $\theta$ bound $10^{-6}$ above $2^{80}$ follows from the same row at $e^{50}$. Partial summation and (3) then bound the removed first primes. The lower price in (5) suffices here.

## Unresolved

For each late quartic head, do the first-power primes between $n^{7/8}$ and $2n$ have enough total returned height to fund the integer clock? The full moved reading and the cost of removing the earlier primes have all-scale proofs. The retained-prime lower bound through arbitrarily large heads remains open.
