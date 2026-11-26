# What the shape of a prime board forces

Christopher Daniel Pang and Hearthline · 26 November 2026

Let $n=k^4$, $x=k^2$, and $t_p=\lceil\log p/\log(1+1/x)\rceil$ for primes $x<p\le n$. The underlying definition uses the least integer power covering $p$. Write $T_d=t_d$ for those primes and $T_d=0$ otherwise. The factorial gcd test determines this support using only integer arithmetic. For $0\le m\le n$ put

$$
 P_m=\sum_{d=1}^m(n-d)T_d,\qquad A_m=\sum_{d=1}^m(n-d)=nm-m(m+1)/2 .
$$

There are $J=2P_n$ oriented trip records. Always use the measured height $H=\lceil J/n^2\rceil$ for travel. An ordered pair of sites contributes at distance $|i-i'|$. The number of cell positions at distances at most $m$ is $C(m)=H(n+2A_m)$. In particular $C(n)=Hn^2$ and $0\le C(n)-J<n^2$. Set $W(n)$ equal to the least possible maximum of $|d-p|$ over injective placements of every record in this box. There is always some placement. The question is how local it can be. [Trip clock and integer proof of its value](one-prime-trip-in-a-shared-lattice.md) · [Exact source and destination ordinals](PALRH/LocalDistance.lean)

## The finite assignment problem

Sort the source groups by prime. If a group $i$ has $a_i$ jobs, its allowed cell ordinals form an interval $[l_i,r_i)$ after sorting eligible cells by physical distance. Both ends are nondecreasing. This stays true after fixed middle addresses are removed. Set $f_0=0$ and $f_{i+1}=\max(f_i,l_i)+a_i$. Place each group in that last block of $a_i$ consecutive ordinals. This fits exactly when every interval of groups satisfies

$$
 l_i+\sum_{i\le u\le j}a_u\le r_j .
$$

Any injection has to land the displayed jobs in $[l_i,r_j)$. Conversely, induction gives $f_{j+1}=\max_{i\le j}(l_i+\sum_{u=i}^ja_u)$. The last reset of the recursion identifies a particular deficient interval whenever the proposed width fails. Bisection on the integer width produces the exact optimum together with a placement and an obstruction one column below it. The decoder recovers the start, direction and tick of each original record. [Formal necessity and sufficiency](PALRH/OrderedTransport.lean) · [Sparse executable placement](../receipt-archives/pal_distance_transport.py)

## The critical travel budget

On the boards $n_j=16^{j+1}$, the following condition is equivalent to RH on paper. There is one $B<\infty$ such that $W(n_j)\le B\sqrt{n_j}(j+1)^2$ for every $j\ge0$. Finite initial boards can be absorbed by increasing $B$. The implication to stock RH has a complete Lean proof. Its hypothesis describes distinct ordinals in bounded physical distance intervals and less than a full layer of unused room. These two requirements force the height to be the minimum height. [Independent statement](checks/local-distance/DistanceChallenge.lean) · [Proof](PALRH/LocalDistance.lean)

**From a placement to an uncalibrated reading.** A cut at $m$ can gain jobs only from the boundary strip of width $W$. It can lose jobs to the opposite strip and to genuine vacancies. Counting the prefix and suffix separately gives

$$
 |P_m-H A_m|\le n^2+2Hn(W+1).
$$

Even a coarse estimate suffices for the slope. For $p>x$, $x\log p\le t_p\le1+(x+1)\log p$, since $1/(x+1)\le\log(1+1/x)\le1/x$. The ordinary Chebyshev bound $\theta(y)\le2y$ gives $H\le11x$ for each nonempty square board. This prices the right side by $O(n^2(j+1)^2)$ under the stated travel budget. [Finite crossing and height bounds](PALRH/LocalDistance.lean)

**Undoing the triangular weight.** On each board allow any integer height $h_j$. Suppose the same $O(n_j^2(j+1)^2)$ discrepancy holds up to $m\le M_j=16^j=n_j/16$. Write $F_m=\sum_{d\le m}(T_d-h_j)$. Finite summation by parts gives the exact identity

$$
 P_m-h_j A_m=(n-m)F_m+\sum_{i=0}^{m-1}F_i .
$$

If all weighted readings have magnitude at most $e$ through $m\le n/4$, induction gives $|F_m|\le2e/n$. Indeed $(n-m)|F_m|\le e+2me/n\le(n-m)2e/n$. The real tick total differs from $x\theta(m)$ by at most $3n$. All omitted small primes cost at most $x\theta(x)\le2n$ and the upward correction on the others costs at most $m+\theta(m)\le3n$. Thus for $s_j=h_j/x$ we have

$$
 |\theta(m)-s_jm|\ll 4^j(j+1)^2\qquad(1\le m\le16^j).
$$

The data do not prescribe a single slope. Read the identical prime prefix at $m=16^j$ on two adjacent boards. Subtraction gives $|s_{j+1}-s_j|\ll 4^{-j}(j+2)^2$, a summable quantity. The limiting slope $c$ is determined by these readings. Summing the tail, then choosing the first $j$ for which $m\le16^j$, yields $\theta(m)=cm+O(\sqrt m(1+\log m)^2)$. [Removing the triangular weight](PALRH/ShapeStrip.lean) · [Passage from integer ticks to prime weights](PALRH/ShapeObservation.lean) · [Limit of the slopes](PALRH/DyadicShape.lean)

**Why the slope becomes one.** Prime powers add $O(\sqrt y)$ to $\theta(y)$. For $\Re s>1$ the Mellin integral of $\psi(1/t)$ on $0<t\le1$ equals $-\zeta'(s)/(s\zeta(s))$ by the Euler product. Subtracting $c/t$ subtracts $c/(s-1)$ from that transform. The proved remainder bound makes the resulting integral holomorphic for $\Re s>1/2$. The first term has residue one at $s=1$, so $c=1$. An off-line zero in the right half of the strip would give a further pole there. Reflection covers the other half. This step derives calibration from the actual zeta pole. [Uncalibrated prime-power transform](PALRH/UncalibratedPrime.lean) · [Analytic continuation and the residue](PALRH/DysonOctave.lean)

## A construction in the other direction

Use every job and fill by decreasing prime distance into cells of decreasing physical distance. This leaves vacancies at the diagonal end. Define

$$
 E_n=1+x+\sup_{0\le u\le n}|\theta(u)-u|.
$$

We claim the maximum travel of this particular assignment is $O(E_n)$ on every sufficiently large fourth power. Let $Q(z)$ be the number of source jobs with $p>z$, and $a=1/\log(1+1/x)=x+O(1)$. For integer $0\le z\le n$, integration of the step function gives

$$
 \sum_{z<p\le n}(n-p)\log p=\int_z^n[\theta(v)-\theta(z)]\,dv
       =(n-z)^2/2+O((n-z)E_n).
$$

Enforcing $p>x$ removes at most $(n-z)\theta(x)$. Rounding ticks and replacing $a$ by $x$ cost $O((n-z)^2)$ in the oriented count, which is $O(x(n-z)E_n)$. It follows that $Q(z)=x(n-z)^2+O(x(n-z)E_n)$. At $z=0$ this gives $H=x+O(xE_n/n)$, with $H\sim x$ by the ordinary prime number theorem. Consequently the same estimate holds with $H$ in place of $x$ in the main term and the error.

Number a job by $q$ starting at the far end. If it travels from $p$ to $d$, then $Q(p)\le q<Q(p-1)$. The number of cells strictly beyond $d$ is $H(n-d)(n-d-1)$. Its jump at $d$ is at most $2H(n-d)$, including the smaller diagonal jump. These inequalities give

$$
 |(n-p)^2-(n-d)^2|\ll (n-p+1)E_n+(n-d+1).
$$

Dividing by $(n-p)+(n-d)\ge1$ proves the travel claim up to the last cell. Under RH, Schoenfeld gives $E_n=O(\sqrt n\log^2 n)$, so this concrete construction supplies the required placement. Unconditionally Dusart gives $E_n=O(n/\log^4 n)$. The stronger unconditional rate below also applies. [Schoenfeld, equation (6.3)](https://electronicsandbooks.com/edt/manual/Magazine/M/Mathematics%20of%20Computation/1960-2002/pdf/1976_v030_n134/2005976.pdf) · [Dusart, Theorem 5.2](https://arxiv.org/pdf/1002.0442)

## What is already paid on every sufficiently large board

Put $V(y)=(\log y)^{3/5}/(\log\log y)^{1/5}$ for large $y$. The unconditional estimate of Johnston and Yang gives $|\theta(y)-y|\le0.027y(\log y)^{1.801}\exp(-0.1853V(y))$ for $y\ge23$. Absorbing the logarithmic factor gives $E_n=O(n\exp(-0.18V(n)))$, since this last envelope eventually increases. The constants in the following two applications are intentionally rounded. [Johnston and Yang, Theorem 1.4, equation (1.8)](https://arxiv.org/pdf/2204.01980)

* **The original target box.** Use the prescribed height $x-2$. On every sufficiently large board, omit just the prime distances in $(\alpha n,\alpha n+w]$, with $\alpha=1/4,1/2$ or $3/4$ and $w=\lceil n\exp(-0.17V(n))\rceil$. Each of the three resulting sets fits at that height with the original middle addresses retained. Indeed, the full excess is at most $O(xnE_n)$ by the preceding $Q(0)$ estimate. The band carries at least $2x(n-\alpha n-w)(w-2E_n)$ units by subtracting the endpoint values of $\theta$ and using $t_p\ge x\log p$. Here $w/E_n\to\infty$. The available cells after fixing the middle jobs are exactly total capacity less those middle jobs. This reduces the earlier $n/\log^3 n$ omitted width to $o(n/\log^a n)$ for every fixed $a$. Its removal still pays for the placement.
* **The missing small-distance contribution.** For the height $x$, add the explicit quantity $xA_{\min(m,x)}$ to $P_m$. For all $m\le x$ this gives $xA_m$ exactly because the sieve leaves no jobs there. For $x\le m\le x\exp(0.10V(n))$ this correction gives $P_m+xA_x-xA_m=o(n^2)$ uniformly. To see the sign and size, write $F_u=\sum_{d\le u}(T_d-x)$. For $u\ge x$, tick rounding yields $F_u=x(\theta(u)-\theta(x)-u)+O(u)$. Uniformly across this range $|\theta(u)-u|=o(x)$, since $V(u)\ge(2^{-3/5}+o(1))V(n)$ and $0.18\cdot2^{-3/5}>0.10$. Also $\theta(x)=x+o(x)$ and $u=o(n)$. Thus $F_u=-n+o(n)$ across the range, while $F_u=-xu$ below $x$. The weighted identity now gives $P_m-xA_m=-n^2+o(n^2)$ there. Finally $xA_x=n^2+O(nx)$. This directly supplies the sign, the amount, and an integer expression that pays it back. The upper end of this paid range is $n^{1/2+o(1)}$ and the required prefixes extend to $n/16$. [Exact small-strip return and tick rounding](PALRH/PrefixReturn.lean)

## Two integer divisions rule out one board area

At $n=16^6$, $x=4096$ and $n^2=281{,}474{,}976{,}710{,}656$. For all $m\le n/16$, ask for $|P_m-hA_m|\le n^2$. Every single $m>0$ requires an integer in $[\lceil(P_m-n^2)/A_m\rceil,\lfloor(P_m+n^2)/A_m\rfloor]$.

| Cut $m$ | $A_m$ | $P_m$ | Forced bound |
|---:|---:|---:|---|
| 5,380 | 90,246,947,190 | 83,672,177,566,201 | $h\le4,046$ |
| 1,021,387 | 16,614,414,106,014 | 67,719,685,941,922,229 | $h\ge4,060$ |

The exact minimax discrepancy on this board is 283,808,050,564,401, achieved only at height 4,060. To check the optimization, at each prime keep its right and left readings, and keep the endpoints. Between jumps $P_m$ is constant and $A_m$ increases. The maximum surplus decreases in $h$ and the maximum deficit increases, so their crossing brackets the optimum. A separate intersection of all allowable integer height intervals is empty at one less unit of error. [Full arithmetic and witnesses](../receipt-archives/check_pal_prime_strip.py) · [Results](../receipt-archives/2026-11-26-pal-local-distance.json)

The small-distance return has a visible effect on this same board. At the prescribed height 4,096 it leaves a maximum absolute discrepancy of 93,468,816,466,096 over all 1,048,576 cuts, less than one third of a board area. Each cut through the square root is paid exactly. On the next board, with 268,435,456 sites, the corrected reading at cut 16,576,186 misses by 24,571,799,698,404,646 units. Three times that exceeds the board area 72,057,594,037,927,936. This rules out extending the observed one-third allowance even to the next size.

In fact every fixed multiple of $n^2$ fails on arbitrarily late boards, even with a fresh choice of height each time. With a common bound $K n^2$, the untilting and tick estimates above would yield $|\theta(m)-s_jm|\ll_K4^j$ for $m\le16^j$. The same overlap argument then yields $\theta(y)=cy+O_K(\sqrt y)$. The ordinary prime number theorem gives $c=1$, whereas Littlewood’s oscillation theorem for $\psi(y)-y$ and the $O(\sqrt y)$ prime-power correction give $\theta(y)-y=\Omega_\pm(\sqrt y\log\log\log y)$. In particular $W(n_j)/\sqrt{n_j}$ is unbounded. Both the measured slope and the full physical placement must eventually allow an increasing factor. Adding the displayed small-distance return costs at most $n^2$ and therefore preserves this obstruction to a fixed constant. The quadratic allowance in $j+1$ remains open. [Littlewood’s result and the prime-power bound, equations (2) and (3)](https://arxiv.org/pdf/1407.1914)
