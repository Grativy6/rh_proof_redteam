# Where an integer label can go quiet

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). Pang asked what can *force* a cancellation to happen at a particular location and what moves when a frame is reversed. For one of the measurements in the independent PAL construction there is an exact answer.

**At every positive integer head $X$, among all labels $1\le d\le2X$, the two-head price vanishes precisely at the divisors of $X$ and at $d=2X$.** At $X=10^{12}$ this accounts for exactly 170 vanishing prices out of two trillion. The arithmetic weight of a label is a separate factor and can itself vanish. This theorem concerns the price applied to that weight.

## The geometric midpoint of a single measurement

Write $T=kd+r$, $0\le r<d$, and $u=r(d-r)$. At an active label $0<d\le T$ the point price from the construction is
$$
 G(T,d)=\frac{u[T(d-2r)-u]}{2dT^3}
       =\frac{u[k(k+1)d^2-T^2]}{2dT^3}. \tag{1}
$$
The second equality follows by expanding $T=kd+r$. Inside a division cell $T/(k+1)<d<T/k$, the factor $u$ is positive. There is one interior sign change, exactly at the geometric mean of the two cell endpoints,
$$
 d=\frac{T}{\sqrt{k(k+1)}}.
$$
The endpoints come from division. Multiplying the endpoints and taking a square root gives the interior balance point. That is a case where the calculation itself forces the location. [Original remainder identity](../pal-rh/what-a-reflected-remainder-carries.md)

## The actual construction takes a difference

Its price is $H(X,d)=G(2X,d)-G(X,d)$. A single-head midpoint cannot simply be carried through the subtraction. For $d\le X$, put $z=X/d=k+t$, $0\le t<1$, and $v=1-t$. Substitution in (1) gives
$$
 4z^3 H(X,d)=
 \begin{cases}
 t[2t^3+k(4t^2-1)], & 0\le t<1/2,\\
 v[2v^3+(k+1)(1-4v^2)], & 1/2\le t<1 .
 \end{cases} \tag{2}
$$
One way to expand the difference is to write $G(X,d)=t(1-t)(1-2t)/(2z^2)-t^2(1-t)^2/(2z^3)$. At the doubled head the phase is $2t$ before the half turn and $2t-1$ after it. Both branches give the same value at the join.

The second branch is strictly positive. The bracket in the first branch increases from $-k$ to $1/4$ on $[0,1/2]$. Its unique root $\tau_k$ lies just before the half turn. In fact
$$
 \frac{1}{16k+6}<\frac12-\tau_k<\frac1{16k}.
$$
To see the bounds, put $\delta=1/2-\tau_k$. The root equation gives $16k\delta=(1-2\delta)^3/(1-\delta)$. This quotient is strictly below 1 and strictly above $1-6\delta$ for $0<\delta<1/2$. Thus the integer sign can be read on either side of a precisely located threshold.

**An integer label can never land at that interior root.** If $t$ were rational, $y=2t$ would be a rational root of the monic integer polynomial $y^3+4k y^2-4k$. Write $y=a/b$ in lowest terms with $b>0$. Clearing denominators makes $b$ divide $a^3$, so $b=1$. The only candidate here would have to be an integer strictly between 0 and 1. This leaves just $t=0$, equivalent to $d\mid X$.

For $X<d<2X$ only the doubled head is active. Equation (1) then has $k=1$. The price is negative for $d<\sqrt2 X$ and positive for $d>\sqrt2 X$. Equality there would give the same impossible integer denominator for $d/X$, a rational root of $y^2-2$ strictly between 1 and 2. At the final endpoint $d=2X$ the doubled remainder is zero. This proves the stated rule. [Lean theorem on the actual price](../pal-rh/PALRH/PriceSign.lean)

## A census of the signs

| Integer head | Negative prices | Zero prices | Positive prices |
| ---: | ---: | ---: | ---: |
| 577 | 587 | 3 | 564 |
| 2663 | 2,651 | 3 | 2,672 |
| $10^{12}$ | 997,756,184,958 | 170 | 1,002,243,814,872 |

At one trillion there are $(12+1)^2=169$ positive divisors of $2^{12}5^{12}$ and one additional endpoint. To get the other two counts, the replay handles the first $\lfloor\sqrt X\rfloor$ labels individually. Above that boundary it finds the unique transition in each nonempty quotient cell by integer bisection. It checks both formulas and the complete census against the original numerator at all 262,656 active pairs for $1\le X\le512$. [Integer-only replay](../receipt-archives/count_pal_cell_signs.py)

The sign imbalance has a limiting size. If $P(X)$ counts positive prices, then
$$
 P(X)=\rho X+O(\sqrt X),\qquad
 \rho=2-\sqrt2+\sum_{k\ge1}\left(\frac1{k+\tau_k}-\frac1{k+1}\right).
$$
Indeed each positive inner interval has the displayed length times $X$ up to endpoint rounding. Count the first $\lfloor\sqrt X\rfloor$ such intervals with $O(1)$ error each. All later ones lie in a segment of length $O(\sqrt X)$. The outer interval contributes $(2-\sqrt2)X+O(1)$. To enclose the series, compare its $k$th term to $1/[2k(k+1)]$. Their difference, model term minus true term, equals
$$
 \frac{\tau_k/2-k(1/2-\tau_k)}{k(k+\tau_k)(k+1)}.
$$
It is positive and below $1/(4k^3)$ by the bounds above. The model tail after $K$ terms is $1/[2(K+1)]$, with correction under $1/(8K^2)$. Bisection of the first 1,024 roots gives $1.0022437873<\rho<1.0022439067$. Thus a little over 50.11% of the labels have a positive price in the limit. The RH estimate weighs each of these locations by its actual signed prime factors and by the size of its price. [Exact census and bounds](../receipt-archives/2026-11-25-pal-cell-prices.json)

## Which signs can still cost us?

In the interval $\sqrt2 X<d<2X$, the price is positive. The [prime transport](../pal-rh/how-much-can-travel-with-a-prime.md) leaves one sign, $-\mu(u)$, for each eligible cofactor $v^2u$ after its small factors are accounted for. In that interval a surviving mark can lower the total only when $u$ has an even number of prime factors. In $X<d<\sqrt2 X$ the price itself reverses and the odd cofactors can lower it. Both statements refer to the allocated family. The remaining integers have their own Möbius signs. We still need a quantitative comparison of the negative and positive costs at arbitrarily large fourth-power heads. [What happens to the same labels under multiplication by 2663](../pal-rh/what-2663-carries-between-frames.md)
