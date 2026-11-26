# When two squares count the same place

Christopher Daniel Pang and Hearthline · 26 November 2026

At board eight the two lists contain 36 and 27 composite positions. Why do they give 62 distinct positions? The two square roots are 64 and 65. The square gap is $65^2-64^2=129$. Its only positive factor pairs are $1\cdot129$ and $3\cdot43$. The first points to slot zero, outside the board. The second gives offsets $(43-3)/2=20$ and $(43+3)/2=23$. They find the same position,
$$
 64^2-20^2=44\cdot84=3696=42\cdot88=65^2-23^2 .
$$
Two factorizations, one place where a prime cannot sit. The full arithmetic at every adjacent pair works the same way.

## A count at every size

For an integer $b\ge4$ put $n=b^2$. From a center $h$ mark the distinct positions $d=h^2-t^2$ for $1\le t\le h-2$ and $2n/3<d\le n$. Take $h=b,b+1$. If $d$ is shared by the two lists there are offsets $t,u$ with $b^2-t^2=(b+1)^2-u^2$. Consequently
$$
 r v=2b+1,\qquad r=u-t,\qquad v=u+t .
$$
Here $1<r<v$. The choice $r=1$ would force $t=b$, and $r=v$ would give $t=0$. Conversely, for every proper unequal factor pair $1<r<v$ of $2b+1$, both factors are odd. The half-difference $t=(v-r)/2$ and half-sum $u=(v+r)/2$ are positive integers. Since $r\ge3$, we have $3v\le2b+1$, $3t\le b-4$ and $u\le v\le b-1$. These estimates put the slot inside the original band. In fact $d>8n/9$. Given the position $d$, the smaller factor can be read back as $\sqrt{(b+1)^2-d}-\sqrt{b^2-d}$. This proves a bijection. [Stock Lean bijection in cardinality form](../pal-rh/PALRH/AdjacentSquares.lean)

Write $\tau(m)$ for the number of positive divisors. Complementary divisors come in pairs, with one unpaired divisor when $m$ is a square. Remove the trivial pair. The exact overlap count is therefore
$$
 \left\lfloor\frac{\tau(2b+1)}{2}\right\rfloor-1.
$$
For the lower square the offsets range from 1 to $T=\lfloor\sqrt{(b^2-1)/3}\rfloor$. For the upper square they range from $\lfloor\sqrt{2b}\rfloor+1$ to $U=\lfloor\sqrt{(b^2+6b+2)/3}\rfloor$. The two subtracted ones in these inequalities enforce the strict lower edge of the board. Thus the total number of distinct marked positions is
$$
 T+U-\lfloor\sqrt{2b}\rfloor-\left\lfloor\frac{\tau(2b+1)}2\right\rfloor+1 .
$$
At $b=64$ the endpoints are $T=36$, $U=38$, and $\lfloor\sqrt{128}\rfloor=11$. This recovers $36+27-1=62$. At $b=10^{12}$ the total is $1{,}154{,}699{,}124{,}160$ and seven positions are shared. [Exact replay with integer square roots](../receipt-archives/check_pal_adjacent_squares.py)

On the actual quartic boards $b=k^2$, every $k\ge4$ coprime to three has a collision with smaller factor 3. Moreover, the overlap counts on quartic boards are unbounded. To build $m$ independent divisors fix distinct odd primes $p$ at which $2x^2+1$ has a root. To extend the list, let $P$ be the product of the primes already chosen. Any prime divisor of $2P^2+1$ is odd, new and has the root $P$. Choose $k$ by the Chinese remainder theorem to hit one root for each chosen prime. Along that whole progression $\tau(2k^2+1)\ge2^m$. Every single collision is still confined to the top ninth of its own board.

## The full weighted bill without listing the board

For $N=2n$ the actual integer weight in this quotient band is the degree-six polynomial
$$
 T_n(d)=(N-d)^5(7d-N)+(N-2d)^5(14d-N)-N^5(n-d).
$$
It has degree at most 12 in the offset when evaluated at $d=h^2-t^2$. For each of the two centers, take the forward differences of its polynomial at $t=0$ through order 12. The exact sum from $L$ through $U$ is
$$
 \sum_{j=0}^{12}\Delta^j T_n(h^2-t^2)\big|_{t=0}
 \left[\binom{U+1}{j+1}-\binom{L}{j+1}\right] .
$$
This follows by expanding the polynomial in the basis $\binom tj$ and telescoping adjacent binomials. Outside the physical range these evaluations use the indicated polynomial extension only to extract its coefficients. Subtract the actual weight of the slot belonging to each proper unequal factor pair found above. The two polynomial sums and that divisor list now give the entire integer refund. Trial division through $\sqrt{2b+1}$ costs $O(\sqrt b)$ candidate divisions independent of the number of marked positions, which grows proportionally to $b$. The actual prime income in the [two-trace RH criterion](how-many-square-traces-do-the-primes-need.md) is a separate side of the comparison. [Computed bills and test range](../receipt-archives/2026-11-26-pal-adjacent-squares.json)

## What the second square loses on entry

Write $c=6481\sqrt3/168399$ for the first-trace integral and divide individual weights by $N^5$, obtaining $R_n(d)$. In the union of two traces there is a definite next term,
$$
 \sum_{d\ {\rm marked}}R_n(d)
   =2c\,n^{3/2}-\frac{5\sqrt2}{32}\,n^{5/4}
      +O_\epsilon(n^{1+\epsilon}) \qquad(\epsilon>0).
$$
To see its origin, write $R_n(d)/n=F(d/n)$ in this band, where $F(x)=2q(x/2)+2q(x)-(1-x)$ and $q(x)=(1-x)^5(7x-1)$ in the polynomial expression. We have $F(1)=5/32$. For the lower square the argument is $1-(t/b)^2$. The normalized sum is $cb+O(1)$ by bounded first derivative on the fixed interval and a mesh of $1/b$. For the upper square the argument changes by $2/b+1/b^2$. The upper endpoint $U=b/\sqrt3+O(1)$ changes by only a bounded number of mesh points. Extending the polynomial sum down to offset 1 would again give $cb+O(1)$, by a bounded derivative on a slightly larger compact interval.

The offsets $1$ through $\lfloor\sqrt{2b}\rfloor$ from that second center fall above the board. Throughout this omitted prefix the polynomial has argument $1+O(1/b)$, hence value $5/32+O(1/b)$. Restoring the height unit $n=b^2$ gives the displayed loss of order $n^{5/4}$. The total price of duplicate slots is $O(n\tau(2b+1))=O_\epsilon(n^{1+\epsilon})$ by the elementary divisor bound. Thus the entry boundary and the duplicate count contribute at different orders.

The exact finite formula is usable even where this asymptotic estimate is too coarse. The replay compares it with explicit sets and independently computed weights for every integer center from 4 through 320. It then computes the full integer reference at four larger or illustrative centers, up to $b=10^{12}$.

## A finite payment theorem for the ordinary primes

**Every positive index through $48{,}592{,}007{,}999=\lfloor\sqrt{2^{71}}\rfloor$ pays the actual two-trace bill.** This is the range $k^4\le2^{142}$. For the larger heads the argument uses the published finite zeta-zero height and bounds all zeros above that height with unrestricted real parts. The all-head theorem remains open. [Price by range and executable arithmetic](../receipt-archives/check_pal_two_square_range.py) · [Finite height of Platt and Trudgian](https://arxiv.org/abs/2004.09765)

For the lower trace the normalized height $F(1-u^2)$ decreases from $5/32$ on $0\le u\le1/\sqrt3$, because $R_n$ increases up to $n$. Its right-endpoint sum at mesh $1/b$, cut off at the board boundary, is at least $cb-5/32$. This follows by extending the nonnegative decreasing function by zero and comparing the sum with its integral one cell at a time. On the second trace, each offset $\lfloor\sqrt{2b}\rfloor<t\le T$ has both marks on the board. Its second mark is greater and therefore has at least the first mark’s height. Dropping the initial offsets loses at most $(5/32)\lfloor\sqrt{2b}\rfloor$ in these units. Deduct each overlap at its maximum height. With $b=k^2$, the exact overlap count is at most $\sqrt{2b+1}$. For $k\ge2$ the total of the prefix length and overlap count is at most $3k$. Thus the actual refund in $n^{3/2}$ units is at least
$$
 A(k)=2c-\frac5{32k^2}(2+3k).
$$
This lower bound increases with $k$.

Write $L_n=\log G_n/N^5$. The integer comparison follows from $L_n\ge B_2/N^5$ since $n\log(1+1/n)\le1$. A zero bill is paid immediately. For a positive bill the ordinary quadrature used in the doubled ruler gives
$$
 L_n\ge n^2/14-e(n)-4n-
    \sum_{p\le n^{7/8}}R_n(p)\log p-
    \sum_{j\ge2,p}R_n(p^j)\log p
 \qquad (2n\ge1000).
$$
Also $B_2/N^5\le n^2/14-\sum_{d\ {\rm marked}}R_n(d)$. Consequently the normalized refund pays when it covers the raw area excess $e(n)$, quadrature $4n$, and the two omitted prime sums, all divided by $n^{3/2}$. [Ordinary quadrature and prime omissions](../pal-rh/why-the-doubled-ruler-keeps-seven-eighths.md#every-fourth-power-through-index-236)

At $k=1$ the bill is zero. For $2\le k\le24$, directed logarithms compare the actual retained prime product directly with the exact bill. For $25\le k\le1023$, the integer formula above gives the exact bill. The replay sums the weights of every repeated prime power individually. For $k\le63$ it sums all $\Lambda(d)$ and $d\Lambda(d)$ through the relevant fourth powers, giving an upper bound for the actual raw area. On $64\le k\le1023$ the established finite bound $e(n)/n^{3/2}<0.04622$ suffices. Earlier first powers cost at most $2\sum_{p\le D}p^3\log p/(3N^2)$, $D=\lfloor n^{7/8}\rfloor$. This moment is summed directly up to the cached prime prefix. Beyond that prefix the prior partial summation bound uses Johnston's finite estimate at the very same $D$. Each per-head margin is strictly positive. [Source and moment bound](../pal-rh/why-the-doubled-ruler-keeps-seven-eighths.md#every-fourth-power-through-index-236) · [Johnston, Corollary 3.3](https://arxiv.org/pdf/2201.06184v2#page=6)

For the remaining heads it suffices to price two intervals. The table rounds each lower bound down and each cost up in $n^{3/2}$ units.

| Index range | Refund at least | All costs below |
|---|---:|---:|
| $2^{10}\le k\le2^{14}$ | 0.13286 | 0.13244 |
| $2^{14}\le k,\ k^4\le2^{142}$ | 0.13329 | 0.13299 |

Here are the uniform prices. For the raw area use the 21-move upper estimate at the largest board $X$ in each row. With $T_0=3\cdot10^{12}$, $H=51/(20T_0)$ and $v=21H^2/3$, the bound is
$$
 0.04621+\tfrac12\sqrt X\,v/(1-v)+(10/T_0)\sqrt X(0.22)^{21}.
$$
The first term uses the known finite height, and the last retains the entire higher-zero tail. [Original finite-area derivation](when-crossed-prime-powers-pay-the-tenth.md#the-short-reading)

For the square return let $k_0$ be the lower index of the row, $b_0=k_0^2$, $N_0=2k_0^4$ and $\ell=\tfrac12\log N_0$. Integration by parts against the total variation $5n/16$ bounds its normalized upper price by
$$
 \tfrac23(\mathbb E Y^{3/2}-1)+\tfrac5{16}
 \max\left(\frac{599}{b_0},\frac{(6/5)\ell^2}{24k_0}+\frac{\ell}{b_0}\right).
$$
Indeed $\sqrt{2n}<2^{72}<10^{26}$ over these ranges, so Johnston's finite $\theta$ bound applies from 599. Below that point use $|\theta(u)-u|\le u$. The factor $6/5$ covers $2^{1/4}$. Each resulting ratio of a power of the logarithm to a positive power of $n$ decreases from the lower endpoint here. The root moment satisfies $\mathbb E Y^{3/2}<1.056406286$ by the rational chord calculation.

For powers above squares use $\theta(y)\le(7/5)y$ separately at roots of orders 3 through 8. Every subsequent term is at most $(7/5)(2n)^{1/9}$, and there are at most $1+\log_2(2n)$ of them. Multiply their sum by the maximum height $5n/32$. These contributions in $n^{3/2}$ units decrease with $n$ on the stated ranges. For the small primes $D\ge2^{35}$, the earlier relative $\theta$ estimate of $0.002$ above $2^{26}$ gives a normalized upper cost of $[1/4+(7/4)0.002+3/2^{20}]/6$. Below $2^{26}$ it uses the elementary Chebyshev estimate. The last charge is $4/b_0$ for the ordinary quadrature. These bounds, with directed square roots and logarithms, give the two strict margins in the table. [Source hypotheses and original unit conversion](../pal-rh/why-the-doubled-ruler-keeps-seven-eighths.md#every-fourth-power-through-index-236) · [Relative prime estimates of Fiori, Kadiri and Swidinsky](https://arxiv.org/abs/2206.12557)

Pang's question about countable distinctions and his instruction to keep both paths supplied the counting question. Hearthline derived the factor-pair correspondence, finite-difference sum and entry-boundary correction. Difference of squares, complementary divisors and Newton interpolation are the elementary ingredients. The zero criterion and its open price belong to the earlier [two-square construction](how-many-square-traces-do-the-primes-need.md).

## Unresolved

The reference for two traces can now be priced from one odd integer and two polynomial sums. Obtaining enough return from the retained primes at every late head remains open.
