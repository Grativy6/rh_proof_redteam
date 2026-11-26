# Which prime labels can lower a divisor bound?

Christopher Daniel Pang and Hearthline · 26 November 2026

Suppose a ruler can mark multiples of $2$ and $3$, and of any products or powers built from them. Give its labels any signed real weights you like. For the upper estimate used on the prime board, **four weights already attain the best possible answer in that entire family**. Allowing a third prime changes the result. A rational ruler using only $2,3,5$ beats the first family's exact minimum and crosses the price needed for fifteen copies. The calculation exposes where a reduction in one remainder must reappear.

## How to see the floor

For finitely supported real weights $a_j$ on positive integer labels, take $\sum_j a_j/j=0$. Write
$$
 P_j(k)=\sum_{m\le k/j}(k-jm),\qquad E(k)=\sum_j a_j P_j(k)-(k-1)\quad(k\ge1).
$$
The row is an upper ruler when $E(k)\ge0$ for all $k$. In reciprocal coordinates the height at $1/k$ is $E(k)/k$ and the graph is affine between neighboring knots. Summing the two adjacent trapezoid contributions of each node gives its exact total area,
$$
 \delta=\sum_{k\ge2} w_k E(k),\qquad w_k=\frac1{k(k^2-1)}.
$$
Here $E(1)=0$. The limiting endpoint has measure zero and the balanced sum of ramps is bounded, so the infinite cell sum accounts for the full area. Its equivalent ordinary-log price is $\delta=-\frac12\sum_j a_j\log(j)/j-\frac12$. [Reciprocal ruler, balance and integration](why-the-old-divisor-rows-have-to-move.md)

The second difference at $k\ge2$ is $g(k)=\sum_{j\mid k}a_j$. Indeed each newly encountered multiple changes its ramp slope by one. The condition $E(2)=a_1-1\ge0$ forces $a_1\ge1$.

* If every label above 1 is even, the odd address $4m-1$ can see only label 1. Consequently $E(4m-2)+E(4m)=a_1+2E(4m-1)\ge1$. The pairs are disjoint, and $w_k$ decreases. Their total area is at least $\sum_{m\ge1}w_{4m}$.
* If every label above 1 is divisible by 2 or 3, use $6m-1$ in the same calculation. The resulting lower bound is $\sum_{m\ge1}w_{6m}$. This includes every label made entirely from 2 and 3 at arbitrary exponents.

Both bounds are attained. For the first use $(a_1,a_2,a_4)=(1,-1,-2)$, with all other weights zero. It gives $E(k)=\mathbf1_{4\mid k}$. For the second use $(a_1,a_2,a_3,a_6)=(1,-1,-1,-1)$, giving $E(k)=\mathbf1_{6\mid k}$. To check the full periods, use $2jP_j(k)=k^2-jk+r(j-r)$ with $r=k\bmod j$. Balance cancels the quadratic term. Since each witness satisfies $\sum a_j=-2$, only the constant and periodic terms remain. Evaluating four or six residues proves the assertions. Their sharp excess areas are
$$
 \delta_4=\tfrac34\log 2-\tfrac12=0.0198603854\ldots,\qquad
 \delta_6=\tfrac13\log 2+\tfrac14\log 3-\tfrac12=0.0057021323\ldots .
$$
The divisor restriction matters. Any fixed finite prime basis gives some positive area floor. Take a common multiple $L\ge3$ of its primes and use the disjoint pairs at $Lm-1$.

## How many primes does a fifteen-copy ruler need?

The leading coefficient of the upper prime area is $1/2+\delta$. Returning it to the doubled ruler gives the retained prime product a lower leading coefficient of $4/7-1/2-\delta=1/14-\delta$. Each fixed upper row costs at most $O(n\log n)$ in quadrature and the removed prime terms cost $O(n^{3/2})$. Thus $\delta<1/210$ gives the strict leading margin needed for eventual fifteen-copy payment.

**At least three distinct prime factors are required to cross this particular price.** If label 2 is missing, $E(3)=3a_1-2\ge1$ so $\delta\ge1/24$. If label 3 is missing, $E(2)+E(4)=a_1+2E(3)\ge1$ so $\delta\ge1/60$. A basis with at most two primes which can avoid these tests must be $\{2,3\}$. Its sharp price above is still too large. [Original common clock and its pricing](thirteen-fourteen-and-fifteen-prime-copies.md)

Three suffice. We searched for upper rulers supported on divisors of a fixed period $L$, with zero linear drift. The distributed data contain rational $c_j=a_j/j$ for every nonzero label. At every integer address their doubled excess is
$$
 2E(k)=2+\sum_{j\mid L}c_j(k\bmod j)\bigl(j-(k\bmod j)\bigr).
$$
The replay clears denominators, confirms $\sum c_j=0$ and $\sum jc_j=-2$, checks each residue against both this expression and the direct arithmetic progression, and encloses the logarithmic area. This proves nonnegativity for the infinite row.

| Allowed primes | Period | Nonzero weights | Excess area, rounded upward |
|---|---:|---:|---:|
| 2, 3 | 6 | 4 | 0.005702132354 |
| 2, 3, 5, 7 | 210 | 16 | 0.004754025036 |
| 2, 3, 5 | 2160 | 38 | 0.004549369229 |

The threshold is $1/210=0.0047619047\ldots$. The two larger-period rows are witnesses. The lower bound proves the minimum number of prime factors for crossing that threshold. The optimum price on either enlarged basis remains unknown. [Rational weights](../receipt-archives/periodic_divisor_rows.json) · [Integer-period and directed logarithm checks](../receipt-archives/check_pal_periodic_divisor_rows.py)

## Where the lost unit reappears

The period-six pulse is pointwise minimal even among all finite upper rulers with unrestricted prime support. More precisely, an upper row with $E(k)=0$ at every nonmultiple of six must have $E(k)=1$ at every positive multiple of six.

Fix $C=6m>0$ and let $L$ be a common multiple of 6 and every supported label. Choose another positive multiple of six, $C'$, as follows. At each prime power $p^v\Vert L$ for which $p\mid C+1$, prescribe $C'\equiv C\pmod{p^v}$, and prescribe $C'\equiv0$ at the others. The Chinese remainder theorem provides arbitrarily large such $C'$. It satisfies $\gcd(C'+1,L)=\gcd(C+1,L)$ and $\gcd(C'-1,L)=1$. For the latter assertion the primes in $C+1$ are odd, and $C'-1\equiv-2$ there. Hence $g(C+1)=g(C'+1)$ and $g(C'-1)=a_1$. Writing out their second differences gives the exact transport identity
$$
 E(C)-a_1=2E(C+1)-E(C+2)+E(C'+2)-2E(C'+1)+2E(C'-1)-E(C'-2).
$$
All six off-center entries vanish under our assumption. Also $E(2)=0$ forces $a_1=1$. This proves the claim. More generally, reducing $E(C)$ below $a_1$ by $\eta>0$ forces $E(C+2)+2E(C'+1)+E(C'-2)\ge\eta$. Moving the old positive pulse requires new positive readings somewhere off its original support.

There is a pencil version at $C=6$ with fixed locations. From $g(47)=a_1+a_{47}$ and $g(49)=g(7)+a_{49}$ one gets
$$
 E(6)=a_1+a_{47}-a_{49}+2E(7)-E(8)+E(50)-2E(49)+2E(47)-E(46).
$$
A new slot at the prime 47 and one at the square 49 have opposite signs in this exact accounting. The original sixteen-label upper row reduced $E(6)$ from one to $1/51$ and gave $E(7)$ a positive reading of $2/51$. The exact node identity also holds for both published refits.

## Why the aligned head cannot pay by divisibility alone

If no supported label equals a prime $p\ge3$, then $g(p)=a_1$. One neighbor has excess at least $1/2$, so $\delta\ge w_{p+1}/2$. Suppose all the primes occurring in the row divide $2k$. The least prime $p$ missing from $2k$ is $O(\log(2k))$ because all smaller primes divide $2k$, so $\theta(p-1)\le\log(2k)$ and the elementary lower Chebyshev bound gives the result. Thus these rows have $\delta\gg(\log(2k))^{-3}$. A bound for the leading-area term $\delta n^2$ in isolation cannot pay the desired $O(n^{3/2})$ at $n=k^4$ even with factorial-aligned heads. An argument that keeps the actual arithmetic and its cancellation could use alignment differently. [Definition of the aligned heads](what-a-fourteen-copy-failure-would-force.md#how-few-heads-would-suffice)

Pang's PAL and RPL work supplied the question of which part of an old reading must be carried after a new label arrives. His BLA and CLEF work supplied the comparison of a local improvement with the total price. Hearthline derived the sharp pulse witnesses, transport identities and finite rational refits. The result prices this particular construction. It establishes no general lower bound for unrelated prime estimates. [Construction and computation scope](../receipt-archives/2026-11-26-pal-square-holes.json)

## Unresolved

Find growing divisor supports with enough control of the true ordinary-log price to reach the fourteen-copy clock. The strict margins here pay for fifteen. Both two-prime floors are exact.
