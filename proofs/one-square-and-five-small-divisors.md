# One square and five small divisors

Christopher Daniel Pang and Hearthline · 26 November 2026

On board eight, keep the square at $64^2=4096$. The [previous two-square calculation](when-two-squares-count-the-same-place.md) needed a second center to cover the bill. Pang suggested the number 17. Look in the opposite direction from the same square. The seven positions
$$
 4097,\quad4352,\quad4420,\quad5185,\quad5321,\quad6596,\quad6800
$$
are $4096+t^2$ for $t=1,16,18,33,35,50,52$. Every one has the proper divisor 17. Together with the original 36 inward marks, these seven change the normalized payment margin from $-0.004195309\ldots$ to $+0.003324162\ldots$. The prime product has identical weights on both sides of that experiment. At the smaller square $4^2$, the first outward position is 17 itself. The proper-divisor rule keeps it in the prime product. [Directed integer calculation](../receipt-archives/check_pal_one_square.py)

**A single square now gives an integer comparison equivalent on paper to ordinary RH.** At each sufficiently large board it suffices to find one square whose root is within 62 of the original root and whose two directions cover the bill. All inward marks factor. Outward marks need a proper divisor from $2,3,5,7,17$. The fixed choice of center below also works in the reverse implication under RH. Eventual payment of the actual prime bill is open. [Independent mathematical statement](../pal-rh/checks/one-square/CenterChallenge.lean)

## One square on each board

Write $n=k^4$, $B=k^2$ and $N=2n$. Choose $B\le b\le B+62$. Mark two disjoint sets:
$$
 \begin{aligned}
 H_-&=\{\,b^2-t^2:\ 1\le t\le b-2,\quad 2n<5(b^2-t^2),\quad b^2-t^2\le n\,\},\\
 H_+&=\{\,b^2+t^2:\ 1\le t\le B,\quad n<b^2+t^2\le2n,\quad
       \exists p\in\{2,3,5,7,17\},\ p\mid b^2+t^2,\ p<b^2+t^2\,\}.
 \end{aligned}
$$
On the inward side the two factors are $b-t$ and $b+t$. On the outward side each admitted label has a proper divisor. Count each position once even when two primes certify it. Using the [doubled ruler and its unchanged prime income](how-many-square-traces-do-the-primes-need.md#what-gets-charged), let
$$
 C=\sum_{d\in H_-\cup H_+}T_n(d),\qquad
 W=\sum_{r=0}^{N-1}r^6,\qquad B_{\rm bill}=(W-16n^7-C)_+ .
$$
The integer test is $(n+1)^{nB_{\rm bill}}\le n^{nB_{\rm bill}}G_n$. At $k\ge8$ there are at most $3k^2$ marks, and each weighs at most $7N^6$. The total normalized credit is at most $42k^6$. Removing this much from the reference gives the one-sided prime-area bound $e(k^4)\le144 k^6$ at every paying head. The quartic interpolation and Mellin argument give ordinary RH from eventual payment. This direction allows a different admissible center on every board. [Shared price inequality](../pal-rh/PALRH/SquareReference.lean) · [One-center proof](../pal-rh/PALRH/OneSquare.lean)

For the price in the other direction take the next multiple of 21 whose quotient by 21 is coprime to 85. Of any three consecutive quotients at most one is divisible by 5 and at most one by 17. Thus the center carries 3 and 7, is invertible modulo 5 and 17, and moves at most $20+2\cdot21=62$ places. A small board can distinguish the fixed choice from the freedom to leave the center where it stands. At $k=8$ the moved center is 84 and the five-divisor test there misses. The allowed unshifted center 64 pays. [Examples, all unshifted payments from 2 through 27, and fixed-center misses](../receipt-archives/2026-11-26-pal-one-square.json)

## The price of looking both ways

For $q(z)=(1-z)^5(7z-1)$ on $[0,1]$, the inward height divided by $n$ at the unshifted mark $d/n=x=1-u^2$ is
$$
 f_m(u)=2\sum_{j=1}^m q(jx/2)-u^2,\qquad m=\lfloor2/x\rfloor .
$$
The three integration cells have $m=2,3,4$ and respective endpoints $\sqrt{1-2/m}$ and $\sqrt{1-2/(m+1)}$. The possible end term at a boundary has zero height. Integrating the three polynomials gives
$$
 c_-=-\frac{26496629\sqrt{15}}{15640625}+
       \frac{640\sqrt3}{9009}+\frac{4608\sqrt2}{1001}
       =0.0720479226\ldots .
$$
On the outward side the height is $(1-u^2)^5(5+7u^2)/32$, whose integral from zero to one is $c_+=64/1001$. These integrals give prices in units of $n^{3/2}$ because the offset mesh is $1/\sqrt n$ and the height unit is $n$.

On the chosen center the outward witnesses repeat with period $3570$. For 2, the offset must have the center’s parity. For 3 and 7 it must be zero modulo the corresponding prime. For 5 the two classes are $\pm2b$, and for 17 they are $\pm4b$, since $2^2\equiv-1\pmod5$ and $4^2\equiv-1\pmod{17}$. The Chinese remainder theorem gives the fraction of covered offsets:
$$
 1-\frac12\frac23\frac35\frac67\frac{15}{17}=\frac{101}{119}.
$$
The fraction before adding 17 is $29/35$. The added fraction is $12/595$, worth exactly $768/595595$ in the limiting normalized refund. Each residue class has the same limiting Riemann integral after the common period rescaling. The bounded center shift changes $b^2/n$ by $O(k^{-2})$, and the new lower inward cutoff in $t/B$ tends to zero. All three inner kernels paste continuously. Thus for the chosen center the total normalized refund tends to
$$
 c_-+\frac{101}{119}c_+=0.1263129853\ldots .
$$

Under RH, the earlier explicit formula gives $e(n)/n^{3/2}\le0.04621$. The shared small-prime and repeat deductions have limiting coefficient $h=1/24+(2/3)(\mathbb E Y^{3/2}-1)$, with the existing rational chord calculation giving $\mathbb E Y^{3/2}<1.056406286$. Ordinary quadrature and rounding are $o(n^{3/2})$. The resulting sufficient cost is below $0.125480858$. Before 17 the allowance on these same centers is $0.1250235185\ldots$. With 17 it crosses the stated sufficient cost and the fixed choice pays eventually under RH. This comparison of limiting allowances leaves open whether the four-divisor version also pays at its true cost. The board-eight sign switch above is an actual payment difference. [Prime omissions, phase bound and moment calculation](../pal-rh/why-the-doubled-ruler-keeps-seven-eighths.md#which-primes-may-be-removed)

There are unconditionally paying runs near every sufficiently large scale. In the [Gaussian localization argument](where-fourteen-pays-again.md), choose the initial tolerance $1/100$. The selected integer side of the fourth-power interval has $e(n)/n^{3/2}\le1/80+o(1)$ since $H\sup|s(v)-s(m)|=o(m^{3/2})$ there and $n/m\to1$. This fits inside the available margin. Thus the earlier guarantee of a run of $(\log K)^A$ consecutive heads in $[K,2K(\log(2K))^{1/4}]$ for each fixed $A>0$ also holds for the one-center clock. Universal eventual payment remains a separate obligation.

## A uniform finite check on the actual primes

For the prescribed moved centers every index $2^{17}\le k\le2^{30}$ pays. Put $b=B+a$ with $0\le a\le62$. For inward offsets with $\sqrt{b^2-n}<t<B\sqrt{3/5}$ the shifted return is at least the unshifted one, since it increases up to $n$. The original inward height decreases with the offset. Right-endpoint quadrature costs at most one maximum height, and the discarded prefix has length at most $12k$ at these indices. Each such height is at most $5n/32$.

For outward positions the return extended by zero beyond $2n$ has Lipschitz constant at most one on $[n,\infty)$. This follows from the expectation of a positive ramp in the original construction. The displacement of a mark in $d/n$ is at most $124/B+3844/B^2$. The difference between the admitted offset count and density times the full count in any prefix is at most one period. Partial summation against the decreasing outward height costs at most $3570$ maximum heights, and one more covers unit quadrature. Combining these bounds lowers the limiting normalized refund by at most
$$
 \frac{5(3572+12k)}{32k^2}+\frac{124}{k^2}+\frac{3844}{k^4}.
$$
The remaining allowance is at least $0.1262986404$ on the claimed interval. The previous 21-move finite spectral bound, cumulative upper bounds for the omitted primes and powers, and ordinary quadrature give total cost at most $0.1262450274$ using the lower index $2^{17}$ and largest board $2^{120}$. The finite-height input covers ordinates up to $3\cdot10^{12}$ and the high-ordinate estimate includes every later zero with unrestricted real part. [Original uniform price derivation](when-two-squares-count-the-same-place.md#a-finite-payment-theorem-for-the-ordinary-primes) · [Price replay at these endpoints](../receipt-archives/check_pal_one_square.py) · [Finite height](https://arxiv.org/abs/2004.09765)

## Seventeen shared places

The first two-neighbor board with exactly 17 shared positions occurs at $k=1933$. Its gap is $2k^2+1=7472979=3^8\cdot17\cdot67$. That gives 36 divisors, hence 18 unequal pairs. The trivial pair goes to zero. The other 17 give the shared positions by the [adjacent-square bijection](when-two-squares-count-the-same-place.md). Trial division through the square root checks every smaller index. In this search 17 overlaps were requested. The appearance of 17 in the first such factorization is a further property of the result.

There is a useful reverse. Put $rv=2b+1$ with $1<r<v$ and offsets $t=(v-r)/2$, $u=(v+r)/2$. The inward collision $d=b^2-t^2=(b+1)^2-u^2$ has a reflected outward collision $e=b^2+u^2=(b+1)^2+t^2$. Expanding gives
$$
 d=\frac{r^2-1}{2}\frac{v^2-1}{2},\qquad
 e=\frac{r^2+1}{2}\frac{v^2+1}{2}.
$$
Both are composite. At $k=5$ the square gap is $51=3\cdot17$, the inner slot is $576=4\cdot144$, and the outer one is $725=5\cdot145$. At $k=12$ the gap is $289=17^2$. Its equal factors give offset zero, which earns no shared slot.

Christopher Daniel Pang supplied the prime 17, the reversal question and the move-the-frame rule from PAL and RPL. Hearthline derived the proper-divisor test, bounded choice of center, two-sided prices and independent deductions. BLA supplied the distinction between a reduction in the reference and a change to genuine prime income. The analytic inputs belong to the earlier linked derivations and their credited sources. [Source files, fixed statement and exact scope](../receipt-archives/2026-11-26-pal-one-square.json)

## Unresolved

Establish payment from at least one permitted center on every sufficiently late head. The five divisors and bounded motion earn the reference. The universal comparison with the retained prime income is still the missing mathematical step.
