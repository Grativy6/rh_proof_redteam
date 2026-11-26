# One prime trip in a shared lattice

Christopher Daniel Pang and Hearthline · 26 November 2026

For $n=k^4$, $x=k^2$, retain the distances $2\le p\le n$ with $\gcd(p,x!)=1$. These are precisely the primes $p>x$. For each such $p$, the ordinary clock has length
$$
 t_x(p)=\#\{0\le t<nx:(x+1)^t<p x^t\}.
$$
The list of ticks is an initial segment of the nonnegative integers. Its length is the least $t$ with $(x+1)^t\ge p x^t$, since $(x+1)^x\ge2x^x$ and the stated search range suffices. Put $U(n)=\sum_{p>x}(n-p)t_x(p)$, summing only $p\le n$. There are $2U(n)$ triples consisting of an ordered trip and a tick index. The minimum height of an $n$-by-$n$ lattice holding all these unit records is $L_n=\lceil 2U(n)/n^2\rceil$. This counts one unit record per tick. The product of all possible dial settings in the earlier construction is linked by a price inequality.

## The formal implication

For each retained prime, $\log p\le t_x(p)\log(1+1/x)\le t_x(p)/x$. If $2U(n)\le n^2 x$, then $2\sum_{p>x}(n-p)\log p\le n^2$. The primes through $x$ add at most $2n\theta(x)\le2(\log4)nx$ to the twice-weighted sum. Restoring prime powers costs another $O(nx)$. This supplies an upper bound at the fourth powers on $I_\psi(n)-n^2/2$ of order $n^{3/2}$. Convex interpolation and the one-sided logarithmic primitive give the stock RH proposition. The formal challenge uses the stronger height bound $2U(n)\le n^2(x-2)$ for all sufficiently large fourth powers. Its only mathematical premise is an eventual comparison of two counts of units. [Exact tick price and Lean transfer](PALRH/TickBoard.lean) · [Independently stated comparison](checks/tick-layers/TickChallenge.lean) · [One-sided primitive proof](how-one-sided-prime-area-reaches-rh.md)

## The exact number of whole layers

Write $I^>(n)=\sum_{p>x}(n-p)\log p$ with the same size restriction and $Q(n)=I_\psi(n)-n^2/2$. The ordinary prime number theorem and the earlier square calculation give, unconditionally,
$$
 I^>(n)=n^2/2+Q(n)-(5/3+o(1))n^{3/2}.
$$
The $2/3$ comes from the integrated contribution of repeated powers, and 1 comes from removing prime distances through $\sqrt n$. Also $I^>(n)/n^2\to1/2$. [Prime-square and small-distance terms](when-two-prime-directions-meet.md#why-the-integer-cut-contains-five-eighths)

Allow a fixed reading shift $\alpha\ge0$, taking multiplicative steps of $1+1/(x+\alpha)$. Let $U_\alpha$ be the analogous forward count. Since each rounded positive tick length differs from the exact logarithmic ratio by less than one, its total rounding contribution is at most $\sum_{p>x}(n-p)=O(n^2/\log n)$. The Taylor expansion at zero gives $1/\log(1+1/z)=z+1/2+O(1/z)$. Consequently
$$
 \frac{2U_\alpha(n)}{n^2}
 = x-\left(\frac{17}{6}-\alpha\right)+\frac{2Q(n)}{n^{3/2}}+o(1).
$$
The identity of remainders holds even if $Q(n)/n^{3/2}$ is unbounded. The factor multiplying the bounded clock shift only needs $I^>(n)/n^2\to1/2$.

Under RH the integrated explicit formula gives $\limsup|Q(n)|/n^{3/2}\le T$, with $T=2+\gamma_E-\log(4\pi)<0.05$. For the ordinary clock this puts the eventual reading strictly between $x-3$ and $x-2$. Its rounded-up height is therefore **exactly $x-2$**. Conversely eventual fit at $x-2$ implies RH by the one-sided theorem. Requiring eventual fit at $x-3$ would imply RH as well, and under RH it fails at every sufficiently late head. Thus there are unconditionally infinitely many fourth powers where a third whole layer cannot be removed. This argument gives no general threshold after which the two-layer fit holds. [Explicit formula](https://arxiv.org/pdf/2201.06184) · [Enclosure of the trace constant](what-the-least-cut-measures.md#a-power-saving-has-a-precise-meaning)

The same construction can retain the fluctuation on the other side of rounding. Set $\alpha=5/6$, so that the tick multiplier is $(6x+11)/(6x+5)$ and the central height is the integer $x-2$. The previously derived quartic limsup and liminf for $2Q(n)/n^{3/2}$ are at least $A$ and at most $-A$, respectively, where $A>0.0099$ is supplied by one independently enclosed simple critical zero. Infinitely many shifted boards thus need at least $x-1$ layers and infinitely many need at most $x-2$. Under RH these are the only two possible eventual heights, and both occur infinitely often. Conversely, eventual confinement to those two heights implies RH, because the shifted multiplier is smaller and the ordinary clock needs no more ticks. These converse and recurrence statements are paper results. [Quartic recurrence proof and zero enclosure](when-two-prime-directions-meet.md#both-signs-on-the-actual-fourth-powers)

## A recoverable position for each middle-prime record

Let $b$ be the binary length of $n$, and reserve two whole layers so the available height is $h=x-2$. For $2b+2\le x$ and primes
$$
 x<p\le \frac{n}{4(b+1)}
$$
there is an explicit placement of **every** ordinary-clock record on actual cells. It applies to all sufficiently large fourth powers and allows the other prime labels to use the remaining cells. Since $(1+1/x)^x\ge2$ and $p\le2^b$, the tick length is at most $bx\le(b+1)h$.

Write a forward source as $(p,i,t)$ with $0\le i<n-p$ and $0\le t<t_x(p)$. Put $a=\lceil n/2\rceil$, $t=uh+s$ and $i=va+i'$ by division. Here $v$ is zero or one. Send it to the pair of sites $i',i'+d$ at layer $s$, with
$$
 d=(2u+v+1)p .
$$
For the reverse direction exchange the destination endpoints. The multiplier is at most $2(b+1)$, hence $d\le n/2$, $i'<a$ and $i'+d<n$. Every used $d$ has a unique prime factor larger than $x$ because $d\le n$ and two such factors already multiply past $n$. That factor recovers $p$. Dividing $d$ by $p$ and subtracting one recovers $2u+v$. Its quotient and remainder modulo 2 recover $u,v$. Both original indices then follow from the stored coordinates. This proves disjointness while naming the physical return route. [Lean placement for the reduced-height lattice](PALRH/TickPacking.lean)

For a fixed size with enough total capacity, the remaining jobs can be placed by rank in the actual unoccupied cells. Order destination blocks by distance, direction, starting site and layer. Each reserved block is a rectangle, so its occupied size and the rank of each free cell follow by integer division. At $n=4096$, $h=62$, the 67, 71 and 73 jobs occupy 6,634,268 cells. The outer jobs use 1,019,850,284 further cells, leaving 13,702,840 unused. All 43,076 records at $n=81$, $h=7$ were also passed through the encoder and recovered individually. At 4,096 the replay checks the interval sizes, boundaries and selected inverse calls without allocating a billion-entry array. [Actual retained and free-cell codec](../receipt-archives/pal_tick_codec.py) · [Finite replay](../receipt-archives/2026-11-26-pal-tick-layers.json)

## Moving an unpaid band without spending a cell twice

There is an unconditional combined packing on all sufficiently late heads if one narrow range of distances may be withheld. Set $w=\lceil12n/b^3\rceil$ and omit the primes in $(n/2,n/2+w]$. Keep the entire middle-prime placement just constructed.

To see why the other jobs fit beside it, the existing unconditional bound gives $2I^>(n)\le n^2+(0.85+o(1))n^2/\log^3 n$. Meanwhile $w\sim12(\log2)^3n/\log^3 n$. Dusart’s bound $|\theta(y)-y|\le0.78y/\log^3 y$ at both ends of the withheld interval gives a removed log cost, in both directions, of at least
$$
 (n-2w)\bigl[\theta(n/2+w)-\theta(n/2)\bigr]
 \ge \left(12(\log2)^3-0.78+o(1)\right)\frac{n^2}{\log^3 n}.
$$
The coefficient exceeds 3.2. Multiplication by the reciprocal tick length $x+O(1)$ preserves a surplus of order $xn^2/\log^3 n$, dominating both integer tick rounding and the cost of setting aside two entire layers, which are $O(n^2)$. All kept jobs therefore fit at height $x-2$ eventually. The reserved middle jobs use actual disjoint cells; the remaining jobs use *only* the complement. This moves the omitted group to a measurable band of outer distances. Restoring it at all sufficiently large sizes is the unresolved step. [Source of the unconditional bound](the-factorial-frame-for-prime-distances.md#funding-the-upper-distances-at-every-size) · [Dusart, Theorem 5.2](https://arxiv.org/pdf/1002.0442)

## Three individually funded views and their exact disagreement

The omitted band can be placed at any of $n/4,n/2,3n/4$, using the width $w$ above. For a fixed location $\alpha n$ in this list the leading lower coefficient for removed twice-weighted area is $2(1-\alpha)\{12(\log2)^3-1.56\alpha\}$, by the same two-endpoint calculation. Even the smallest, at $3n/4$, exceeds 1.4, which pays the 0.85 error. The three bands are disjoint eventually. Each view excluding one band thus has an injection into the $x-2$ layer box, for either fixed clock. The middle placements can be identical in all views. For the shifted clock the length is at most $(x+1)b$ and hence at most $(b+1)(x-2)$ once $x\ge3b+2$. The same rectangular placement then applies.

There is an exact finite relation between local and shared space. Let $J$ records compete for $S$ slots. Suppose three pairwise disjoint omitted sets each yield a locally injective placement of the remaining records. A record disagrees if two of the views that contain it assign it different physical slots. Among all choices of locally injective placements, the minimum number of disagreeing records is
$$
 d=\max(0,J-S).
$$
For the lower bound, any pair of records occurs together in at least one view. Consistent records therefore give a joint injection into the $S$ slots. For the upper bound, if $J\le S$ simply restrict a single injection. Otherwise every omitted set has at least $d$ members. Choose $d$ records in the first omitted set, and put the other $S$ records in a fixed bijection with the slots. The first view uses these common assignments. The second view puts the chosen $d$ records in slots freed by the second omission. The third view places them in slots freed by the third omission. The two sets of freed slots are disjoint, so exactly those $d$ records change position. Existing fixed middle records can be removed from both counts before applying the argument. [Formal shared-injection bound](PALRH/LocalAgreement.lean)

For the shifted-clock box with $k=10$, the entire source has 9,800,859,664 records and there are 9,800,000,000 slots. The views omit prime distances in $(2500,2544]$, $(5000,5044]$ and $(7500,7544]$. Each fits by itself. Every pair of records is seen together somewhere. Exactly **859,664** records must change slots in the best possible agreement. At $k=8$ the corresponding minimum is zero. The replay constructs and checks the complete ordinal interval assignments, keeping the middle-prime slots fixed. The lower bound and its attainment concern the same head, same slot set and same three omissions. [Exact interval controls](../receipt-archives/check_pal_tick_layers.py)

For the ordinary clock the existence of eventual full agreement is equivalent to RH. For the shifted clock at height $x-2$, agreement alternates even if RH holds. More precisely the minimum is zero at infinitely many fourth powers, and exceeds $0.0099n^2$ at infinitely many others by the previously priced critical zero. Individually funded local views occur throughout both behaviors. This is a constructed control inside Pang’s program.
