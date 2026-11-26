# How far a square mark must reach

Christopher Daniel Pang and Hearthline, 26 November 2026 (New York).

At $5,184=72^2$, a single mark of weight **+72** lands. The running count is already **−745** after it lands. Those are two different observations. Starting at the new mark and widening a window backwards, give the newest mark weight $h$, the one before it $h-1$, and so on down to one. The weighted total is still **+14 at width 775**. It becomes **−24 at width 776**. Looking forward from the same mark first reaches a nonpositive total at width 1,113.

This is an example of a proof condition in which **each head can choose its own width**. An ordinary integer inequality on one such window per head suffices for stock Mathlib RH. On infinitely many actual positive square marks, any successful choice must reach at least $(2\pi^2/9-o(1))$ times the square root of the head. We can prove that obstruction without knowing the signs of the intervening Möbius coefficients.

## Why one earlier window suffices

Use $a(v^2d)=v\mu(d)$ with $v=2^i3^j$, $(d,6)=1$, zero on the other labels. Write $M(n)=\sum_{d\le n}a(d)$ and $M(0)=0$. For $0\le m<n$, let $h=n-m$ and define
$$
 T(n,h)=\sum_{d=m+1}^n(d-m)a(d)
        =\sum_{k=m}^{n-1}[M(n)-M(k)].
$$
Each $a(d)$ appears for exactly $d-m$ values of $k$. The second expression compares the current height to the preceding average. If there is a width with $T(n,h)\le0$, the new height is at most one of the earlier heights. If such a width exists at every sufficiently late head, a finite initial maximum bounds all $M(n)$ from above. The [finite rectangle argument](how-much-can-the-newest-half-gain.md) then gives RH.

The new height may also rise. For $b(n)=\sqrt n$ the exact allowance is
$$
 D(n,h)=\sum_{k=m}^{n-1}(\sqrt n-\sqrt k),\qquad
 \frac{h(h+1)}{4\sqrt n}\le D(n,h)\le\frac{h(h+1)}{2\sqrt n}.
$$
Rationalize each difference and sum the integers from 1 to $h$. Suppose that, for some natural $K$, at each $n\ge1$ at least one width satisfies
$$
 n\,\max(0,T(n,h))^2\le K h^2(h+1)^2 .
$$
Induction now gives $M(n)\le4\sqrt{Kn}$. At a first excess over that barrier, $M(n)-M(k)$ would strictly exceed the corresponding barrier difference for *every* earlier $k$. It would do so on the very width that had been chosen to fund the new head. The implication to stock RH uses no hypothesis about how the widths were selected. [Formal maximum principle](../pal-rh/PALRH/TrailingRows.lean) · [Independent integer statements](../pal-rh/checks/trailing-rows/RowChallenge.lean) · [Conditional proofs](../pal-rh/checks/trailing-rows/RowSolution.lean)

The direction of time matters here. Allowing future heights in the maximum principle would already fail for $M(n)=n$, which is below all of its future averages yet outgrows every square-root ceiling.

## A finite test that includes all possible widths

Let $C(n)=\sum_{k<n}M(k)$. The average on $(m,n]$ is the slope from $(m,C(m))$ to $(n,C(n))$. The largest such slope is the last incoming edge of the lower convex hull after inserting the new point. To see this, compare the slopes through three successive points. If the newest slope is at most its predecessor, the middle point cannot improve the incoming maximum, so remove it and repeat. The remaining slopes increase, and the last edge attains the maximum. Thus a single pass finds precisely the heads at which **all** widths cost something.

Among the first **50,000,000 heads**, the full list is **1, 4, 9, 16 and 36**. At each of these five we priced every width. The largest of the five optimal squared allowances is $256/289$, attained at 16 with width 16. Hence the smallest natural $K$ for this entire prefix is **1**. There are 16 heads where the full-width price is positive and a shorter width rescues it. An independent brute-force calculation also tries every width at every positive mark through 4,096. [Native hull search](../receipt-archives/trailing_row_hull.cpp) · [Replay and full figures](../receipt-archives/2026-11-26-pal-trailing-rows.json)

For $n>50$ million, the full-width price is just $U(n)=\sum_{d\le n}d\,a(d)$. Two quotient recurrences from different inputs give identical first and zeroth moments. For example $U(10^{13})=-963749535440427659775$. On each interval $[l,r]$ bounded by two sampled heads, the variation in $U$ is at most $r\sum_{l<d\le r}|a(d)|$. If the two endpoint values plus that bound sum to a negative number, every intermediate value is negative. The direct calculation proves that a nonpositive width exists at **every integer from 37 through 5,906,674,542**.

A second bound uses the older exact ordinary sieve through 200 million and the published ordinary Mertens bounds above it. From $U_\mu(k)=kM_\mu(k)-\sum_{s<k}M_\mu(s)$ these give $U_\mu(k)\le0.913\,k^{3/2}+20100$ in the stated high range. The small allowance covers $s\le200$. The positive divisor weights $b(q)$ from the original measure give $U(n)=\sum_{q}q b(q)U_\mu(\lfloor n/q\rfloor)$. Using the actual binned maxima of $U_\mu$ when available gives a nonpositive width through **9,793,285,009**, and a valid squared allowance **$K=9421$** for every head through ten trillion. The first upper envelope to cross zero is an open interval for that estimate. The exact trillion-scale sample itself is computed without this external input. [Native moment recurrences](../receipt-archives/trailing_row_moments.cpp) · [Panel replay](../receipt-archives/check_pal_trailing_rows.py) · [Lioen and van de Lune, §6](https://ir.cwi.nl/pub/13491/13491D.pdf)

## A floor on the reach of a real square mark

Take $v=2^i3^j$, $A=4^i$, $B=9^j$. There are arbitrarily large choices with $j$ odd, $i\equiv1\bmod3$ and $2^i/3^j\to1$. Indeed $(2r+1)\log 3/\log 2$ is dense modulo 3 by irrational rotation, so it comes arbitrarily close to $3s+1$. On this sequence $A/v,B/v\to1$. At $n=v^2$ the mark is $+v$. At $n=5v^2$ it is $-v$. In each case price the center with its own sign and compare it to its neighbors on either side.

For offsets $1\le e\le2.2v$ which are multiples of neither $A$ nor $B$, the valuations at 2 and 3 of $n\pm e$ equal those of $e$. An occupied neighbor therefore has $e=w^2d$ with $w$ smooth, $(d,6)=1$ and weight at most $w$ in absolute value. Fix finitely many primes $p\ge5$. For each such $p$, a square factor $p^2\mid n\pm w^2d$ rules out one residue class of $d\bmod p^2$. The Chinese remainder theorem gives the count
$$
 \frac{z}{3}\prod_p(1-p^{-2})+O_P(1)
$$
through $z$ for the remaining rough $d$. The error is uniform in $n,w$ and orientation, since it only counts an incomplete period. Put $\kappa_P=\prod_p(1-p^{-2})$. Summing over $w^2\le H$ gives at most $\kappa_P H+O_P(\sqrt H\log(2H))$ in absolute weight through offset $H$. Here $\sum_w1/w=3$ and $\sum_{w\le\sqrt H}w\le2\sqrt H(1+\log_3\sqrt H)$.

The exceptional offsets are $A,2A,B,2B$ at most for these heads. At $kA$ the remaining factor is $d_0B\pm k$, with $d_0=1$ or $5$ and $k=1,2$. Since $B\equiv9\bmod16$, its exponent at 2 is bounded and its exponent at 3 is zero. The resulting weight is $O(2^i)$. At $kB$ the remaining factor is $d_0A\pm k$. For $k=1$, $A\equiv4\bmod9$ bounds its exponent at 3. For $k=2$, its exponent at 2 is one and the mark vanishes. These exceptions first occur at $H\asymp v$ and contribute $O(\sqrt H)$ in total.

Summing the prefix allowances over $H<h$ bounds the triangular contributions of every preceding neighbor. For the oriented centered price, on either side, this proves uniformly for $1\le h\le2.2v$
$$
 T_{\rm oriented}(n,h)\ \ge\
 hv-\frac{\kappa_P}{2}h(h-1)-O_P(h^{3/2}\log(2h)).
$$
The full product over $p\ge5$ is $\kappa=9/\pi^2$, by the Euler product at 2. For fixed $\epsilon>0$ choose the finite prime set first and then take $v$ large. All widths $h\le(2/\kappa-\epsilon)v$ have price at least $c_\epsilon h v$, with $c_\epsilon>0$. At the positive heads $n=v^2$ this forces $n T^2/[h^2(h+1)^2]\to\infty$ uniformly over these widths. The negative heads give the same obstruction with sign reversed and $v=\sqrt{n/5}$. This calculation explains the constant $2\pi^2/9$ and exactly which real inputs incur the cost. [Euler product](https://dlmf.nist.gov/25.2) · [Zeta value at two](https://dlmf.nist.gov/25.6)

At $v=62,208$, the first **1,990,656** widths in each direction still have a positive oriented price at $v^2$, and at $5v^2$ after reversing the sign. At $v=4,478,976$, the same holds through **71,663,616** widths at the positive square. A segmented prime sieve visits every original label. The shorter examples were also checked by trial division. [Segmented scan](../receipt-archives/trailing_spike.cpp) · [Widths and both orientations](../receipt-archives/2026-11-26-pal-trailing-rows.json)

Pang’s PAL v2.4 orientation and retained-mark questions, RPL’s old/detail split, and BLA’s accounting for an actual change of boundary led Hearthline to let the head choose its own incoming interval. The finite maximum principle, paid physical portion and spike obstruction were derived in Pang’s constructive program. [Corpus routes](../pal-rh/CORPUS-ROUTES.md) · [Which part of a moving row has already been paid](../pal-rh/which-window-pays-for-the-return.md)

## Unresolved

One adequately priced incoming width must be found at every head. A large positive square can force all short choices to fail. The signed calculation on longer windows earns part of their allowance at every sufficiently large scale. The unassigned part can still affect the sign.
