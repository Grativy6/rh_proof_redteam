# What a multiple-labelled address costs

Christopher Daniel Pang and Hearthline · 26 November 2026

Consider the ordinary prime-trip board with $n=k^4$, $x=\sqrt n$ and the minimum actual height $H=\lceil J/n^2\rceil$. Let $b=\lfloor\log_2 n\rfloor+1$, $B=\lceil xb/H\rceil$, and $Y=\lfloor n/(4B)\rfloor$. All asymptotic statements here concern fourth powers tending to infinity. The prime number theorem gives $H\sim x$ and $Y\sim(\log2)n/(4\log n)$. [Counting the actual jobs and layers](how-prime-trips-change-distance.md#a-construction-in-the-other-direction)

Reserve the existing addresses for every middle prime $x<p\le Y$. For a source start $i$ and tick $t$, set $a=\lceil n/2\rceil$. Its physical distance is

$$
 d=\big(2\lfloor t/H\rfloor+\lfloor i/a\rfloor+1\big)p .
$$

The remaining coordinates recover $i\bmod a$, $t\bmod H$ and the travel direction. Each occupied distance is at most $2Bp\le n/2$ and has only one prime divisor above $x$. The minimum possible maximum travel of the remaining jobs $p>Y$ is denoted by $W_{\rm fixed}$. We obtain

$$
 W_{\rm fixed}\sim Y .
$$

This gives the leading exterior cost of the existing reversible address. In the fully movable model the unconditional maximum needed is $o(n/\log^a n)$ for every fixed $a$. The original middle jobs have been held fixed throughout the first optimization. [Earlier multiple decoder](one-prime-trip-in-a-shared-lattice.md#a-recoverable-position-for-each-middle-prime-record) · [Fully movable bound](how-prime-trips-change-distance.md#a-construction-in-the-other-direction)

## The forced return trip

If the exterior radius is $W$ and $T=\max(0,Y-W)$, every available column at positive distance at most $T$ stays unused by the exterior jobs. For any scheme storing middle jobs at multiples of their own primes, the count of potentially occupied positive labels in this interval is at most

$$
 \sum_{x<p\le n}\lfloor T/p\rfloor\le T\sum_{x<p\le n}1/p=(\log2+o(1))T .
$$

The last relation follows from the prime number theorem by partial summation on $[\sqrt n,n]$. A fixed positive fraction of the $T$ columns therefore stays entirely empty. Each contains at least $2H(n-Y)$ physical cells. Fewer than $n^2$ cells in the box can be empty. This forces $T=O(x)$ for every such scheme, irrespective of the exact multiple assigned.

For the displayed decoder each multiplier $r$ is at most $2B=O(\log n)$. If $T/r\le x$ it contributes nothing. Otherwise $\pi(T/r)\ll T/(r\log x)$ by the ordinary prime counting bound. Summing over $r$ bounds the number of occupied labels through $T$ by $O(T\log(2B)/\log x)=o(T)$ uniformly in $T$. Thus $2H(n-Y)(1-o(1))T<n^2$ whenever $T>0$, which gives the sharper lower bound

$$
 W_{\rm fixed}\ge Y-(1/2+o(1))x .
$$

## Where the middle records land

Let $I$ be the total number of reserved records. Their mass at prime $p$ is $2(n-p)t_p$, so by tick rounding and the prime number theorem $I\sim2HnY$. In fact their destination distance, divided by $n$, has limiting distribution $\beta UV$, where $\beta=(\log2)/2$ and $U,V$ are independent uniform variables on $[0,1]$.

To see it, fix $0<\delta<1$ and first use $\delta Y\le p\le Y$. The weighted empirical measure of $p/Y$ tends to ordinary length there. Indeed $n-p=n(1+o(1))$, $t_p=(x+O(1))\log p+O(1)$, and $\theta(vY)-\theta(uY)\sim(v-u)Y$ for any fixed $\delta\le u<v\le1$. For each such $p$, $t_p/(H\log n)\to1$ uniformly. The full evenly spaced ticks therefore give a uniform limit for $\lfloor t/H\rfloor/\log n$ independent of $p/Y$. Replacing the parity term $\lfloor i/a\rfloor+1$ in the multiplier by zero changes $d/n$ by at most $2Y/n$. Finally $2Y\log n/n\to\beta$. The discarded primes through $\delta Y$ carry at most $O(\delta I)$ in the limit. Sending $\delta$ to zero proves the claim for the entire middle set.

The fraction of reserved jobs beyond $zn$ consequently converges to $L(z/\beta)$, where

$$
 L(s)=1-s+s\log s \quad(0<s<1),\qquad L(0)=1,\qquad L(s)=0\quad(s\ge1).
$$

For $0<s<1$, integrate $1-s/u$ over $s<u<1$ to obtain the formula. Because the distribution is continuous, convergence of the monotone tail functions is uniform on $[0,1]$. The small prime cutoff gives a specific nonuniform shape in the receiving columns.

## A matching exterior construction

Order exterior jobs from the largest prime down, and free physical cells from largest distance down. Place them in that order. For a source with $p/n\to z<1$ and destination distance $d$, we have

$$
 \frac{p-d}{Y}\longrightarrow\frac{L(z/\beta)}{1-z}.
$$

Let $R(d)$ be the count of reserved records strictly beyond $d$. The available tail at $d$ is $H(n-d)(n-d-1)-R(d)$. The exterior source tail at $p>Y$ is exactly the full source tail there. Its difference from $H(n-p)^2$ is $O(H(n-p+1)E_n)$, where $E_n=o(Y)$ from the unconditional prime error bound. The full source jump at $p$ is $O(Hn\log n)=o(HnY)$, and a destination jump is at most $2Hn$. [Tail calculation](how-prime-trips-change-distance.md#a-construction-in-the-other-direction)

For $p\ge3n/4$, every sufficiently late such job stays beyond $n/2$. Its far-end rank is at most $Hn^2(1/16+o(1))$ while all $Hn^2(1/4+o(1))$ far-end cells beyond $n/2$ are free. Here the fully movable bound gives travel $O(E_n)$. For $p\le3n/4$, comparison of the two squared tails first gives $|p-d|=O(Y)$ uniformly since $R(d)\le I=O(HnY)$ and $n-p\ge n/4$. Uniform convergence of the reserved tails then gives $R(d)=I L(p/(n\beta))+o(I)$. Expanding the exact square costs $O(HY^2)=o(HnY)$ and yields

$$
 2H(n-p)(p-d)=I L(p/(n\beta))+o(HnY).
$$

This proves the profile also at $z=0$ and $z=\beta$. Since $L(z/\beta)\le1-z$ for $0\le z<1$, the constructed radius is at most $(1+o(1))Y$. Together with the forced low-distance hole this proves the stated asymptotic optimum.

Pang’s RPL return question asks which input remains recoverable after a change of frame. Here the prime’s divisibility mark genuinely recovers the input and genuinely forces expensive travel for other records. The rank decoder is an explicit alternative with its own exact inverse. The derivation concerns the independent prime board developed in Pang’s PAL program. Its mathematical inputs are the integer trip counts and classical prime estimates identified above. [Source roles](../proofs/PROVENANCE.md) · [Implementation and finite witnesses](../receipt-archives/2026-11-26-pal-local-distance.json)
