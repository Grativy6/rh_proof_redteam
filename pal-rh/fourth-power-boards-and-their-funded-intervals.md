# Fourth-power boards and their funded intervals

Christopher Daniel Pang and Hearthline · 26 November 2026

Let $I_\theta(x)=\sum_{p\le x}(x-p)\log p$ and $I_\psi(x)=\sum_{m\le x}(x-m)\Lambda(m)$. At integer $n$ the board’s log margin is $G(n)=n^2-2I_\theta(n)-nH_n$, with $1\le H_n=\log(n!)-n\log n+n\le1+\log n$. Write $P(x)=x^2-2I_\theta(x)$. Positive $G$ gives enough total states, $G(n)>n$ pays even the paired decoder’s rounding, and $G(n)\le4(\log 2)n(\lfloor\sqrt n\rfloor+1)$ gives the fixed spare-room allowance. [Definitions, digits and source credit](the-prime-board-and-its-signed-area.md)

## Why fourth powers reach every intermediate size

Each function $(x-u)_+$ is convex. Integrating a positive prime or prime-power measure against it preserves convexity. Suppose first that the unrestricted board fits at every sufficiently large $n=k^4$. Then $I_\theta(n)\le n^2/2$ at those sizes. For $a=k^4\le x\le b=(k+1)^4$, the chord through the two areas gives
$$
I_\theta(x)-x^2/2\le (x-a)(b-x)/2\le(b-a)^2/8.
$$
Since $b-a\le15k^3$ for $k\ge1$, this is $O(x^{3/2})$. Adding repeated prime powers costs $O(x^{3/2})$, by $\psi-\theta=O(\sqrt x)$. Thus $V(x)=I_\psi(x)/x-x/2$ has an upper bound $C\sqrt x$ on $x\ge1$, after enlarging $C$ on a compact interval. The alternating-divisor argument in the previous proof gives RH. Conversely RH funds the full paired board at all sizes by the quantitative integrated estimates there. Thus eventual fit at the fourth powers is equivalent to RH, including for the paired scheme. [One-sided Mellin implication and conditional funding](the-prime-board-and-its-signed-area.md)

For the two-sided formal implication, set $E(n)=I_\psi(n)-n^2/2$. Suppose $|E(k^4)|\le Ck^6$ at the knots, as supplied by the two integer comparisons. Take $l=(k-1)^4$, $a=k^4\le n\le b=(k+1)^4$. The upper chord uses $a,b$. A lower line through $l,a$ follows from monotonicity of secant slopes. If $|E|\le T$ at these three knots, $b-l\le W$, and $b-a\le15(a-l)$, the two inequalities give
$$
|E(n)|\le 31T+W^2 .
$$
The lower line has coefficients $1+(n-a)/(a-l)$ and $-(n-a)/(a-l)$. The quadratic remainder there has magnitude $(n-l)(n-a)/2$. This accounts for both the factor 31 and the square of the physical width. Using $T=64Ck^6$ and $W=16k^3$ gives $|E(n)|\le(1984C+256)n\sqrt n$. The result passes to the stock RH proposition through the actual prime-power Mellin transform. [Lean interpolation and reduction](PALRH/QuarticBoards.lean) · [Independently fixed integer challenge](checks/quartic-boards/QuarticChallenge.lean)

This exponent is sharp for a deduction using only convexity and values on the grid. For any fixed integer $d>4$, interpolate $x^2/2$ linearly through $k^d,(k+1)^d$. The resulting continuous function is convex and agrees exactly at every knot. At a midpoint its excess is $(b-a)^2/8$, of order $x^{2-2/d}$, larger than $x^{3/2}$. This example identifies the additional arithmetic one would need to justify a coarser sampling argument for the same area.

## Where the middle of the band comes from

Let $W(x)=P(x)/x$ on $x\ge1$, and $\mathcal P(s)=\sum_p(\log p)p^{-s}$ on $\Re s>1$. Direct integration gives
$$
\int_1^\infty W(x)x^{-s-1}dx=\frac1{s-1}-\frac{2\mathcal P(s)}{s(s+1)}.
$$
With $L(s)=-\zeta'(s)/\zeta(s)$, expanding the Euler product over prime powers gives
$$
\mathcal P(s)=L(s)-L(2s)-\sum_{\substack{k\ge3\\ k\ {\rm odd}}}\mathcal P(ks).
$$
The final double sum converges locally uniformly for $\Re s>1/3$, by comparison with $\sum_{m\ge2}(\log m)m^{-3\sigma}/(1-m^{-2\sigma})$. This continues the displayed transform meromorphically there. At $s=1$ its two polar terms cancel. At $s=1/2$ it has residue $4/3$, because $L(2s)$ has residue $1/2$ there. At our enclosed simple zero $\rho=1/2+i\gamma$ its residue is $2/[\rho(\rho+1)]$. Its magnitude exceeds $0.0099$, since $14.13472<\gamma<14.13474$. The ordinary zero-free line $\Re s=1$ ensures $L(2\rho)$ is regular. The real interval $(0,1)$ is zero-free by the alternating eta series. [Local critical zero and elementary enclosure](the-boundary-of-the-signed-factorial-rows.md#locate-and-price-the-zero-independently)

For completeness, suppose that either orientation of $W(x)-(4/3)\sqrt x$ is eventually bounded above by $u\sqrt x$ with $0<u<|2/[\rho(\rho+1)]|$. Subtract that orientation from $u\sqrt x$. The result is eventually nonnegative and its Mellin integral has no real singularity on $(1/2,\infty)$. Taylor expansion of $x^v$ with nonnegative coefficients at a real convergence point, followed by monotone convergence, forces convergence throughout that real interval. Otherwise the real abscissa would be singular. Omitting the initial compact interval changes an entire function. As real $\sigma\downarrow1/2$, the transform times $\sigma-1/2$ tends to $u$. At $\sigma+i\gamma$ its absolute value times $\sigma-1/2$ tends to $|2/[\rho(\rho+1)]|$. Positivity bounds the latter by the former, which is impossible. Consequently for $g_n=G(n)/n^{3/2}$,
$$
\limsup g_n\ge \frac43+\left|\frac2{\rho(\rho+1)}\right|,
\qquad
\liminf g_n\le \frac43-\left|\frac2{\rho(\rho+1)}\right|.
$$
To pass to integers, $\theta(x)=O(x)$ makes $W'(x)=O(1)$ between corners, and $W(x)=O(x)$. Rounding a large real head to an integer affects $W(x)/\sqrt x$ by $O(x^{-1/2})$. The factorial correction $H_n/\sqrt n$ also tends to zero. This oscillation argument is in the classical line of Landau and Ingham. Johnston treats the one-sided integrated Chebyshev criterion and gives an oscillation lemma when RH fails. The board result here uses the real prime-square residue together with one actual nonreal residue. [Johnston, Theorem 1.2 and Lemma 2.8](https://arxiv.org/pdf/2201.06184)

## An entire stretch follows a crossing

Dusart’s unconditional estimate $\theta(n)-n=O(n/\log^2 n)$ yields $G(n)=O(n^2/\log^2 n)$. Also $I_\theta(n+1)-I_\theta(n)=\theta(n)$ and $0\le H_{n+1}-H_n=1-n\log(1+1/n)\le1/(n+1)$. Hence
$$
G(n+1)-G(n)=2(n-\theta(n))+1-H_{n+1}-n(H_{n+1}-H_n),
\qquad
|g_{n+1}-g_n|=O\!\left(\frac1{\sqrt n\log^2n}\right).
$$
The two limsup and liminf inequalities force arbitrarily late crossings of $4/3$. Choose an increasing sequence of crossing integers $N$ with $g_N\to4/3$. For any prescribed $h_N=o(\sqrt N\log^2N)$, telescoping shows $\sup_{|n-N|\le h_N}|g_n-4/3|\to0$. Take $h_N=\sqrt N\log N$. Every sufficiently late such interval meets both board bounds throughout, and contains increasingly many consecutive square heads. Dividing by $\log2$ converts its asymptotic spare capacity to $4/(3\log2)=1.92359\ldots$ bits per $n^{3/2}$. This is an unconditional subsequence statement. The spacing of these intervals is uncontrolled. [Dusart, Theorem 5.2](https://arxiv.org/pdf/1002.0442)

## One billion consecutive sizes from a finite sieve

Let $a<b$ be two computed anchors and $d=b-a$. For $a\le x\le b$, convexity of $I_\theta$ gives the lower bound for $P(x)$. A supporting line of slope $\theta(a)$ gives the upper bound. Incorporating $1\le H_n\le1+\log b$ yields
$$
\min(P(a),P(b))-d^2/4-b(1+\log b)
\le G(n)\le P(a)+2d\max(0,a-\theta(a))+d^2.
$$
Choose successive integer widths $\lfloor\sqrt{a\lfloor\sqrt a\rfloor}/2\rfloor$, shortening the last at the requested endpoint. A segmented Eratosthenes sieve counts primes in short bins $[l,r]$. Each of the $c$ primes contributes between $\log l$ and $\log r$ to $\theta$, and between $l\log l$ and $r\log r$ to $\sum p\log p$. Using both outward bounds in $P(n)=n^2-2n\theta(n)+2\sum_{p\le n}p\log p$ accounts for every prime in a bin. No assumption on their ordering inside a bin enters.

Use the previous direct proof up to 100,000. In every one of the next 1,284 intervals the left bound exceeds $b$ and the right bound lies below $4(\log2)a(\lfloor\sqrt a\rfloor+1)$. Together these cover every positive size through $10^9$, including the paired rounding cost and the bound on spare room. The last interval begins at 997,402,412. The segmented count and an independent sieve by division quotients both count 50,847,534 primes up to the last anchor. [Whole-interval arithmetic](../receipt-archives/check_pal_board_intervals.py) · [Ranges, margins and reproducibility](../receipt-archives/2026-11-26-pal-fourth-power-boards.json)

## Unresolved

The signed oscillation and the interval calculations supply genuinely funded stretches. To finish, prove the required upper fit throughout the unbounded sequence of fourth powers, or the two integer inequalities of the fixed Lean implication on that sequence. A few successful intervals do not bound the next gap.
