# The prime board and its signed area

Christopher Daniel Pang and Hearthline · 26 November 2026

For $n\ge1$ set $e_p=2(n-p)$ for primes $p\le n$, $D_n=\prod_{p\le n}p^{e_p}$, $N_n=(n!)^nD_n$ and $B_n=n^{n^2}$. Three universal assertions are equivalent to RH. The first is $N_n\le B_n$ at every size. The second also requires $B_n\le N_n2^{4n(\lfloor\sqrt n\rfloor+1)}$. The third asks that the particular two-cell encoder below fit at every size, with or without that same upper bound on spare room. All quantifiers range over positive integers. The only size with one board is $n=1$, where all counts equal one apart from the optional allowance. [Teaching example](../proofs/how-much-room-the-prime-board-needs.md)

## The exact area

Write $\theta(x)=\sum_{p\le x}\log p$, $\psi(x)=\sum_{m\le x}\Lambda(m)$ and
$$
I_\theta(x)=\sum_{p\le x}(x-p)\log p,\qquad
I_\psi(x)=\sum_{m\le x}(x-m)\Lambda(m).
$$
For $x\ge2$ these are the integrals from 2 to $x$ of the corresponding step functions. Logarithms count independent settings additively. Integrating the increasing function $\log t$ between its left and right integer sums gives $1\le H_n=\log(n!)-n\log n+n\le1+\log n$. It follows directly that
$$
G(n)=\log(B_n/N_n)=n^2-2I_\theta(n)-nH_n .
$$

If every board fits, $I_\theta(n)-n^2/2\le-n/2$. For $x=n+u$, $0\le u\le1$, the difference $I_\theta(x)-x^2/2$ equals the linear interpolation of its endpoint values plus $u(1-u)/2$. Hence $\int_2^x(\theta(t)-t)\,dt<0$ for $x\ge5$. On $2<x\le5$ the step heights on the open subintervals are $\log 2$ and $\log 6$, both below $t$. Johnston’s Theorem 1.2 gives RH. The following section supplies another derivation of this direction from a signed divisor sum. [Johnston, *On the average value of π(t) − li(t)*](https://arxiv.org/pdf/2201.06184)

Conversely assume RH. Put $Q(x)=I_\psi(x)-x^2/2+2$ and $\Delta=I_\psi-I_\theta$. Johnston’s Lemmas 2.3 and 2.6 give $|Q(x)|\le0.08x^{3/2}$ for $x\ge3000$ and $0.98\sqrt t<\psi(t)-\theta(t)<1.5\sqrt t$ there. Summing the finite prime and prime-power lists at 3,000 gives $136068.02545226<\Delta(3000)<136068.02545227$. Integrating from 3,000 gives $(2/3)(0.98)x^{3/2}<\Delta(x)<x^{3/2}$. Thus
$$
G(n)=4-2Q(n)+2\Delta(n)-nH_n,\qquad
n<G(n)<2.17n^{3/2}\quad(n\ge3000).
$$
For the lower bound use $1+\log n<\sqrt n/2$ in this range, by differentiation. The upper bound is below $4(\log 2)n(\lfloor\sqrt n\rfloor+1)$. The direct integer products, or the outward logarithm enclosures in the replay, handle $2\le n<3000$, including their two-cell loss below. [Johnston, Lemmas 2.3–2.6](https://arxiv.org/pdf/2201.06184) · [Finite heads and initial integrals](../receipt-archives/2026-11-26-pal-prime-board.json)

## Why a bound in one direction reaches zeta

Suppose $I_\theta(n)\le n^2/2$ at every positive integer. Interpolation supplies the real-variable inequality with an additive $1/8$. The ordinary bound $\psi(t)-\theta(t)=O(\sqrt t)$ follows by separating prime squares from higher powers and applying $\theta(y)=O(y)$. Hence
$$
V(x)= I_\psi(x)/x-x/2 \le C\sqrt x \quad(x\ge1).
$$
Extend $V$ by zero below 1. Define $S(x)=\sum_{r\le x} V(x/r)$, $A(x)=\sum_{m\le x}(1-m/x)\log m$ and $H^{(1)}_k=\sum_{r=1}^k1/r$. Since $\sum_{d\mid m}\Lambda(d)=\log m$, regrouping the same finite labels gives
$$
S(x)=A(x)-\tfrac x2 H^{(1)}_{\lfloor x\rfloor},\qquad
S(x)-2S(x/2)=\sum_{r\le x}(-1)^{r+1}V(x/r).
$$
The last expression is $O(1+\log x)$ for $x\ge1$. Indeed, replacing the sums of $\log m$ and $m\log m$ by their integrals, with endpoint errors bounded by their final heights, gives $A(x)=x(\frac12\log x-\frac34)+O(1+\log x)$. The difference $H^{(1)}_{\lfloor x\rfloor}-H^{(1)}_{\lfloor x/2\rfloor}$ is $\log 2+O(1/x)$ by integral comparison for $x\ge2$. The two terms of size $(x/2)\log2$ cancel. The bounded initial interval is harmless.

Set $F(x)=C\sqrt x-V(x)\ge0$ on $x\ge1$ and zero below 1. Its alternating sum $U(x)=\sum_{r\le x}(-1)^{r+1}F(x/r)$ is $O(\sqrt x)$, since the alternating partial sums of $1/\sqrt r$ lie between zero and one. For any real $b>1/2$ let $J(X)=\int_1^X F(y)y^{-b-1}dy$ for $X\ge1$, extended by zero below 1. On a finite interval the change of variables $x=ry$ gives
$$
\int_1^X U(x)x^{-b-1}\,dx
=\sum_{r\le X}(-1)^{r+1}r^{-b}J(X/r)
\ \ge\ (1-2^{-b})J(X).
$$
Each term before its sign decreases with $r$, because $J$ is nonnegative and increasing. The first pair pays the displayed fraction of $J(X)$, and every subsequent pair contributes a nonnegative amount. An unpaired last term has positive sign. The integral on the left stays bounded as $X\to\infty$. This proves that $\int_1^\infty |V(x)|x^{-b-1}dx$ converges for every $b>1/2$, since $|V|\le C\sqrt x+F$.

Its complex Mellin integral is holomorphic on $\Re s>1/2$ by domination on each compact subset using a slightly smaller $b$. On $\Re s>1$, integrate the finite pulses and sum the absolutely convergent von Mangoldt series to obtain
$$
\int_1^\infty V(x)x^{-s-1}dx
=-\frac{\zeta'(s)}{s(s+1)\zeta(s)}-\frac1{2(s-1)}.
$$
A zero in the open right half of the critical strip gives a pole with nonzero residue here. Holomorphy excludes it. Reflection gives the other half. The one-sided integer premise has done all the arithmetical work in this implication. Establishing that premise remains the constructive task.

The Lean theorem in this edition takes both integer comparisons. It derives the two-sided $O(n^{3/2})$ estimate for the prime-power area, extends the resulting integral and concludes the stock proposition. The independent challenge declares the natural-number products afresh. The one-sided alternating-sum argument above is a paper proof. [Finite sums and their Mellin integral](PALRH/LinearPrimeIntegral.lean) · [Whole-number implication](PALRH/PrimeBoard.lean) · [Fixed challenge](checks/prime-board/BoardChallenge.lean)

## How much the decoder costs

The number $E=\sum e_p$ of occupied prime cells is at most $n^2/2$. Odd distances use at most $2\lfloor n/2\rfloor\lceil n/2\rceil$ cells. Remove the $2(n-1)$ cells at distance one, and include the $2(n-2)$ cells at distance two when $n\ge2$. All remaining prime distances are odd. Give each prime cell a distinct cell from the complement in row-major order. Its $p$-state dial and $\lfloor n^2/p\rfloor$-state extra digit fit reversibly by ordinary quotient and remainder. The other cells retain $n$ states each.

The aggregate residual capacity is $n^{n^2-2E}\prod_p\lfloor n^2/p\rfloor^{e_p}$. Rank each row permutation by successive choices among the remaining symbols and combine the row ranks in base $n!$. Repeated Euclidean division stores the result in those residual places whenever the product is at least $(n!)^n$. This is exactly the paired cross-multiplied inequality in the challenge. Per pair the rounding loss is $\log(n^2/(n^2-a))\le a/(n^2-a)\le1/n$, with $a=n^2\bmod p\le n-1$. Thus the total loss is at most $E/n\le n$. The preceding RH estimate pays this loss at all large sizes. A paired fit always implies the unrestricted fit by counting.

### Why the single-cell arrangement eventually fails

With one cell per prime dial, the rounding loss is
$$
W_n=2\sum_{p<n}(n-p)\log\!\frac{n}{p\lfloor n/p\rfloor}.
$$
The prime number theorem on any fixed interval $\delta\le p/n\le1$ gives $W_n\sim A n^2/\log n$ after letting $\delta\downarrow0$, where
$$
A=2\int_0^1(1-t)\log\!\frac{1}{t\lfloor1/t\rfloor}\,dt
=\frac32-\sum_{k=2}^{\infty}(2/k-1/k^2)\log\!\frac{k}{k-1}.
$$
The integrand is strictly positive on a positive-length interval. At $t\le1/2$ the logarithm is bounded by $2t$, so the omitted small primes contribute $O(\delta^2n^2/\log(\delta n))$ using the elementary prime count bound. Integrating on $(1/(k+1),1/k]$ gives the displayed series. Its evaluated enclosure is $0.185663238<A<0.185663240$. Dusart’s unconditional estimate $\theta(x)=x+O(x/\log^2x)$ implies $G(n)=O(n^2/\log^2n)$ by integration. Thus $W_n>G(n)$ at every sufficiently large size. Some finite sizes after the first failure can still fit. [Dusart, Theorem 5.2](https://arxiv.org/pdf/1002.0442) · [Arithmetic replay](../receipt-archives/check_pal_prime_board.py)

A different allocation also has an exact obstruction. If every prime pair must take *two whole* Lehmer digits, while every remaining original cell takes one, a prime $p>n/2$ gives fewer than $2n$ available residual states. At least one of its two digits must have radix at most $\lfloor\sqrt{2n-1}\rfloor$. There are just $n\lfloor\sqrt{2n-1}\rfloor$ such digits, counting the radix-one places. At 1,563 the number of these prime pairs is 86,104 and only 85,965 small digits exist. For large $n$ the counts grow as $n^2/(4\log n)$ and $O(n^{3/2})$, respectively. The global mixed-radix decoder pays for arbitrary splits of the row ranks.
