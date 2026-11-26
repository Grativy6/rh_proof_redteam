# How one-sided prime funding reaches RH

Christopher Daniel Pang and Hearthline · 26 November 2026

The fixed theorem assumes a single eventual whole-number inequality. For some natural $K$ and every $k\ge K$, at $n=k^4$,
$$
 \prod_{\substack{2\le m\le n\\ \gcd(m,(k^2)!)=1}}m^{n-m}
 \ \le\ \prod_{a=0}^n\binom{n}{a}.
$$
All mathematical inputs in the solution after this premise are derived in the PAL project or in its pinned stock Mathlib dependencies. The proof does not import the separate RH release. The reverse implication, from RH to this eventual inequality, was derived on paper using the integrated explicit formula. [The two finite resources](what-a-pascal-row-pays-for.md#the-remaining-two-integer-test)

## From counting states to an upper bound

At $n=k^4$, the gcd filter selects exactly the primes $p>k^2$. Write $R$ for the product on the left, $P$ for the product on the right and $B=n^{n^2}$. The unconditional inequality $(n!)^nP^2\le B$ funds the retained records as soon as $R\le P$. The omitted dials cost at most $4nk^2$ binary digits by the primorial estimate. A bound on demand therefore gives an upper bound $I_\theta(n)-n^2/2\le Cn^{3/2}$ at the fourth powers, from the exact board logarithm and the factorial remainder. Putting repeated prime powers back uses $\psi-\theta=O(\sqrt x)$. The finitely many early sizes are covered by enlarging $C$ using their actual finite readings. The chord of the nonnegative sum of ramps interpolates the upper bound at every integer. [Board price](PALRH/PrimeBoard.lean) · [Upper chord](PALRH/QuarticBoards.lean)

For real $x\ge1$, define the centered reading
$$
 V(x)=\sum_{d\le x}\Lambda(d)(1-d/x)-x/2 .
$$
Continue it by zero below 1. Raising the end of each nonnegative ramp to $\lfloor x\rfloor+1$ bounds the sum from above. Thus $V(x)\le C'\sqrt x$. Everything that follows uses that one direction.

## Price a finite alternating reading without any prime hypothesis

For $N$ large enough to include all nonzero terms let
$$
 A_Nf(x)=\sum_{j=0}^{N-1}\bigl[f(x/(2j+1))-f(x/(2j+2))\bigr].
$$
Put $S(x)=\sum_{r\le x}V(x/r)$, $A(x)=\sum_{m\le x}(1-m/x)\log m$ and $H_j=\sum_{r=1}^j1/r$. Regroup the finite products $m=rd$. Each original weight is kept, and $\sum_{d\mid m}\Lambda(d)=\log m$ yields
$$
 S(x)=A(x)-\tfrac x2H_{\lfloor x\rfloor},
 \quad A_NV(x)=S(x)-2S(x/2).
$$
Here $2N\ge\lfloor x\rfloor$ suffices. The following explicit lower estimate holds independently of any zero-location assumption:
$$
 A_NV(x)\ge-12\sqrt x\qquad(x\ge1).
$$

To see the cancellation, let $M=\lfloor x/2\rfloor$ and pair the log weights at $2j-1$ and $2j$ with the weight at $j$ for the half-sized reading. The odd ramp is at least the even ramp. Since $0\le1-2j/x\le1$, replacing $\log(2j-1)$ by $\log(2j)$ costs at most $\log(2j)-\log(2j-1)$. All such costs together are at most $\log(2M+1)$. The two even log terms leave $2\log2$ per unit of their ramp. Their ramp sum is
$$
 \sum_{j=1}^M(1-2j/x)=M-M(M+1)/x\ge x/4-2 .
$$
For $x\ge2$, the harmonic difference is at most $\log(\lfloor x\rfloor/M)\le\log2+1/(2M)$ by comparison with the integral of $1/t$. Multiplication by $x/2$ costs at most one extra unit. The two terms $(x/2)\log2$ cancel. Bounding the remaining constant and logarithm by $12\sqrt x$ gives the estimate. The initial interval $1\le x<2$ is evaluated directly. [Lean divisor identity and paired-log estimate](PALRH/PrimeDivisorPrimitive.lean)

## Why the first pair controls an entire octave

Let $L(x)=\int_0^x V(t)\,dt/t$. The support removes the singularity at zero. If $V(t)\le C\sqrt t$, then $L(x)-L(y)\le2C(\sqrt x-\sqrt y)$ for $0\le y\le x$. Consequently $D(x)=2C\sqrt x-L(x)$ is nonnegative and nondecreasing. A finite change of variable in each dilated term gives
$$
 A_N L(x)=\int_0^x A_NV(t)\,\frac{dt}{t}\ge -24\sqrt x .
$$
The same $N$ covers every $t\le x$. At $t<1$ all the prime terms vanish. Also $0\le A_N(\sqrt{\phantom x})(x)\le\sqrt x$ by ordinary alternating pairs. Therefore
$$
 0\le D(x)-D(x/2)\le A_ND(x)\le(2C+24)\sqrt x .
$$
The middle inequality keeps the first pair and uses monotonicity on every other pair. Iterate to an argument below 1, where $L=0$. The formal proof uses $4\sqrt{x/2}\le3\sqrt x$ at each return and gives
$$
 |L(x)|\le4(2C+24)\sqrt x\qquad(x\ge0).
$$
This is a pointwise square-root bound on the **primitive**, earned from a one-sided bound on the original reading. The original reading and its accumulated value have distinct roles. [General positive-pair recovery](PALRH/PositivePrimitive.lean) · [Physical scale changes and integration](PALRH/PrimitiveRecovery.lean)

## Why that bound reaches the ordinary target

Integrate each finite ramp to get
$$
 L(x)=\sum_{d\le x}\Lambda(d)\bigl[\log(x/d)-1+d/x\bigr]-(x-1)/2
 \qquad(x\ge1).
$$
In reciprocal coordinates, the pulse $w(t)=t-1-\log t$ on $0<t\le1$ has Mellin transform $1/[s^2(s+1)]$ for $\Re s>0$. Its nonnegativity permits absolute interchange of the prime-power sum and the Mellin integral on $\Re s>1$. The elementary center $(1/t-1)/2$ has transform $1/[2(s-1)]-1/(2s)$. It follows that
$$
 s\int_0^1 L(1/t)t^{s-1}dt
  =-\frac{\zeta'(s)}{s(s+1)\zeta(s)}-\frac1{2(s-1)}
 \qquad(\Re s>1).
$$
The square-root bound on $L$ makes the left side holomorphic for $\Re s>1/2$. At any zeta zero there in the critical strip the right-hand logarithmic derivative has a pole with nonzero residue. Analytic continuation excludes such a zero. Reflection gives the stock RH proposition. [Finite integrated weights](PALRH/LogPrimitive.lean) · [Kernel transform](PALRH/PrimitiveMellin.lean) · [One-premise deduction](PALRH/OneSidedBoard.lean)

At $x=2663$ direct prime-power calculation gives $A_NV(x)$ between −1.16940231 and −1.16940230, and $A_NL(x)$ between −6.81149793 and −6.81149792. The independent all-integer log and harmonic formulas give overlapping outward enclosures for both. These finite examples illustrate the transfer. Establishing the eventual subset comparison is the remaining mathematical obligation. [Finite replay](../receipt-archives/check_pal_one_subset.py)
