# One product, one direction per board

Christopher Daniel Pang and Hearthline · 26 November 2026

Multiply the distance labels that pass the factorial sieve through a cut. All the separate clocks can be recovered from a clock on this single product plus at most one flagged tick at each prime. Our formal RH test can now use just that product and integer powers. **Each board can choose its own direction of comparison. Its choice has to work at every cut on that board.** [Fixed statement](../pal-rh/checks/product-direction/ProductChallenge.lean) · [Formal proof](../pal-rh/PALRH/BoardOrientation.lean)

Here is the complete criterion. At index $j\ge0$ put $M=16^j$, $x=4^{j+1}(j+1)^2$, $P_m=\prod_{2\le d\le m,\ \gcd(d,x!)=1}d$ and
$$
 a=\lfloor x/13\rfloor,\quad b=(a-\lceil M/x\rceil)_+,\quad
 H_m=x((m-x)_++b),\qquad L_m=x((m-x)_+-a)_+ .
$$
At every $j$, at least one of these assertions must hold:
$$
 \begin{aligned}
 &\text{for all }0\le m\le M,\qquad P_m x^{H_m}\le(x+1)^{H_m},\\
 &\text{for all }0\le m\le M,\qquad (x+1)^{L_m}\le P_m x^{L_m}.
 \end{aligned}
$$
This condition implies stock Mathlib RH in Lean. On paper RH gives both comparisons at all the cuts. The remaining mathematical task is to earn a board-wide choice at every size. The guard $\lceil M/x\rceil$ reserves room for the original ticks whose separate rounding the product clock omitted. [How each true record is funded](../pal-rh/two-roundings-on-the-same-primes.md)

**Moving the choice by one quantifier changes the result.** If a cut can choose its own direction after the product is read, one of the two inequalities holds automatically for every nonnegative input value. This unconditional theorem and the board-wide conditional theorem appear in the same independent challenge. Both have short human-readable meanings. [Declarations and both verdicts](../receipt-archives/2026-11-26-pal-product-direction.json)

## Where the original ticks went

At sixteen sites the retained product is $5\cdot7\cdot11\cdot13=5,005$. The four separate clocks have $8+9+11+12=40$ ticks per full sequence. The product takes 39. The extra tick belongs to distance 7, where there are nine forward starts. The 251 product-clock records and nine named flag records together account for the original 260. We decoded them all. The same rule stores the flag of a later prime in the initial row pocket, where its address identifies the prime that produced it.

There are two distinct kinds of rounding in this experiment. One concerns multiplying until a prime is reached. The other concerns opening a whole column of $x$ lanes. Through 16,777,216, 506,582 of 1,013,709 primes had a separate-clock flag, 531,994 saved a whole column by sharing it, and 266,179 did both. We can account for the asymptotic frequency of the two bits together using the actual prime arrivals. [Arithmetic and phase proof](../pal-rh/two-roundings-on-the-same-primes.md) · [Original whole-column returns](which-empty-cells-must-cross.md)

## Why the board can choose its own side

One signed inequality on a board controls a logarithmic integral of the actual prime weights in both directions **on that board**. The proof pairs readings at $t,t/2,t/3,t/4,\ldots$. Every argument is at most $t$. The estimate consequently stays inside the observed region. Once both sides of the integral have been paid, the next board is free to choose the opposite sign.

More precisely, on a board with observed horizon $M$ its chosen orientation gives $\sigma V(t)\le Cx$ for $1\le t\le M$, with the same $C$ on every board. For any $d>0$ one may replace this by $Cx t^d$. Apply the positive first-pair argument with weight $t^d$. Halving reduces this weight by $2^{-d}<1$. The bound on the alternate reading of the primitive is $24\sqrt t\le24x t^d$ in the whole observed region. This yields $|\int_0^t V(v)\,dv/v|\ll_d x t^d$. Use the first geometric board covering $t$ and absorb its squared logarithm in $t^d$. Taking $d$ arbitrarily small yields every exponent above one half for this same primitive. Its Mellin transform reaches the ordinary zeta function. [Local recovery and analytic transfer](../pal-rh/PALRH/BoardOrientation.lean) · [The underlying divisor calculation](why-either-side-of-the-pocket-is-enough.md)

Pang supplied the ordered trace, the same-frame return and the instruction to try each direction. Hearthline derived the product clock, guard, local recovery, and board-level choice within Pang’s independent program. [Corpus roles](PROVENANCE.md)
