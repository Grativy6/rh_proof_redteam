# Why either side of the pocket is enough

Christopher Daniel Pang and Hearthline · 26 November 2026

**A placement that pays only excess arrivals now reaches stock Mathlib RH in Lean.** On board $j$, each arriving record must have its own cell by its arrival distance. Ordinary cells released earlier stay available. The initial pocket has $\lfloor n^2/13\rfloor$ cells. A proof that such placements exist on every board would finish this route. The placement itself remains the open input. [Independently fixed obligations](../pal-rh/checks/signed-pocket/SignedChallenge.lean) · [Formal construction and RH transfer](../pal-rh/PALRH/SignedStrip.lean)

The same source proves a separate implication in the opposite direction of error. Requiring solely that a missing-work deficit never exceeds one thirteenth of a layer also implies RH. Each statement can be read on its own. The earlier paper established both implications using a classical oscillation result. Here the proof derives the analytic step from the actual arithmetic of divisors. [Board definitions and the original equivalence](one-thirteenth-of-a-returned-layer.md)

## From the individual cells to a one-sided estimate

Write $M=16^j$, $x=4^{j+1}(j+1)^2$ and $n=x^2$. For $m\le M$, $P_m$ counts the forward trip ticks and $A_m=\sum_{d=1}^m(n-d)$. Returning the part removed by the square-root sieve gives the signed imbalance
$$
 Z_m=P_m+xA_{\min(m,x)}-xA_m .
$$

There are $B+x(A_m-A_{\min(m,x)})$ available cells through $m$, where $B=\lfloor n^2/13\rfloor$. If every assigned ordinal has been released when its job arrives, counting the jobs through each $m$ gives $Z_m\le B$. Conversely, if this inequality holds at every cut, number the jobs in arrival order and assign each one the cell with the identical ordinal. Its deadline has released that ordinal, and the same numbering works at every later cut. This proves the equivalence between an actual common placement and the excess-only integer test on a fixed board. [Exact splitting of capacity and assignment equivalence](../pal-rh/PALRH/SignedStrip.lean)

Choose $\sigma=1$ for excess or $\sigma=-1$ for deficit. Suppose $\sigma Z_m$ satisfies the bound on every board. The triangular weight $n-d$ can be shortened using only positive coefficients. For $1\le d\le m$ the ratio $(m+1-d)/(n-d)$ is decreasing. Successive differences of these ratios and the last ratio give a positive combination of the measured prefixes. Their sum is $m/(n-1)$. For instance when $n=8,m=3$ the coefficients are $2/21,2/15,1/5$. They turn the weights $7,6,5$ at the three distances into $3,2,1$, preserving the chosen direction of the inequality. [Both orientations of the finite calculation](../pal-rh/PALRH/ReturnedTaper.lean)

On the shortest observed board covering an integer $m$, the root is of order $\sqrt m(1+\log m)^2$. The shortened read, the independently priced tick rounding, and the $O(\sqrt m)$ prime-power correction therefore imply the following. For every $1/2<b<1$ there is a constant $C_b$ such that at every real $t\ge1$,
$$
 \sigma V(t)\le C_b t^b,\qquad
 V(t)=\sum_{d\le t}\Lambda(d)(1-d/t)-t/2 .
$$

The proof first sums the prime weights at integer cuts. Between adjacent integers $V(t)+t/2$ is increasing because each individual von Mangoldt weight is nonnegative. This pays for using real arguments in the next step. [Shortened area, prime powers and interpolation](../pal-rh/PALRH/SignedStrip.lean)

## Where the other direction comes from

Set $V(t)=0$ below 1, and $P(t)=\int_0^t V(u)\,du/u$. In this section $P(t)$ is a logarithmic integral, distinct from the finite number of jobs $P_m$. Pair the values at $t,t/2,t/3,t/4,\ldots$ with alternating signs, ending after all possible nonzero terms. Expanding $\log k=\sum_{d\mid k}\Lambda(d)$ makes this reading an ordinary sum of logarithms and a finite harmonic correction. Pairing the even integer $2i$ with $2i-1$ gives an upper as well as a lower bound. The extra amount on the upper side is at most $\log(t+1)/t$ per pair. The harmonic term matches the linear main term. The resulting alternate reading of $V$ lies between $-12\sqrt t$ and $12\sqrt t$. Integration gives bounds of $\pm24\sqrt t$ for the alternate reading of $P$. [Actual divisor and harmonic sums](../pal-rh/PALRH/PrimeDivisorPrimitive.lean) · [Integrated readings](../pal-rh/PALRH/PrimitiveRecovery.lean)

The signed input makes $H(t)=(C_b/b)t^b-\sigma P(t)$ increasing. For such an $H$, each paired difference in the alternate reading is nonnegative. The first difference $H(t)-H(t/2)$ is bounded above by the full reading, now priced by $O_b(t^b)$. Halve repeatedly. The powers decrease by $2^{-b}$ each time, so the total cost is finite and $|P(t)|\ll_b t^b$. This recovers both sides of the same primitive from the single chosen orientation. [Power-scale recovery](../pal-rh/PALRH/PowerRecovery.lean)

The Mellin transform of the underlying window is $1/[s^2(s+1)]$. The two-sided primitive estimate gives holomorphy of the centered transform on $\Re s>1/2$. Its identity with the zeta logarithmic derivative excludes zeros there and the functional equation supplies the reflection. This last passage uses the routine at the pinned stock zeta definition. The independently fixed bare challenge rejects the same exported conditional term because it still requires the all-board hypothesis. [Analytic transfer](../pal-rh/PALRH/PrimitiveMellin.lean) · [Independent comparisons](../receipt-archives/2026-11-26-pal-signed-pocket.json)

Pang’s PAL and RPL supplied the same-frame return, and his request to turn each directional claim both ways led to the two separate tests. Hearthline derived and formalized the paired upper-log bound, the power-scale recovery, and the direct bridge from each orientation in Pang’s independent construction. [Corpus and source roles](PROVENANCE.md)
