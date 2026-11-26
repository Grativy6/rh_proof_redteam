# One integer comparison to the Riemann hypothesis

Christopher Daniel Pang and Hearthline · 26 November 2026

Take a row of $n=k^4$ spots. Ask how many independent **forward** trip settings it carries. A distance $m\ge2$ gets a dial if it shares no divisor with $(k^2)!$ except 1. There are $n-m$ forward trips of length $m$, and each dial has $m$ positions. Call the total number of settings $R$.

Now pick one subset of the $n$ spots of each possible size. A three-element subset can be picked independently of a four-element subset. Call the total number of such collections $P$.

**The one remaining claim is that $R\le P$ at every sufficiently large fourth power.** If that holds, the stock Mathlib proposition `RiemannHypothesis` follows. The Lean theorem now takes this one eventual comparison as its entire mathematical premise. The comparison itself remains open in our construction. [Independently fixed statement](../pal-rh/checks/one-subset/OneSubsetChallenge.lean) · [Proof of the implication](../pal-rh/PALRH/OneSidedBoard.lean)

In symbols, write
$$
 R=\prod_{\substack{2\le m\le n\\\gcd(m,(k^2)!)=1}}m^{n-m},
 \qquad P=\prod_{a=0}^n\binom{n}{a}.
$$
The gcd test selects exactly the primes above $\sqrt n$. The two directions of travel use independent copies of the same subset resource. Both copies and all $n$ row permutations already fit on the board at **every** size. [Sieve and two readings of five](what-happens-when-the-sieve-forgets-five.md) · [Construction and decoder](two-pascal-rows-fit-on-every-board.md)

### Try it at sixteen

Here the recognizing number is $4!=24$, and the retained distances are 5, 7, 11 and 13. Thus $R=5^{11}7^9 11^5 13^3$. Cancel the factors $R$ and $P$ have in common. On the trip side **175** settings remain. On the subset side **1,980,876,636,356,482,204,434,432** remain. The open comparison has a definite direction and can be checked with integer multiplication at any proposed size. The size-16 result says exactly what has been paid for at that size.

### Where did the second assumption go?

Previously the Lean condition also put an upper limit on unused space. For this direction of proof, an upper bound on demand supplies an upper bound on a sum of prime weights. The problem was obtaining enough information about the other direction.

Keep the running total of that prime signal. At a scale $x$, read it at $x,x/2,x/3,x/4,\ldots$ with alternating signs. The finite divisor identity prices that reading using ordinary integers. The one upper bound makes a related running total increase with its argument. Then the difference between its first two readings, at $x$ and $x/2$, can be no greater than the whole paired sum, because every following pair contributes a nonnegative amount. Repeat on $x/2,x/4,\ldots$. The costs decrease by the square root of two each time and have a finite sum. This earns a bound in both directions on the running total. Its transform reaches the ordinary zeta function, where an off-line zero would produce a pole. [All steps, with the finite cost of an octave](../pal-rh/how-one-sided-prime-area-reaches-rh.md)

The same exported term passed the one-premise challenge. Submitted against the independently pinned bare RH statement, it was rejected because the statements differ. The extra premise is visible in the mathematics and in the theorem type. [Both comparisons](../receipt-archives/2026-11-26-pal-one-subset.json)

This route grew from Pang’s PAL v2.4 retained distinctions, RPL’s separation of a carried part from the remaining detail, BLA’s comparison of costs in one frame, and his point-and-horizon question. Hearthline derived the prime-board construction and one-sided transfer in his program. The count, its remaining premise, the finite arithmetic replay and the scope of both comparisons are public. [Source record](PROVENANCE.md) · [Reproduction](../receipt-archives/2026-11-26-pal-one-subset.json)
