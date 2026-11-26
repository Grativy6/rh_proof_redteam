# A square-root signal that forgets a whole turn

Christopher Daniel Pang and Hearthline · 26 November 2026

Before each retained prime arrives, read the lane where its first tick will land. On a column with $x$ lanes, lane $r$ gives the unit arrow $\exp(2\pi i r/x)$. There are $N$ arriving primes. We proved on paper that the sum of their arrows has size $O(\sqrt N)$ on the prescribed boards. The estimate holds simultaneously at every prefix and after any fixed extra turn per arrival. Over those extra turns, the largest terminal reading has order **exactly $\sqrt N$**. [Proof, classical inputs and ranges](../pal-rh/prime-lane-polynomials.md)

Now add one whole column to the price of every prime. Keep the very same primes in the very same order. **Every fast arrow stays identical**, including the entire polynomial obtained by varying the extra turn. The altered job bill is different. On board 4, the slower cumulative reading first leaves its allowed arc at prime **46,771**. Both versions show lane 25,317 there. The genuine excess is $-1,177,883$ ticks, the altered excess is $50,431,717$, and the allowance is $50,406,400$. [Exact control and measured spectra](../receipt-archives/2026-11-26-pal-lane-phase.json)

There is a way to measure the missing turn. On the slower circle let $x^2$ ticks make one full turn. Subtract the expected $x$ ticks for each distance past the root, and read the residue at every physical cut. The actual change per cut is smaller than the gap between adjacent copies of the allowed arc. Starting at zero, a path that always reads inside that arc has to stay in the original copy. That is a lifting argument you can check without complex analysis. The resulting all-board assertion implies stock Mathlib RH in Lean. [Fixed modular statement](../pal-rh/checks/slow-arc/ArcChallenge.lean) · [Speed and lift of the actual tick stream](../pal-rh/PALRH/SpokeArc.lean)

So we have an unconditional root-scale theorem about the fast signal, an exact alteration it cannot detect, and a slower measurement whose all-board bound remains open. The same off-resonance argument gives an unrounded companion for primorial leading digits, including a power discrepancy estimate. [Primorial consequence](../pal-rh/prime-lane-polynomials.md#the-unrounded-primorial-consequence)

Pang’s recurring question was which distinctions a turn carries when the next frame reads it. His PAL, RPL and APCI work supplied the changed-frame control. Hearthline derived the phase bounds and the slow lift in his independent program. [Source roles](PROVENANCE.md)
