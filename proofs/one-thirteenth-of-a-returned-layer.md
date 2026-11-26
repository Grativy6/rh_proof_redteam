# One thirteenth of a returned layer

Christopher Daniel Pang and Hearthline · 26 November 2026

**Keep the part the sieve removed. On a fixed sequence of boards, RH is equivalent to a single integer test on each board.** Every prefix of its corrected prime-trip count must agree with its flat reference to within one thirteenth of a layer. The size of the board, the return, the reference height and the allowance are all prescribed. The test starts at board zero. One counterexample at any size would violate a mathematical consequence of RH. [Complete proof in both directions](../pal-rh/why-one-thirteenth-is-enough.md)

## What to count

Choose $j=0,1,2,\ldots$. The last distance to inspect is $M=16^j$. Set $x=4^{j+1}(j+1)^2$ and make the board $n=x^2$ sites long. A whole layer has $n^2$ cells.

1. A distance $d$ gets ticks if $d\ge2$ and $\gcd(d,x!)=1$. One tick is one multiplication by $(x+1)/x$. Stop as soon as the product reaches $d$. Each of the $n-d$ forward trips of that distance gets that many ticks.
2. At a cut $m\le M$, let $P_m$ count all such forward ticks through distance $m$. The flat strip through that cut has $A_m=\sum_{d=1}^{m}(n-d)$ positions per unit height. Compare with $xA_m$.
3. **Carry $xA_{\min(m,x)}$ forward.** The sieve excluded every distance through $x$. This entry is the flat strip removed at precisely those distances. Put it back alongside the actual tick count. Take the largest absolute difference over the cuts.

The single question at board $j$ is whether

$$
 13\max_{0\le m\le M}\left|P_m+xA_{\min(m,x)}-xA_m\right|\le n^2 .
$$

Through the square root the answer is exact to the cell. The first four boards lie wholly inside that range. Leaving the return out would fail the proposed allowance at the square-root cut on every board from $j=3$ onward. It fails by a simple count of the missing positions. [Lean proof of the missing-strip obstruction](../pal-rh/PALRH/ReturnedHorizon.lean)

## Why thirteen appears

The classical RH bound on the accumulated prime weight contains $1/(8\pi)$. Our board grows by a factor of sixteen in the observed distance. Converting that bound to layers gives $(\log 2)^2/(2\pi)=0.07646647\ldots$. One thirteenth is $0.07692307\ldots$. A calculation covering the root, the clock rounding and every early board keeps the reading inside that allowance. This is a sufficient choice. The proof leaves the optimal denominator undetermined. [All constants](../pal-rh/why-one-thirteenth-is-enough.md#why-the-number-thirteen-works) · [Schoenfeld’s equation (6.3)](https://electronicsandbooks.com/edt/manual/Magazine/M/Mathematics%20of%20Computation/1960-2002/pdf/1976_v030_n134/2005976.pdf)

The other direction starts with the measured integers. Undo the taper $n-d$, turn the remaining ticks into their measured prime weights, and use the overlapping prefix lengths to recover the square-root error bound for the ordinary prime-counting signal. Its transform excludes an off-line zero. The Lean theorem proves this implication for stock Mathlib RH. **Our open step is to pay that fixed inequality for every board independently of RH.** [Independent statement](../pal-rh/checks/returned-horizon/ReturnedChallenge.lean) · [Proof of the implication](../pal-rh/PALRH/ReturnedHorizon.lean)

There is also a one-sided construction on paper. Start with a pocket of cells, then release the ordinary strip a distance at a time. If each arriving job can use a cell already released, a pocket of one thirteenth of a layer on every board suffices. On three tested horizons, the deepest shortfall stayed at exactly the same distance when we changed the board size. At the largest it was 16,576,186, just before a prime. A wider prime gap occurred elsewhere. [The pocket and the three readings](../pal-rh/why-one-thirteenth-is-enough.md#either-sign-alone-and-the-least-initial-buffer)

The arithmetic replay counts the actual jumps through $j=6$. A published finite prime estimate combined with the paper argument covers all boards through $j=21$. Each range has its source and method. Pang’s PAL v2.4 supplied the ordered distinction, RPL the instruction to carry the residue, and BLA the requirement to compare prices in one frame. Hearthline derived the returned strip, the board sequence and both implications within Pang’s independent program. [Ranges and source roles](../pal-rh/why-one-thirteenth-is-enough.md#the-range-already-covered) · [Exact finite readings](../receipt-archives/2026-11-26-pal-returned-horizon.json)
