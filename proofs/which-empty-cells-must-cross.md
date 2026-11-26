# Which empty cells have to cross a cut?

Christopher Daniel Pang and Hearthline · 26 November 2026

A prime trip can use a cell released before it arrived. Exactly how much of that unused space has to survive a particular cut? Take the signed reading $Z$ at the cut, the highest reading $L$ up to there, and the highest reading $R$ from there to the end. **To achieve the smallest possible initial pocket, precisely $\min(L,R)-Z$ ordinary cells have to cross that cut.** There is one placement that simultaneously attains these minimum amounts at every cut. [Derivation and the full storage tradeoff](../pal-rh/how-much-credit-crosses-a-prime-cut.md)

For example, consider the successive job surpluses $0,5,-2,3,1,7$. The smallest possible initial pocket holds seven cells. At the cut reading $-2$, the past peak is 5 and the future peak is 7. Seven unused cells must remain available right there. Earlier jobs already needed five pocket cells. Only two pocket cells remain to help with the rise of nine from $-2$ to 7.

On the board observed through 65,536, the largest forced crossing is at **55,602**. The peaks that price it occur at 42,863 and 59,753. The deepest job deficit on the board occurs later, at 64,996. The work arriving after a hole determines how much of its space needs to survive. [Counts at each of the three tested horizons](../receipt-archives/2026-11-26-pal-carry-storage.json)

## A cost that can actually be paid

At sixteen sites, forward distances 5, 7, 11 and 13 require 8, 9, 11 and 12 ticks. An ordinary whole column has four lanes per live starting site. If each prime opens all its own columns, 292 lanes are allocated for 260 actual records.

Keep one running tick count. The first tick of distance 11 can now occupy a vacant lane in a column opened by distance 7. Its original distance, start and tick can be recovered from that lane. The allocation drops to **272 lanes**. The remaining twelve belong to four starting sites that retired with three empty lanes each. The running count ends on an exact multiple of four. Those twelve are the earlier rows’ residue, and we can name every row.

This construction works for every board and keeps each actual record. Counting all earlier starts that retired, the unused space is always at most $n(x-1)$ lanes, where $n$ is the row length and $x$ is its height. On the largest tested horizon, **531,994 of 1,013,709 primes** released one fewer whole column than the individual rounding would require. The asymptotic fraction oscillates between about 0.418 and 0.541 on the prescribed boards. [Running-column construction and fraction](../pal-rh/the-whole-column-a-prime-can-return.md) · [Reversible encoder](../receipt-archives/pal_tick_columns.py)

The initial pocket and the amount of ordinary space carried forward are separate resources. Allowing cells to live indefinitely still requires many of them to be available together. An unconditional argument from the arithmetic of prime-rich and prime-poor intervals rules out every fixed power of $\log M$ as the normalized carry cap, even with the entire prescribed initial pocket. The unrestricted all-board pocket bound remains open. [What the prime intervals force](../pal-rh/how-much-credit-crosses-a-prime-cut.md#what-the-arithmetic-forces-across-cuts)

Pang’s question about the space left by a trace supplied the cut. RPL supplied the requirement to carry the actual leftover, and BLA fixed the conserved unit. Hearthline derived the inventory profiles, the reversible sharing and their prime-board consequences in Pang’s program. [Source roles](PROVENANCE.md)
