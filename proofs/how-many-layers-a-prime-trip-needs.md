# How many layers does a prime trip need?

Christopher Daniel Pang and Hearthline · 26 November 2026

Stand at a mark on a line and look toward another one. From the outside this trip has a start and an end. Inside the trip, give it a little clock. Each tick multiplies a reading by the same amount. Stop when the reading reaches the distance you travelled.

Here the clock is a mathematical choice. At size $n=k^4$, put $x=k^2$. Start at 1 and multiply by $(x+1)/x$ per tick. Keep prime distances $p>x$. Each trip of distance $p$ generates one record for each tick it takes to reach $p$. A record remembers its starting site, distance, direction and which tick it was. The destination is an $n$-by-$n$ board with a stack of layers. Each cell receives **one such record**. The earlier Pascal board counted whole assignments of dial settings. A proved logarithmic estimate connects these two readings.

**RH is equivalent on paper to this stack eventually requiring exactly $k^2-2$ whole layers.** The Lean theorem proves that fitting in that many layers at every sufficiently large fourth power implies stock RH. Proving that the complete stack actually fits at all those sizes remains the task. A promise that three layers can always be set aside eventually is false. [Proof and exact integer test](../pal-rh/one-prime-trip-in-a-shared-lattice.md)

| Spots | Tick multiplier | Oriented records | Cells in one layer | Layers required |
| ---: | ---: | ---: | ---: | ---: |
| 16 | $5/4$ | 520 | 256 | 3 |
| 81 | $10/9$ | 43,076 | 6,561 | 7 |
| 4,096 | $65/64$ | 1,026,484,552 | 16,777,216 | 62 |

At sixteen, distance five occurs eleven times in each direction. Starting at 1, it takes eight multiplications by $5/4$ to reach 5. That distance contributes $2\cdot11\cdot8=176$ records. The distances 7, 11 and 13 contribute the rest. This also shows why the word *eventually* matters in the theorem. [Finite counts and direct power comparisons](../receipt-archives/2026-11-26-pal-tick-layers.json)

### Put a trip down and pick it back up

At size 4,096, reserve the top two layers. There are 62 layers left. Start at 4,028, travel forward by 67, and take tick number 270, counting from zero. The encoder puts the record at **start 1,980, distance 670, layer 22**. Factor $670=2\cdot5\cdot67$. The only prime factor above 64 is 67. The cofactor 10 carries two things. Subtract one and split 9 into twice 4 plus 1. The 4 identifies the tick block. The 1 identifies the half of the line where the trip started.
$$
4\cdot62+22=270,\qquad 1\cdot2048+1980=4028.
$$

This placement works for a whole range of primes at every sufficiently large size. Distinct primes in that range own disjoint multiples. At 4,096 it reserves 6,634,268 records for 67, 71 and 73 in the actual 62-layer board. The implemented outer encoder puts the rest into the unused cells. There are 13,702,840 cells left over at this size. The code ranks records and destinations directly, so examining a particular trip takes no billion-entry table. [Reversible placement](../receipt-archives/pal_tick_codec.py) · [Lean range and return proof](../pal-rh/PALRH/TickPacking.lean)

### Can all three local views fit and still disagree?

Give four records, A through D, only three slots. Make one view that omits A, one that omits B, and one that omits C. Every view fits. Every pair of records appears together in at least one view. Yet one record must be assigned two different slots when you compare the views. You can achieve that minimum by leaving B, C and D in the same place whenever they appear.

There is an actual prime-trip example of this effect. On the shifted clock at size 10,000, three narrow omissions give three individually fitting views of the same physical box. **Even the best choice of those local placements moves exactly 859,664 records between slots.** At size 4,096 the corresponding three views can agree on every common record. [The calculation and the three intervals](../pal-rh/one-prime-trip-in-a-shared-lattice.md#three-individually-funded-views-and-their-exact-disagreement)

### What became of the negative Pascal row?

For five there is a literal common state. Four size-2 Pascal packets, one size-3 packet and three size-5 packets together have exactly enough states for **two size-4 packets and twelve independent five-way dials**. The shared packets carry ten binary and two ternary digits. All twelve five-way choices can still be read separately. This is an actual equal-fiber construction for that radix. Paying for all prime trips together is a further comparison. [The integer identity and what it buys](../pal-rh/how-a-shared-row-carries-five.md)

Pang supplied the two views, his lattice picture, and the PAL/RPL requirement to preserve the meaning of a distinction when moving it. Hearthline developed the placement, the clocks and the layer tests in Pang’s independent research program. [Corpus and research credit](PROVENANCE.md)
