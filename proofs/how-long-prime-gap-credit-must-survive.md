# How long must a prime gap’s unused space survive?

Christopher Daniel Pang and Hearthline · 26 November 2026

Give a prime the space released since the preceding prime. Let it spend what it needs and discard the leftover. Can nearby primes share just enough of this space to make the one-thirteenth construction work?

**On the board observed through 1,048,576, groups of 245 consecutive prime arrivals are too short if each job needs a cell on arrival. Groups of 246 suffice.** We optimized over every way of choosing the group boundaries. If the entire group can use its future cells immediately, the exact transition moves from 63 to 64. Both experiments have the same initial pocket and the same actual jobs. [Integer costs and optimal partitions](../receipt-archives/2026-11-26-pal-expiring-gaps.json)

Try ten arrivals, each costing 23 cells. Every whole distance column releases 10. Three gaps are three columns wide and seven are two columns wide. Exactly 230 jobs arrive and 230 cells open. Give the three wide gaps first and they leave 21 spare cells, exactly enough for the seven short gaps. Let the spare cells expire at each gap and the same ten arrivals need 21 outside cells. Reverse the order and even the shared pool needs those 21 up front. The total stays fixed. The ability to use it changes.

| Observed distances through | Prime arrivals | Smallest maximum group when future cells within the group are available | Smallest maximum group when jobs must be filed on arrival |
|---:|---:|---:|---:|
| 65,536 | 3,724 | 8 | 21 |
| 1,048,576 | 68,394 | 64 | 246 |

The starting pocket is $\lfloor n^2/13\rfloor$ cells on the prescribed board. Groups contain consecutive primes. A group receives the distance columns since the end of the preceding group. Unused group cells expire when the group ends. All draws on the pocket pay for distinct jobs. A fixed-address variant already fails on the first active board after 215 primes. If each non-pocket destination must be a multiple of its owner and available by that owner’s arrival, its only eligible positive distance is the prime itself. [Original arrivals and the pocket](one-thirteenth-of-a-returned-layer.md) · [Group rules and direct arithmetic](../pal-rh/why-expiring-gap-credit-fails.md)

## Why the required range grows

A prime’s tick cost, divided by the height, is close to $\log p$. A group of $s$ nearby primes consequently asks for about $s\log p$ columns’ worth of space. The distance spanned by the group is a **whole number** of columns.

There are intervals of prime sizes where $s\log p$ stays away from every integer for every permitted group length $s$. Choosing the boundaries after seeing all the primes cannot remove that separation. Summed across many groups, the positive and negative differences nearly balance globally. Expiring the unused space makes the positive differences separately chargeable. The total charge then exceeds the pocket.

We proved this on every sufficiently late board for every fixed cap on group size. It even holds for every cap that grows as a fixed power of the logarithm of the observed distance. The detailed proof gives a larger explicit growth rate and uses an unconditional prime number estimate. It applies to the stated rule for expiring local cells. The shared-pool all-board inequality remains open. [Proof, exact growth rate and scope](../pal-rh/why-expiring-gap-credit-fails.md)

Pang’s PAL and RPL question about carrying the unresolved part into the next frame led directly to this experiment. Hearthline derived the phase interval, growth obstruction and exact finite optimization in his program. [Corpus source roles](PROVENANCE.md)
