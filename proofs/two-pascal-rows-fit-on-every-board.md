# Two Pascal rows fit on every board

Christopher Daniel Pang and Hearthline · 26 November 2026

Take two marked spots and a two-by-two board of bits. Each of the two row orders can be straight or reversed. Two bits store those orders. Now choose a subset of every size from the two spots. The empty and full subsets are fixed. The one-element subset still has two choices. That takes one bit. Do it a second time, independently, with the fourth bit. **All 16 input records come back from the 16 possible boards.**

This works at every positive size. Give someone $n$ row permutations and **two independent collections of subsets**, each containing one arbitrary subset of each size $0,1,\ldots,n$. All of it fits into $n^2$ cells of $n$ symbols each. At size 3 the encoder takes all 17,496 records through distinct boards and gives every one back. The universal theorem is an ordinary inequality between integers. [Decoder and exhaustive small boards](../receipt-archives/check_pal_pascal_board.py) · [Lean theorem](../pal-rh/PALRH/PascalBoard.lean)

### How many prime digits does that carry?

Take one collection for forward trips and the other for reverse trips. At size 16, the prime distances above the square root are 5, 7, 11 and 13. Each column below gives actual independent base-$p$ digits, in one direction.

| Prime $p$ | Digits the trips require | Digits available at that prime in the subset choices |
| ---: | ---: | ---: |
| 5 | 11 | 9 |
| 7 | 9 | 8 |
| 11 | 5 | 5 |
| 13 | 3 | 9 |

Two five-way digits and one seven-way digit are missing after the same-prime matches. That leaves **175 possible settings**. Six unused 13-way digits alone have more than enough room for them at this size. The encoder can change radix by ordinary division. [Why the individual counts are exact](../pal-rh/what-a-pascal-row-pays-for.md)

There is a specific comparison to pursue at every larger size. Match all the factors the trips and the subset collection have in common. What is still needed and what is still available are then two **coprime integers**. If the available count is at least the needed count at every sufficiently large fourth power, the construction gives RH. This condition is open in our work. Matching only equal prime factors pays **61.64286796… percent** of the large-prime payload in the limit, measured by logarithmic size, in addition to the full row permutations. That is an unconditional part of the construction. [Cofactor calculation and remaining comparison](../pal-rh/what-a-pascal-row-pays-for.md#how-much-the-same-prime-matches-pay)

Can we fix the shortage just by stacking smaller Pascal rows? We tested that too. If every prime must pay in its original radix, the desired pattern would need 3.9 rows of height at least one sixth and about 4.083 rows of height at least one fifth, even if fractional row weights are allowed. Raise a shelf and **more** rows reach it. That is impossible with positive quantities. It pinpoints where this proposed construction needs an exchange or a genuine shared part. [Where five forces a negative row](../pal-rh/what-a-pascal-row-pays-for.md#why-changing-the-sizes-of-positive-rows-cannot-pay-every-prime-in-its-own-radix)

Pang’s PAL and RPL work asks which parts of a source return with their own labels, and what remains after matching them. BLA keeps the remaining demand and the available room on the same board. Hearthline applied those questions to the product of a Pascal row. Lagarias and Mehta studied this product, its factorial representation and prime valuations. Du and Lagarias studied the distribution of its prime factors across the row. The packing theorem and matching calculation here are presented as derivations in Pang’s program. Literature priority for these particular inequalities has not been established. [Original product study](https://arxiv.org/abs/1409.4145) · [Partial factorizations](https://arxiv.org/abs/2006.15439)
