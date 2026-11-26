# How much room does the prime board need?

Christopher Daniel Pang and Hearthline · 26 November 2026

Put three marks in a row, numbered 0, 1 and 2. Give each mark a list of the three marks in any order. Now look at who can reach whom by a **prime distance**. From 0 to 2 the distance is 2. The return trip also counts. Give each trip its own dial with two positions, including zero.

There are $6^3\cdot2^2=864$ possible records. Hand someone a three-by-three board with three symbols per cell. Can they store the record and give it all back? Here is one trip through the encoder. Rows list the three permutations. Dials appear in row-major order.

| What went in | Board, read one row at a time | What came back |
| --- | --- | --- |
| 201, 012, 120 and dials 0, 1 | 012 / 001 / 000 | 201, 012, 120 and dials 0, 1 |

Both dial readings travel. The place reserved for a dial lets zero be an ordinary setting. The program goes through all 864 records and recovers each one from a distinct board. [Encoder and decoder](../receipt-archives/check_pal_prime_board.py)

## Change the size

At size $n$ each of $n$ rows can take $n!$ orders. Every prime distance $p<n$ occurs $2(n-p)$ times, each with $p$ settings. The records and available boards therefore number

$$
N_n=(n!)^n\prod_{p\le n}p^{2(n-p)}, \qquad B_n=n^{\,n^2}.
$$

**The assertion that every record fits, at every positive size, is equivalent to the Riemann hypothesis.** An injection at a fixed size exists exactly when $N_n\le B_n$. The outstanding research question is how to prove the inequality for arbitrary $n$. An encoder can expose a shortage in a particular arrangement even when the board as a whole has ample room. [Proof in both directions](../pal-rh/the-prime-board-and-its-signed-area.md)

## Where does the first arrangement break?

Give every prime dial its own cell. A base-$n$ cell used for a base-$p$ dial can carry another digit in $\lfloor n/p\rfloor$ positions. The rest are unusable for this arrangement because every extra digit must accommodate *every* setting of the dial. Pool the remaining capacities and use them for the row orders. Size **4,243** is the first failure. The missing capacity amounts to just over 523 bits, so 524 extra binary places suffice. The whole board still has over 448,387 natural logarithm units of spare capacity.

Let each dial borrow one other cell. A pair of cells has $n^2$ states. Put dial $d$ and extra digit $r$ into the integer $pr+d$. Split that integer into two base-$n$ digits. To read it back, reassemble the integer and divide by $p$. The quotient recovers $r$ and the remainder recovers $d$.

| Board size | Entire board | Single-cell arrangement | Two-cell arrangement |
| ---: | ---: | ---: | ---: |
| 2,663 | +226,501.059 | +49,039.053 | +226,437.808 |
| 4,243 | +448,387.560 | −362.619 | +448,297.320 |

Entries give the logarithm of capacity divided by demand, rounded to three decimals. A negative entry forces two inputs to compete for a place. Prime distances occupy at most half the cells, so every dial can borrow a distinct cell. The total cost of rounding all the two-cell capacities is at most $n$ in these units. At 4,243 the actual cost is about 90.24. The reconstruction is explicit. The inequality that would fund it at *every* size remains open here. [Exact products, bounds and first failure](../receipt-archives/2026-11-26-pal-prime-board.json)

Pang’s PAL v2.4 spine supplied the question of what a retained place lets its next reader recover. His RPL and BLA supplied the questions about the remaining digit and the cost of changing where the count is taken. Pang’s calculator-inside-a-board example prompted this finite storage construction. Hearthline developed the counts, the encoders and the deductions for his research program. The analytic connection uses Daniel R. Johnston’s theorem on the integrated prime-counting error. Research priority for the board reformulation has not been established. [Corpus routes](../pal-rh/CORPUS-ROUTES.md) · [Johnston, Theorem 1.2](https://arxiv.org/pdf/2201.06184)
