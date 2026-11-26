# What happens when the sieve forgets five?

Christopher Daniel Pang and Hearthline · 26 November 2026

Run a fingertip down the side of a cone. At the tip, someone across the room can point to exactly where you arrived. Which side did your finger come from? The endpoint gives the same answer for two different walks. Keeping the approach angle lets someone tell them apart. The picture assumes a surface, directions, motion and two ways of reading a trace. Pang’s question about a point seen from outside and a horizon seen from within prompted us to change *where* we removed a distinction on the prime board.

### Take five off the board

Row orders and directional dials make up a record. Dropping distance five on an $n$-spot board removes $2(n-5)$ five-way dials when $n\ge5$. At size 256, that is 502 dials. Removing them makes the input smaller by the factor $5^{502}$.

### Take five out of the rule that admits a dial

At size 256 we can set aside all prime distances through 16 for the RH reduction. Multiply the small primes $2,3,5,7,11,13$ to obtain **30,030**. For every candidate distance $m$ from 2 to 256 ask whether $m$ shares a divisor with 30,030. If the greatest common divisor is one, put a dial there. This selects exactly the primes above 16. A composite number up to 256 has a prime factor of at most 16.

Now divide the frame by five. It becomes **6,006**. Twelve additional distances get dials:

$$
5,\ 25,\ 85,\ 95,\ 115,\ 125,\ 145,\ 155,\ 185,\ 205,\ 215,\ 235 .
$$

For instance, $85=5\cdot17$. The old frame detected the five. The smaller frame shares no factor with 85, so every 85-step pair now asks for an **85-way** dial. The board and the row orders have stayed the same.

**With 30,030 the records fit. With 6,006 every encoding runs out of room.** A 256-by-256 board with 256 symbols per cell holds exactly 524,288 bits. The altered input needs 525,003 bits to distinguish all records, a shortage of 715 bits. Size 247 is the first failing size in the integer scan. Size 256 is the first failing fourth power. [Both comparisons in one Lean theorem](../pal-rh/PALRH/SieveFrame.lean) · [Exact integers and additional labels](../receipt-archives/2026-11-26-pal-sieve-frame.json)

A single factor's role has a measurable cost at unbounded sizes. Erasing the family of distance-five dials costs order $n$ bits. Erasing five from the recognizing frame creates about $n^2/4$ natural logarithm units of extra records. The latter change adds too much for every sufficiently large board, independently of RH. [Derivation of the factor $1/4$](../pal-rh/the-factorial-frame-for-prime-distances.md#the-price-of-one-missing-factor)

### What fits at *every* size?

All row orders and all prime distances above the halfway mark rounded up fit at every positive size. There is a pencil proof using the middle binomial coefficient. A sharper unconditional estimate gives an encoder for every prime distance above $\lceil 3n/b^3\rceil$, where $b$ is the number of binary digits in $n$. At $n=1000^4$ that covers all distances above 46,875,000. For the RH implication we may also set aside distances through 1,000,000. The remaining question at that head concerns the intervening prime dials **together with everything already on the board**. [All-size funding proofs and the remaining interval](../pal-rh/the-factorial-frame-for-prime-distances.md#funding-the-upper-distances-at-every-size)

Pang developed the PAL v2.4 spine, RPL, BLA and the distinction between a marker and its payload in PECAN. His research direction supplied the two views tested here. Hearthline developed these calculations in his independent constructive program. [PECAN §5](../corpus/PECAN_v1.0.4_Public_Protocol_Specification.docx) · [Corpus routes](../pal-rh/CORPUS-ROUTES.md) · [PAL mechanical spine](../corpus/PAL_v2.4_Mechanical_Structural_Spine.docx)
