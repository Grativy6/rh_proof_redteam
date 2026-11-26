# The first prime a board has to give up

Christopher Daniel Pang and Hearthline · 26 November 2026

Imagine sliding your finger down a cone. At the tip there is one place to point. From inside the walk there is also a direction of arrival. The point alone keeps the answer to “where?” The approach can still matter to the next question. Pang brought this picture to the investigation. The following board gives its two views an exact arithmetic meaning.

At a fixed size $n$, put every row order on the board. Start with all its prime-distance dials. Raise a cutoff one distance at a time, keeping only dials **above** the cutoff. Record the first cutoff where the inputs fit. Call it $d(n)$.

**This single integer answers every fit question for that board.** A cutoff $c$ succeeds exactly when $c\ge d(n)$. Removing further dials only shrinks demand. Removing all the dials always leaves room for the row orders. For genuine prime dials $d(n)$ is either **zero or a prime**. A composite distance could never be the first thing that changes the answer, since there were no dials there to remove. [Proof for any choice of labels](../pal-rh/PALRH/HorizonCut.lean)

Here is a board where the point is visibly nonzero. On the size-256 board with the damaged sieve frame 6,006, settings at distances through 4 can all be discarded and the inputs still overflow. Removing the distance-5 dials produces a fit with **451 whole bits** to spare. Eleven misleading distances, including 25 and 85, still have dials. The first successful cutoff is exactly 5. An undamaged board and this repaired board can therefore answer “fits” while carrying different information. [Original frame change](what-happens-when-the-sieve-forgets-five.md) · [Exact second change](../receipt-archives/2026-11-26-pal-horizon-cut.json)

### A scale for progress toward RH

For the genuine prime board, measure how $d(n)$ grows through the fourth powers. **An eventual bound $d(n)\le n^{3/4}$ at those sizes is equivalent to excluding nontrivial zeta zeros strictly to the right of $3/4$.** The same statement holds with any fixed exponent from $1/2$ up to 1, excluding 1. At $1/2$ it gives RH. The established cutoff $3n/(\text{binary length of }n)^3$, rounded up, funds records at every size. It saves a growing logarithmic factor and still has growth exponent one. A fixed power saving would change the complex region the construction can exclude. [Proof of the entire scale](../pal-rh/what-the-least-cut-measures.md)

### Make a board that really does fail, repeatedly

There is a second test with the arithmetic fluctuations exposed. In the factorial sieve, lower the square-root cutoff just far enough to admit some products of two nearby primes. The amount to move is determined by **counting integer pairs**, with no zero table. At that setting, the resulting records genuinely fit at infinitely many fourth powers and overflow at infinitely many others. At roots 16, 20 and 24 the observed answers are overflow, fit and overflow.

The goal on this board is to bound the **size** of an overflow. A total overflow allowance of $n^{3/2}/70$ bits is insufficient at infinitely many fourth powers. An eventual allowance of $2n^{3/2}/15$ bits for overflow is equivalent to RH. Thus this version can preserve a real fluctuation and still test the same proposition. [Where the two prime directions meet, and the exact integer condition](../pal-rh/when-two-prime-directions-meet.md)

Pang supplied the point and horizon question, PAL’s scope and return rule, RPL’s retained detail, and the question of which distinctions must survive together. Hearthline derived these board results in his research program. The analytic inputs include the prime number theorem in short intervals, the integrated explicit formula, and the completed-zeta product. The global bounds equivalent to RH remain open in this program. [Corpus and derivation credits](PROVENANCE.md)
