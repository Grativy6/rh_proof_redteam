# How far does a prime trip have to move?

Christopher Daniel Pang and Hearthline · 26 November 2026

Take sixteen sites in a row. Put one cell above each ordered pair of sites, then stack three such layers. A cell has a distance you can read by subtracting its two site numbers. A trip starts with its own prime distance. We want to store each trip and tick in a distinct cell, and see how far its distance reading has to change. [How a trip makes ticks](how-many-layers-a-prime-trip-needs.md)

**Two columns of travel are too few.** The distance 11 has five forward trips and eleven ticks. The distance 13 has three forward trips and twelve ticks. Including both directions gives $2(5\cdot11+3\cdot12)=182$ records. If these distances can change by at most two, every one must land in columns 9 through 15. Those columns contain $2\cdot3(7+6+5+4+3+2+1)=168$ cells. Fourteen records have nowhere to go. Three columns suffice for the entire board. This shortage rules out every rearrangement at radius two. [Exact interval argument and assignments](../pal-rh/how-prime-trips-change-distance.md)

## What the locating mark costs

Pang asked what a prime would have to carry so it could be recognized in the next frame. Our earlier placement put each middle prime into a distance divisible by that prime. Factoring the destination recovers its owner. Another decoder orders all jobs and cells by distance and recovers the original prime from the rank. We measured the least possible outer travel with the middle addresses fixed, then allowed every job to use the rank decoder. Both experiments use exactly the minimum whole number of layers for the same board.

| Sites | Layers | All jobs use rank | Middle prime stays readable as a divisor |
|---:|---:|---:|---:|
| 16 | 3 | 3 | 3 |
| 20,736 | 142 | 134 | 272 |
| 65,536 | 254 | 265 | 814 |
| 1,048,576 | 1,022 | 1,038 | 11,481 |
| 5,308,416 | 2,302 | 2,258 | 54,375 |

The two last columns measure distance in columns of the board. In the last column only the outer trips enter the travel maximum. On the million-site board, trying 11,480 leaves an interval short by 17,580,098 **available cells**, after subtracting those already occupied. The reason persists as the boards grow. The middle jobs reserve multiples of their own primes farther out, leaving low-distance cells that only an outer job can come back to fill. We derive both the limiting travel cost and where that travel occurs. [Proof for fixed addresses](../pal-rh/what-a-multiple-address-costs.md) · [Assignments and shortage counts](../receipt-archives/2026-11-26-pal-local-distance.json)

## What the readings would have to earn

Let each board choose its own minimum height. Put all its real jobs into that box, with a return address for each one. **If one constant pays for travel of at most $B\sqrt n(j+1)^2$ on each board $n=16^{j+1}$, the ordinary Riemann hypothesis follows.** The definition of the packing uses counting, integer powers and gcd. The direction from RH to such a placement has a separate paper proof using Schoenfeld’s bound on the actual prime weights. Our outstanding step is the all-board travel bound. [Independently stated condition](../pal-rh/checks/local-distance/DistanceChallenge.lean) · [Derivation and unconditional range](../pal-rh/how-prime-trips-change-distance.md)

There is a way to see an overconfident version fail without constructing the full placement. At a cut $m$, count all the forward jobs up to distance $m$. Compare that count with one ordinary triangular strip filled to a freely chosen integer height $h$. Could one flat height track *every* cut within a single board area $n^2$? At $n=16{,}777{,}216$, cut 5,380 requires $h\le4{,}046$. Cut 1,021,387 requires $h\ge4{,}060$. The best height across every cut is 4,060, and even it misses by more than one board area. Carry the area of the missing small-distance strip explicitly. That reduces the worst miss to less than one third of a board area at this size. At the very next board the miss rises above one third. [The two divisions, the optimum and its witnesses](../pal-rh/how-prime-trips-change-distance.md#two-integer-divisions-rule-out-one-board-area)

Pang’s PAL v2.4 led with the ordered record of distinctions. RPL and PECAN supplied the question of which part of a record travels and how to recover its owner. BLA prompted the comparison in one physical frame. Hearthline developed the placements, bounds and counterexamples with Pang in this independent program. [Corpus and source roles](PROVENANCE.md)
