# Why the last two square roots remain

Christopher Daniel Pang and Hearthline, 26 November 2026 (New York).

At 49, start with the mark at 1. Multiply its label by every square you can reach whose root is coprime to six. The roots are **1, 5 and 7**, and the marks sit at **1, 25 and 49**. An exact divisor calculation accounts for 1.37403256… of their three units. Assign that amount in order. The mark at 1 is fully accounted for. About 0.374 of the mark at 25 is accounted for. The rest of 25 and all of 49 remain.

Now start with the negative mark at 5 and raise the head to 245. The same three roots put marks at **5, 125 and 245**. The very same fractions apply, with their original negative sign. The denominator that matters is the head divided by the starting label. Two labels can have matching measurements and still retain separate owners.

**At every head, for every occupied starting label, this calculation leaves at most its last two roots. Sometimes it needs both.** This is a statement about the individual integers in the sum. We can point to them, take their original signs with them, and ask a second question about exactly what remains.

## Which marks are these?

Start with $n=v^2d$, where $v=2^i3^j$, $d$ is squarefree and coprime to six. Its signed weight is $a(n)=v\mu(d)$. Other integers have weight zero. At head $t$, give each such $n$ one copy at $nr^2$ for every $r\le\sqrt{t/n}$ coprime to six. A copy has weight $a(n)$.

Every occupied final integer has exactly one owner. Remove the powers of two and three. In the remaining prime factorization, put half of each exponent, rounded down, into $r$, and its odd remainder into $d$. For example $245=5\cdot7^2$ returns to owner 5. There are no collisions to estimate. Equivalently the filled weight at $v^2u$ is $v(-1)^{\Omega(u)}$ for $(u,6)=1$. The powers of two and three in an occupied integer must both be even.

## How the amount is earned

Let $g(z)$ count the roots coprime to six through $z$. It steps at $1,5,7,11,13,\ldots$. The continuous amount $G(z)$ comes from counting divisors, so its signed sum over all owners can be evaluated exactly. The two functions satisfy

$$
   \frac14 < g(z)-G(z)<\frac53 \qquad(z\ge1).
$$

The short proof uses the alternating gaps 4 and 2. The divisor calculation gives $G(z)=z/3-0.94928618\ldots+O(z^{-2})$. The upper and lower edges of the staircase stay within two thirds of $z/3$. A finite set of endpoints settles the small roots. All the inequalities and the formula for $G$ are in the [derivation](../pal-rh/what-the-last-two-square-roots-carry.md).

There is little room to improve the count by sliding that smooth line. At $6m+1$ the staircase sits $2/3$ above $z/3$. Just before $6m+5$ it sits almost $2/3$ below. Every asymptotically parallel straight line that stays under the staircase must therefore leave at least $4/3$ of a unit in the supremum. A different dilation of the divisor calculation achieves a uniform upper bound of $27/20=1.35$. Even the best possible intercept in this class sometimes needs a second root.

## What a second question can recover

The leftover roots keep their signs. We took an explicitly specified fraction of *those same roots* and worked out its signed contribution. The first and second portions come from disjoint fractions of each mark. Here are the actual totals, with the real-valued portions rounded to the nearest integer.

| Head | Completed signed count | First portion | Second portion | Still unassigned |
| ---: | ---: | ---: | ---: | ---: |
| $10^{12}$ | −191,383,316 | −116,608,576 | −69,266,020 | −5,508,720 |
| $10^{13}$ | −723,457,240 | −459,530,197 | −241,074,887 | −22,852,156 |

At ten trillion the two portions account for 96.84% of the magnitude of the signed count. As the head grows, the first has leading term $-0.30267087\ldots\sqrt t(\log t)^2$. An identified part of its remainder contributes a further $-3.4892967\ldots\sqrt t\log t$ with the slowly growing cutoff in the derivation. These are asymptotics of two members of the partition. An estimate of the second-order term of the *whole* sum would also need the subleading part of the first portion and the rest of the roots. [Reproducible counts and bounds](../receipt-archives/2026-11-26-pal-dense-squares.json)

The missing inequality now has specific inputs. Do the portions still unassigned, added with the signs of their own starting labels, ever exceed the negative amount already accounted for at arbitrarily large heads? An eventual nonpositive total would imply RH. The finite table leaves that question open.

Pang supplied the PAL v2.4 frame question, the RPL old/detail split, and the instruction to try the map both ways. Hearthline developed the square completion, its inverse, the capacity bound and the signed prices within Pang’s constructive program. The arithmetic inputs are prime factorization, Möbius inversion, elementary summation and the stated zeta identities. [Research provenance](PROVENANCE.md) · [Corpus routes](../pal-rh/CORPUS-ROUTES.md)
