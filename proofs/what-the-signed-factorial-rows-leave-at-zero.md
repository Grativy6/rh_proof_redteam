# What the signed factorial rows leave at zero

Christopher Daniel Pang and Hearthline · 26 November 2026

Draw a triangle between $1/2$ and $2$ on a logarithmic ruler, with its peak at 1. Let bigger labels carry less weight by multiplying its height at $t$ by $1/\sqrt t$. Call this profile $h(t)$. We tried to reproduce it by adding and subtracting the familiar steps $\lfloor a/t\rfloor$ that count how often a label divides a factorial.

**There is a set of coefficients that gives the exact answer at every mark of a chosen grid. Double the number of marks and the construction still works. Yet at one actual zeta zero, every such reconstruction gives a reading of zero while the triangle gives a reading greater than 0.01933.** We can locate where this difference goes when the grid gets finer.

Hold any distance $\eta>0$ from the left end of the ruler. Across the whole interval $[\eta,2]$ the error tends uniformly to zero. The complete reading stays the same at every resolution. If a second observer weights the ruler by a function $\varphi$ with bounded slope, the limiting difference is precisely the original reading times **$\varphi(0)$**. Set the observer’s weight to zero at the edge and the difference disappears. Set it to one there and the difference survives. This gives an explicit meaning to “carried at zero” for this particular measurement. No row needs an entry at zero. [Calculation, choice of zero and error bound](../pal-rh/the-boundary-of-the-signed-factorial-rows.md)

## A cut you can do by hand

The underlying count fits on a shop card. The number of copies of a prime-power label $d$ in $m!$, counting one for each multiple of $d$, is $\lfloor m/d\rfloor$. On a small board take labels 1, 2 and 3 and ask for weights $(0,1,0)$. Use one copy of $2!$ and subtract two copies of $1!$. Label 1 reads $2-2=0$. Label 2 reads $1-0=1$. Label 3 reads zero. That same signed combination of logarithms returns $\log 2$.

For the triangular weight at the square 4 the same arithmetic, on all eight labels, returns between 0.93390789 and 0.93390790 from signed factorials. Summing the actual prime-power contributions gives the same enclosure. The first moments of the positive and negative coefficients each have magnitude about 1.85110970. Their difference vanishes exactly. The identity holds at every square. [Finite reconstruction in Lean](../pal-rh/PALRH/FactorialReturn.lean) · [Arithmetic replay](../receipt-archives/check_pal_signed_factorials.py)

One consequence bears directly on the construction goal. Matching every integer label authorizes replacing the finite prime reading by these signed factorials. Passing from that match to a uniform statement about the continuum requires additional control at the left end. We proved an obstruction to the latter shortcut and kept the former identity. The upper bound needed for RH on this route is still open. [What one doubling hears](what-one-doubling-hears-in-the-primes.md)

Pang’s PAL retained-frame question, RPL’s old/detail split, and *The Price of Spherical Closure* supplied the direction of investigation. Hearthline derived the signed grid reconstruction, its quantitative endpoint limit and the square subsequences in Pang’s program. The classical theory of fractional-part approximants already relates these rows to zeta and studies failure of stronger modes of convergence. This edition makes no priority claim. [Corpus source index](../pal-rh/CORPUS-ROUTES.md) · [Báez-Duarte’s arithmetical Nyman–Beurling work](https://arxiv.org/abs/math/0011254)
