# Two arrows and a mirror

Christopher Daniel Pang and Hearthline · 26 November 2026

Chris asked what law a fictional world could have that would make its own critical line earnable from the inside. Start with two arrows, draw the second from the tip of the first, and ask when the trip brings you home.

Here is the entire rule. At $s=\sigma+it$ put
$$
 F(s)=2^{-s}+2^{s-1}.
$$
The first arrow has length $2^{-\sigma}$ and angle $-t\log2$. The second has length $2^{\sigma-1}$ and angle $+t\log2$. Moving sideways changes their lengths in opposite directions. Moving upward turns them in opposite directions. Reflection $s\mapsto1-s$ just exchanges them.

To come home, two arrows must point opposite ways and have equal lengths. Equality of lengths requires $-\sigma=\sigma-1$, hence $\sigma=1/2$. The angle difference must be an odd multiple of $\pi$. This gives all the zeros explicitly,
$$
 s=\frac12+\frac{(2m+1)\pi}{2\log2}\,i,\qquad m\in\mathbb Z .
$$
At the first one both arrows have length $1/\sqrt2$. One points straight down and the other straight up. Those are the two marks you can draw on paper to teach the rule.

## Turn the screw the other way

Add a fixed left-pointing arrow of length $a\ge0$. The new rule is $F_a(s)=2^{-s}+2^{s-1}-a$. Reflection still exchanges the two moving arrows and leaves the third alone. Set $z=2^{s-1/2}$. The zero equation becomes
$$
 z^2-\sqrt2\,a z+1=0 .
$$
For $0\le a<\sqrt2$ the roots are complex conjugates whose product is 1. Both have modulus 1, so every zero again has $\sigma=1/2$. At $a=\sqrt2$ they meet at $z=1$. For $a>\sqrt2$ there are two distinct positive reciprocal roots. Their moduli now put the zeros on opposite sides of the line.

The split can be seen with fractions. Take $a=17/12$ and write $x=2^s$. The equation becomes $(3x-4)(2x-3)=0$. Two real zeros are $s=\log_2(4/3)$ and $s=\log_2(3/2)$. Both are inside the strip $0<s<1$. Their sum is one, and neither is one half. The mirror still works exactly.

This little world's objects and rules are exposed all the way down. It gives a pencil test for the distinction between a symmetry that pairs zeros and a mechanism that confines them. The corresponding mechanism for the ordinary Riemann zeta function remains the research question. [PAL construction and live mathematical target](CONSTRUCTION-KEY.md)
