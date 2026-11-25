# What the last two rows carry

Christopher Daniel Pang’s PAL research program, 25 November 2026. Pang asked whether a frame could write its own trace onto itself, and asked to try a direction both ways. For the [balanced arithmetic list](the-balanced-newton-handoff.md), the trace can be read in two ways. Its last coefficient and the change between its last two physical rows give the same rational number with opposite signs. Across fourth-power frames that number must change sign infinitely often.

## Read it with a pencil

Use $m(n)=\mu(n)$ when $(n,6)=1$ and zero otherwise. At integer side $H\ge1$, write $s_H=\sum_{n\le2H}w_H(n)m(n)/n$ for the paid slope, $a_H$ for the list, and $e_H(k)=1-\sum_da_H(d)C(k/d)$ for its actual row error. In the outer strip $H<k\le2H$,

$$
a_H(k)+e_H(k)-e_H(k-1)=m(k). \tag{1}
$$

Here is why. True marks through $k$ count one. The old list agrees with them through $H$. Each remaining divisor candidate $d$ between $H+1$ and $k$ has $1\le k/d<2$, so the census reads exactly one. Hence $e_H(k)=\sum_{H<d\le k}(m(d)-a_H(d))$. Subtract two adjacent rows.

At $k=2H$ the true mark is zero because $2H$ is even. The taper has also run down to zero, and its balancing charge is $-2s_H$. Therefore

$$
\boxed{\ e_H(2H)-e_H(2H-1)=-a_H(2H)=2s_H.\ } \tag{2}
$$

At side four the two errors are $373/140$ and $601/140$. Their difference is $57/35$, exactly twice the $57/70$ charged by that frame. Equation (1) also reads the first missing mark at five as $-99/56+43/56=-1$. [Finite proof for every side](PALRH/CarriedEdge.lean) · [Arithmetic reproduction](../receipt-archives/check_pal_carried_edge.py)

## What changes at the next integer

Keep the single additional integer $D_H=\sum_{H<n\le2H}m(n)$. The exact update is

$$
\begin{aligned}
D_{H+1}&=D_H+m(2H+1)-m(H+1),\\
s_{H+1}-s_H&=\frac{D_H}{H(H+1)}
+\frac{m(2H+1)}{(2H+1)(H+1)} . \tag{3}
\end{aligned}
$$

Going from one strip to the next drops $H+1$ and admits $2H+1$ and the even $2H+2$. For each old strip index, its change of taper divided by that index is $1/[H(H+1)]$. The last admitted odd index supplies the second fraction. The entire absolute cost of these individual new odd marks from $H$ onward is at most $\frac12\sum_{h\ge H}1/[h(h+1)]=1/(2H)$. The term whose signed accumulation matters is the old band $D_h/[h(h+1)]$.

The same scalar can jump to a prescribed larger frame directly. For $K\ge8$ put $H=\lfloor\sqrt{2K}\rfloor$. Then $2H\le K$ and $2K<(H+1)^2$. Reading the outermost coefficient in the established Newton update gives $s_K=-s_K(a_H*a_H*g)$, where $g$ is the coprimality indicator and the $s_K$ on the right is the taper applied to the displayed stream. Thus the old balanced list determines the next scalar at every required $K$. The side-four seed gives the raw marks up to 24. Tapering them supplies the initial small sides. [Canonical cut and scalar update](PALRH/CarriedEdge.lean)

## Why fourth-power samples suffice

**A one-sided bound on just the last two rows of each fourth-power frame would imply RH.** More precisely, either of the two following bounds, with its own constants, is equivalent on paper to RH.

- For every $\eta>0$ there is $C_\eta$ such that $s_{j^4}\le C_\eta j^{-2+\eta}$ for all $j\ge1$.
- For every $\eta>0$ there is $C_\eta$ such that $-s_{j^4}\le C_\eta j^{-2+\eta}$ for all $j\ge1$.

Both statements concern a rational number visible in (2). Controlling one side at every prescribed sample is enough. Finding selected small values at arbitrarily large indices supplies less information.

First the missing integer frames can be priced. From (3), $|D_H|\le H$, $|D_{H+1}-D_H|\le2$, and $|m|\le1$ give
$$
|s_{H+2}-2s_{H+1}+s_H|\le \frac{6}{H(H+1)} .
$$
For $0\le k\le L$, add the successive differences on $[H,H+L]$. Each differs from the initial difference by at most $6L/[H(H+1)]$. Subtract the linear interpolation between the two endpoints. The resulting absolute error is at most $12L^2/[H(H+1)]$. At $H=j^4$, $L=(j+1)^4-j^4\le15j^3$, so this costs at most $2700j^{-2}$. A one-sided bound $O_\eta(j^{-2+\eta})$ therefore travels to every intervening integer as $O_\epsilon(H^{-1/2+\epsilon})$ after renaming the arbitrary exponent. [Discrete curvature and interpolation](PALRH/CarriedEdge.lean)

Now extend the slope by $S(x)=\sum_{n\ge1}m(n)w(n/x)/n$ at real $x>0$, with $w(t)=1$ through 1, $2-t$ through 2 and zero thereafter. It vanishes below $1/2$. Off its finitely many corners on a compact interval,
$$
S'(x)=x^{-2}\sum_{x<n\le2x}m(n).
$$
It follows that $S(x)-s_{\lfloor x\rfloor}=O(1/x)$ for $x\ge2$. For $\Re z>0$, absolute summation and the substitution $t=n/x$ give
$$
\Phi(z)=\int_0^\infty S(x)x^{-z-1}\,dx
=\frac{W(z)}{G(1+z)},\qquad
W(z)=\frac{2^{z+1}-1}{z(z+1)},\quad
G(u)=(1-2^{-u})(1-3^{-u})\zeta(u). \tag{4}
$$

At $z=\rho-1$ for a nontrivial zeta zero $\rho$, $|2^\rho|>1$, so the taper preserves the pole there. On the real interval $z>-1$ the ratio is regular. For $0<u<1$ this follows from the positive alternating eta series and $\zeta(u)=\eta(u)/(1-2^{1-u})$. At $z=0$ the poles of $W(z)$ and $G(1+z)$ cancel.

Suppose, for example, $S(x)\le C x^\alpha$ eventually, for some $-1<\alpha<0$. Increase $C$ so $f(x)=Cx^\alpha-S(x)\ge0$ on $x\ge1$. Its Mellin integral, originally on the right, continues as $C/(z-\alpha)-\Phi(z)$ plus an entire function from $[1/2,1]$. The transform of a nonnegative function has a singularity at its real abscissa of convergence if that abscissa is finite. Indeed its Taylor expansion about a real point to the right has nonnegative terms when evaluated a distance to the left, by expanding $\exp(h\log x)$ under the integral. If the transform were analytic at the abscissa, a point just to its right would admit this expansion beyond the abscissa. Monotone convergence there contradicts the definition of the abscissa. The displayed continuation is regular on the real axis strictly above $\alpha$. Thus the integral is holomorphic throughout $\Re z>\alpha$. Equation (4) excludes a zero with $\Re\rho>1+\alpha$. The same reasoning uses $Cx^\alpha+S(x)$ for the opposite direction. Taking $\alpha=-1/2+\epsilon$ proves sufficiency, using zeta symmetry for the left half of the critical strip.

For necessity assume RH. For each $1/2<b<1$, the Balazard–Saias estimate bounds the partial sums of $m(n)/n^b$, as detailed in the [error-exponent proof](when-a-drop-would-count.md#proof-of-the-exponent). Since $\sum m(n)/n=0$, summation by parts gives $\sum_{n\le h}m(n)/n=O_b(h^{b-1})$. Its average over $H\le h<2H$ is the actual $s_H$. This proves both one-sided envelopes. The general use of smoothed Möbius sums to detect zeta zeros is classical. This derivation locates such a sum in the endpoint of Pang’s prescribed frame and proves the stated sample spacing. [Báez-Duarte on Möbius convolutions](https://arxiv.org/pdf/math/0504402) · [Balazard–Saias estimate](https://arxiv.org/pdf/math/0202141)

## An oscillation that is already forced

Unconditionally, **there is $c>0$ such that infinitely many fourth-power sides $H=j^4$ have $s_H>c/\sqrt H$, and infinitely many have $s_H<-c/\sqrt H$**. The same is true for cube sides. These are assertions about actual signed arithmetic at unbounded sizes.

Take any critical-line zero $\rho=1/2+i\gamma$, whose existence is classical. Put $\alpha=-1/2$. At $\alpha+i\gamma$, (4) has a pole. At $\alpha$ it is regular. If the pole is simple let $A$ be its nonzero residue. An eventual bound $S(x)\le Cx^\alpha$ with $0<C<|A|$ leads to the same nonnegative transform as above. It converges absolutely for $\sigma>\alpha$ and hence its absolute value at $\sigma+i\gamma$ is at most its value at $\sigma$. Multiply that inequality by $\sigma-\alpha$ and take $\sigma\downarrow\alpha$. The complex side tends in magnitude to $|A|$, and the real side tends to $C$. This contradicts $C<|A|$. A pole of higher order sends the complex side to infinity, which contradicts any finite $C$. The negative direction follows by changing the sign of $S$. Modifying a compact initial interval contributes an entire term, so the conclusion applies to every tail. [Hardy’s original critical-line result](https://fr.wikisource.org/wiki/Page:Comptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences,_tome_158,_1914.djvu/1014)

Passing to integer sides costs $O(1/H)$. Between neighboring cubes the gap is $O(H^{2/3})$, so the preceding interpolation error is $O(H^{-2/3})=o(H^{-1/2})$. A positive excursion beyond $c/\sqrt H$ forces an excursion at one of the two cube endpoints with a slightly smaller constant. The negative excursions transfer the same way. At fourth powers the elementary interpolation allowance is of square-root order itself. It suffices for the RH criterion with an arbitrary positive exponent. To preserve the excursions at the exact square-root scale, use the true signs once more.

Take $H=j^4$ and $L=(j+1)^4-H\asymp H^{3/4}$. Uniformly for subintervals of $[H,H+L]$ or $[2H,2H+2L]$, the sum of the rough marks is $o(L)$. For ordinary $\mu$ this follows from the all-short-interval theorem of Matomäki and Teräväinen with exponent $2/3$. Intervals too short for its length threshold have length $O(H^{2/3})$ and cost $o(L)$ by counting. To pass to $m$, convolve $\mu$ with the indicator of $d=2^a3^b$. For each fixed $d$ apply the same estimate on the interval divided by $d$. The sum of the absolute allowances for $d>D$ is $O(L\sum_{d>D}1/d+\log^2 H)$ over these smooth $d$, by counting multiples. The reciprocal sum converges. First take $H$ to infinity and then $D$ to infinity. [Matomäki and Teräväinen, Theorem 1.1](https://arxiv.org/pdf/1911.09076)

It follows that $\sum_{x<n\le2x}m(n)$ differs from $D_H$ by $o(L)$ uniformly on $H\le x\le H+L$. In the coordinate $v=1/x$ the derivative of $S(1/v)$ is precisely $-\sum_{x<n\le2x}m(n)$ away from the corners. Its variation from the initial slope is $o(L)$, and the interval in $v$ has length at most $L/H^2$. The difference from the chord connecting the endpoint values is therefore $o(L^2/H^2)=o(H^{-1/2})$. The chord is a convex combination of those two actual readings. This carries both square-root-size excursions onto the very fourth powers used by the criterion.

The same argument locates both extremes if a zero lies farther right. Let $\Theta$ be the supremum of the real parts of the nontrivial zeros and write $y_+=\max(y,0)$, using $\log 0=-\infty$ for this formula. On the fourth-power samples, each sign separately satisfies
$$
\limsup_{j\to\infty}\frac{\log\big((\pm s_{j^4})_+\big)}{\log(j^4)}=\Theta-1.
$$
For a zero of real part $\beta>1/2$, repeat the pole argument at $\alpha=\beta-1$. The elementary fourth-power interpolation cost $O(H^{-1/2})$ is negligible at that scale. For $\Theta=1/2$ the critical-line argument above gives the lower exponent. To obtain the upper bound when $\Theta<1$, use the partial-sum argument for any $\Theta<b<1$, giving $|s_H|\ll_b H^{b-1}$. At $\Theta=1$ the unrestricted $|s_H|\le1$ suffices. Thus both orientations of the endpoint encode the same extremal real part.

In a separate finite calculation the slopes at $50^4,51^4,52^4$ have signs $+,-,+$. Cubes indexed by $187,188,189,190,191$ also have strictly negative slopes. The [integer replay](../receipt-archives/check_pal_carried_edge.py) bounds reciprocals using directed integer division and tests the unit recurrence directly against the physical rows. The proof of infinitely many changes uses (4). [Exact endpoints, tested sizes and formal scope](../receipt-archives/2026-11-25-pal-carried-edge.json)

## How much decay is earned already

Classical unconditional Mertens estimates give $|\sum_{n\le x}\mu(n)|\ll x\exp(-c\sqrt{\log x})$ for some $c>0$. The same form holds for $M_6(x)=\sum_{n\le x}m(n)$ with a possibly smaller $c$. In the convolution over $q=2^a3^b$, terms with $q\le\sqrt x$ have $\log(x/q)\ge(\log x)/2$. For the rest, $\sum_{q>\sqrt x}1/q\le x^{-1/4}\sum_q q^{-1/2}$. Summation by parts then shows that $U(h)=\sum_{n\le h}m(n)/n$ has a limit and its tail is $O(\exp(-c'\sqrt{\log h}))$. The limit is zero since the series just to the right of 1 equals $1/G(s)$ there. Averaging $U$ gives $|s_H|\ll\exp(-c'\sqrt{\log H})$ after decreasing the constant if needed. This proves decay on every side, including the two sequences with sign changes. [Lee and Leong, Theorem 1.1](https://arxiv.org/pdf/2208.06141)

With that limit established, (3) gives an exact signed route to the missing scale,
$$
s_H=-\sum_{h\ge H}\frac{D_h}{h(h+1)}+r_H,\qquad |r_H|\le1/(2H).
$$
The Mertens estimate also gives absolute convergence here. A positive bound on the negative of the first sum, or the opposite bound after reversing signs, can now be tested directly at $H=j^4$. The decay established above is slower as a bound than the required $H^{-1/2+\epsilon}$.

## Unresolved

The sign reversals are earned. The required **upper size** on the true fourth-power readings is open in this construction. Equation (3) locates the remaining cancellation in the signed sum of the previous band $D_h/[h(h+1)]$. The contribution of the individual new odd marks already has an unconditional $1/(2H)$ tail allowance. The analytic one-sided equivalence and the oscillation at unbounded indices are paper arguments. The finite extraction, square transfer, unit update and curvature have companion Lean proofs.
