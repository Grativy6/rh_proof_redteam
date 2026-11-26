# What the last two square roots carry

Christopher Daniel Pang and Hearthline, 26 November 2026 (New York). The [example at 49](../proofs/why-the-last-two-square-roots-remain.md) gives the allocation on individual marks.

## The square map and its inverse

Write $m(d)=\mathbf1_{(d,6)=1}\mu(d)$, and let $v$ range over $2^i3^j$, $i,j\ge0$. Our earlier measure has coefficients $a(v^2d)=v m(d)$ on the unique smooth-square and rough decomposition, with zero on other labels. Put $M(t)=\sum_{n\le t}a(n)$ and $g(z)=\#\{1\le r\le z:(r,6)=1\}$. For the completed measure,

$$
  L(t)=\sum_{n\le t}a(n)g(\sqrt{t/n})
      =\sum_{(r,6)=1}M(t/r^2),\qquad
  M(t)=\sum_{(r,6)=1}\mu(r)L(t/r^2).
$$

Both sums truncate at $\sqrt t$ since the counts vanish below one. The composite coefficient of a dilating square $q^2$ is $\sum_{r\mid q}\mu(r)$ for rough $q$, so only $q=1$ remains. Per final label the unique occupied factorization is $v^2r^2d$ with $r,d$ rough and $d$ squarefree. Its sign is $(-1)^{\Omega(r^2d)}=\mu(d)$. In the critical area norm the inverse costs at most $\sum_{r\le H}1/r\le1+\log H$. The Lean reduction gives stock RH from a lower floor on the continuous, square-completed normalized primitive at every dyadic head. [Formal inverse, norm and conditional floor](PALRH/DenseSquares.lean)

There is also a direct paper implication from an eventual sign on the *integer count*. Write $Z_6(s)=(1-2^{-s})(1-3^{-s})\zeta(s)$. In $\Re s>1$, summation and the Euler product give
$$
 \int_1^\infty L(t)t^{-s-1}\,dt
 =\frac{Z_6(2s)}
 {s(1-2^{1-2s})(1-3^{1-2s})Z_6(s)} .
$$
For $\Re s>1/2$ the numerator has a nonzero absolutely convergent Euler product. The two smooth factors are also nonzero there. On the real interval $(1/2,1)$ the alternating zeta series gives $\zeta(s)<0$, and at $s=1$ its reciprocal extends with a zero. Hence the displayed expression is regular at every real $s>1/2$, while every zeta zero with $\Re s>1/2$ supplies a pole.

If $L(t)\le0$ eventually, remove the finite initial integral and change sign. Its Mellin integral now has a nonnegative integrand on the tail. A finite abscissa of convergence must be a real singularity. Indeed, if the integral continued analytically across its real abscissa, the Taylor series about a real point just to its right would extend a little to its left. In that leftward direction its successive terms are integrals of nonnegative logarithmic moments. Monotone convergence would give a convergent integral at the new point, contradicting the abscissa. Thus the integral is analytic throughout $\Re s>1/2$. The pole test and zeta reflection give RH. This proof on paper exposes exactly which sign premise remains to be earned.

## A continuous part that can be placed on the actual roots

Use
$$
 k(y)=\frac{\lfloor y\rfloor}{\sqrt y}-\frac12\sum_{j\le y}j^{-1/2},
 \quad c=\lim_{n\to\infty}k(n)=-\frac{\zeta(1/2)}2,\quad
 F(z)=\int_0^z k(u^2)\,du .
$$
Set $k=0$ below one. Termwise integration gives
$F(z)=\tfrac12\sum_{j\le z^2}[\log(z^2/j)+1-z/\sqrt j]$.
For $p>0$ put
$$
 G_p(z)=\frac{2p}{3c}\,[F(z/p)-F(z/(2p))],\qquad
 \Gamma_p(z)=g(z)-G_p(z).
$$

To check monotonicity, $3cG_p'(z)=2k((z/p)^2)-k((z/(2p))^2)$ almost everywhere. Each right endpoint minimum $k((n+1)^-)=k(n+1)-1/(2\sqrt{n+1})$ increases with $n$. For $y\ge4$ the minimum exceeds $3/8$ by the four terms at $5^-$, while $k(y)\le c<3/4$. Before $z=2p$ the second term vanishes. Both facts make $G_p$ nondecreasing.

Here is an explicit remainder in the straight-line approximation. Let $c_n=k(n)$. Its positive increments obey
$$
 \frac{c_{j+1}-c_j}{j^{-1/2}-(j+1)^{-1/2}}
   =\frac{\sqrt j}{2(\sqrt j+\sqrt{j+1})}
   \in[1/4-1/(16j),1/4].
$$
Telescoping bounds $c-c_n$. With $n=\lfloor y\rfloor$, the remaining difference is $c_n-k(y)=\sqrt n-n/\sqrt y$. Subtracting $\{y\}/(2\sqrt y)$ from this difference gives $-\{y\}^2/[2\sqrt y(\sqrt n+\sqrt y)^2]$. These bounds imply
$$
 \left|c-k(y)-\frac{1/4+\{y\}/2}{\sqrt y}\right|\le y^{-3/2}\qquad(y\ge2).
$$
Take $b=z/(2p)\ge\sqrt2$ and integrate $c-k(u^2)$ from $b$ to $2b$. The mean term is $(\log2)/2$. The integral of $u^{-3}$ costs $3/(8b^2)$. The centered fractional part has periodic primitive $(\{v\}^2-\{v\})/2$ with oscillation $1/8$. Substituting $v=u^2$ and integrating by parts costs at most $1/(32b^2)$ more. In particular
$$
 \left|z/3-G_p(z)-\frac{p\log2}{3c}\right|\le \frac{4p^3}{3cz^2}.
$$

The root staircase satisfies $-2/3\le g(z)-z/3\le2/3$. For $p=3$ this proves $1/4<\Gamma_3(z)<5/3$ at $z\ge48$. For $p=17/8$ it gives $0\le\Gamma_p(z)<27/20$ at $z\ge96$. On the remaining interval use monotonicity of $G_p$ between successive jumps and check both sides of each jump in the finite formula for $F$. Below one both counts vanish for these choices. The outward rational intervals include every required endpoint. At $p=1$ and $2$, the left side of the jump at 5 breaks the capacity bound. For instance $G_2(5)>1.02272$ while only one root is available just before 5. [Endpoint calculations](../receipt-archives/check_pal_dense_square_payment.py) · [Numerical enclosures](../receipt-archives/2026-11-26-pal-dense-squares.json)

At each $n$, spend $G_p(\sqrt{t/n})$ units, filling its rough roots in increasing order, and keep the remaining $\Gamma_p(\sqrt{t/n})$ units at the end. Each unit carries the original signed weight $a(n)$. For either admissible $p$, at most two roots per owner remain, including a possible fractional one. Any continuous comparison $z/3-b+o(1)$ staying under $g$ has $b\ge2/3$ by the left limits at $6j+5$. At $6j+1$ its limiting deficit is $b+2/3\ge4/3$.

## The first signed amount

For $T\ge1$ let $D_a(T)=\int_1^T M(y)k(T/y)y^{-3/2}dy$, set to zero below one. Expanding $k$ and grouping divisors replaces the input by the positive convolution $a*1$. It is supported on $w=2^i3^j$ with $b(w)=(2^{\lfloor i/2\rfloor+1}-1)(3^{\lfloor j/2\rfloor+1}-1)/2$. Indeed $m*1$ is the smooth indicator, and summing $v$ over $v^2\mid w$ gives this product. The two integrals of the cumulative smooth weights give
$$
 D_a(T)=\sum_{w\le T\ \mathrm{smooth}} b(w)
       \left[\frac{1+\log(T/w)}{\sqrt T}-\frac1{\sqrt w}\right].
$$
For the rough seed $m$ use the same formula with coefficient one and call it $D_0$. Alternatively, integrating each individual $a(n)$ via $u=\sqrt{T/y}$ gives $D_a(T)=2T^{-1/2}\sum_n a(n)F(\sqrt{T/n})$. Hence the signed portion allocated to real roots equals
$$
 P_p(t)=\sum_n a(n)G_p(\sqrt{t/n})
 =\frac{\sqrt t}{3c}\,[D_a(t/p^2)-\tfrac12D_a(t/(4p^2))].
$$
Let $E=[(1-2^{-1/2})(1-3^{-1/2})]^{-1}$, $h=\log4$, $\ell=\log9$. We have $D_0(T)\to-E$ by summing the convergent reciprocal smooth roots in the previous identity. Also $D_a(T)=\sum_{v^2\le T}D_0(T/v^2)$. The number of pairs $ih+j\ell\le\log T$ is $(\log T)^2/(2h\ell)+O(\log(2T))$ by summing their row lengths. For each fixed $K$ the strip $1\le T/v^2<K$ contains $O_K(\log(2T))$ pairs. On all other rows the limiting error can be made arbitrarily small. Thus
$$
 \frac{P_p(t)}{\sqrt t(\log t)^2}\ \longrightarrow\
 -\frac{E}{12ch\ell}=-0.30267087\ldots .
$$
This works for each fixed admissible dilation. The remaining signed sum is $R_p(t)=\sum_n a(n)\Gamma_p(\sqrt{t/n})$. Every $n$ retains its sign and owner. For example, labels $n\le Y$ can contribute at most $6Y$ in absolute value because $\sum_{n\le Y}|a(n)|\le Y\sum_v1/v=3Y$.

## A signed portion of the remainder

Fix $p=3$ and write $\Gamma=\Gamma_3$. Its Mellin mass $I=\int_1^\infty\Gamma(z)dz/z^2$ exists by the two-root bound. To evaluate it, integrate by parts through $Z$. The boundary term $-\Gamma(Z)/Z$ tends to zero. Removing the multiples of 2 and 3 from the harmonic sum gives
$$
 \sum_{r\le Z,\ (r,6)=1}\frac1r
 =\tfrac13(\log Z+\gamma+\log2+\tfrac12\log3)+o(1).
$$
The derivative of $G_p$ gives
$\int_1^Z G_p'(z)dz/z=\tfrac13\log Z+\tfrac13\log(2/p)+C_k/(6c)+o(1)$
where $C_k=\int_1^\infty(k(v)-c)dv/v$. The Mellin transform of $k$ equals $(s-1/2)\zeta(s+1/2)/[2s(s+1/2)]$ by integrating its two sums in absolute convergence and continuing to $s=0$. The estimate on $c-k$ justifies identifying the constant term with $C_k=2\zeta(1/2)-\zeta'(1/2)/2$. Differentiating the completed zeta reflection at $1/2$ and using the digamma value at $1/4$ gives $b=\zeta'(1/2)/\zeta(1/2)=[\log(8\pi)+\gamma+\pi/2]/2$. Therefore
$$
 I=(\gamma+\tfrac32\log3)/3+(4-b)/6=0.96069608\ldots .
$$
Direct integration through 72 and the pointwise capacity on the tail give an independent enclosure $(0.95095,0.97063)$. [Zeta reflection](https://dlmf.nist.gov/25.4) · [Digamma values](https://dlmf.nist.gov/5.4)

Group the remaining roots by their smooth row $v$ and let
$W(y)=\sum_{d\le y}m(d)\Gamma(\sqrt{y/d})$. With $y=t/v^2$, take the fraction $k(K/y)/c$ of each unspent mark when $1\le y\le K$. The selected signed total is $\sum_v vW(t/v^2)k(Kv^2/t)/c$ over those rows. Earlier fractions are excluded by construction. Grouping divisors as before yields $S(x)=\sum_{r\le x}W(x/r)=\sum_{w\le x\ {\rm smooth}}\Gamma(\sqrt{x/w})$, positive and $O(\log^2(2x))$. Hence
$$
 D_W(K)=\int_1^K W(y)k(K/y)y^{-3/2}\,dy
 =K^{-1/2}\int_1^K S(x)\,\frac{dx}{x}
 -\tfrac12\int_1^K S(x)\,\frac{dx}{x^{3/2}}
 \ \longrightarrow\ -E I .
$$
The last integral separates by $x=wz^2$ and uses the summable smooth factors $1/\sqrt w$.

For fixed $K$ the smooth-row rotation argument gives the limit $D_W(K)/(ch\ell)$ after division by $\sqrt t\log t$. Here the cutoff can grow at every head. The variation of $\Gamma$ through $Z$ is $O(1+Z)$ because $g$ and $G$ both increase. Summing over rough $d\le K$ gives $O(K)$ variation for $W$ on $[1,K]$, since $\sum_{d\le K}\sqrt{K/d}=O(K)$. After $y=e^z$, the supported product $e^{-z/2}W(e^z)k(K/e^z)$ has sup norm $O(K)$ and variation $O(K^{3/2})$. The interval discrepancy of the rotation is $O(1/\log(2+\log t))$ after $O(\log t)$ visits, uniformly in the starting phase. The incomplete end rows contribute $O(K(1+\log K)^2/\log t)$ after normalization. Thus $K(t)=\max(10^6,[\log(3+\log t)]^{1/4})$ tends to infinity slowly enough to give
$$
 \frac{\text{selected part of }R_3(t)}{\sqrt t\log t}
 \ \longrightarrow\ -\frac{EI}{ch\ell}=-3.4892967\ldots .
$$
The earlier proof gives the integer-separation discrepancy estimate and the periodization argument. [Smooth-row transfer](where-the-negative-running-mass-comes-from.md)

## Finite sign ranges and reproduction

Through 500,000 we generated every input mark and every rough-square copy. The last positive completed head is 43 in that range, and the last nonnegative head is 44. For larger $t$ group the roots with $\lfloor t/r^2\rfloor\le1000$ first. Their sum equals
$$
 \sum_{n\le1000}a(n)g(\sqrt{t/n})-M(1000)g(\sqrt{t/1001}).
$$
Replacing each $g(z)$ by $z/3$ gives a coefficient of $\sqrt t$ between $-1.07137098$ and $-1.07137097$. The error is bounded by $(2/3)(\sum_{n\le1000}|a(n)|+|M(1000)|)=2132/3$. This entire group is strictly negative at $t\ge500000$. The remaining roots each read $M$ at an integer above 1000. The [earlier bounds on those actual integers](../proofs/the-integer-that-turns-at-forty-four.md) therefore give $L(t)<0$ from 45 through **27,373,823,781** by our direct arithmetic, and through **ten trillion** when using the earlier published finite Mertens bound of Lioen and van de Lune. The two large exact counts in the reader table are computed directly without that outside bound.

The two native recurrences start respectively with rough Möbius signs and rough Liouville signs. At head $906{,}150{,}257$, ordinary Liouville has sum **+1** while our completed measure gives **−2,997,993**. The prime factors 2 and 3 have different weights in the two measures. [Native recurrences](../receipt-archives/dense_square_counts.cpp) · [Pólya comparison, Borwein, Ferguson and Mossinghoff](https://www.cecm.sfu.ca/~pborwein/PAPERS/P208.pdf) · [All inputs, counts and directed bounds](../receipt-archives/2026-11-26-pal-dense-squares.json)

## Unresolved

To close this route one sufficient estimate is $R_3(t)\le(E/(12ch\ell)-\epsilon)\sqrt t(\log t)^2$ at every sufficiently late head, for some $\epsilon>0$. The second selection identifies one more negative contribution inside $R_3$. Signs from the other unspent fractions are still capable of growing together. The finite percentages place no uniform upper bound on them.
