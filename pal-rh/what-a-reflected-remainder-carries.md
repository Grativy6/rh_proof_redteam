# What a reflected remainder carries

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). GPPR keeps the event label and its multiplicity when a wrapped observation collides. APCI asks whether changing the observation changes its answer on the same input. Pang also asked us to try both orientations of every directional idea. Here the input is the actual first square pass. Ordinary division of integers supplies the orientation and the return cost. [Corpus route and editions](CORPUS-ROUTES.md) · [Earlier cubic receiver](what-the-first-omitted-label-sees.md)

**At a side of one trillion, a single sector of the remainder calculation has absolute cost greater than 158 million. Its actual signed contribution lies between −45,627 and −45,417. The entire known positive source at that side is only 39.117 million.** The signs in that sector do real work. Even its guaranteed absolute cost alone would exceed the available positive source four times over. [Independent arithmetic reconstructions](../receipt-archives/2026-11-25-pal-reflected-cells.json)

## Divide once, then turn the remainder around

Continue with $m(d)=\mu(d)\mathbf1_{(d,6)=1}$. For the passed stream write $a(p^2d)=p\,m(d)$ for $p=2^i3^j$, $(d,6)=1$, and zero elsewhere. The raw stream uses just $m$. Each positive index of the passed stream has at most one such expression with a rough cofactor. Define $w(t)=\max(0,\min(1,2-t))$. The recovered reading is $S(x)=\sum_k a(k)w(k/x)/k$.

At integer head $T$ and label $d\ge1$, let $r=T\bmod d$. The error is zero for $d>T$. Otherwise it is
$$
 G(T,d)=\frac{r(d-r)(d-2r)}{2dT^2}
       -\frac{r^2(d-r)^2}{2dT^3}. \tag{1}
$$
Reflecting $r$ to $d-r$ reverses the first term. The second survives. At $T=12,d=5$, for example, $r=2$ and $r(d-r)=6$. The two numerators over the common denominator $2dT^3$ are $12\cdot6\cdot1-36=36$ and $12\cdot6\cdot(-1)-36=-108$. Their mean is $-36$. The sign of the first term records which orientation was used.

The positive reference weight is $h(t)=(1-t)_+^2(1+2t)$. Every term in (1) comes from this finite sum.
$$
 \frac{(T-d)_+}{2d}-\sum_{i=1}^{\lfloor T/d\rfloor} h(id/T)=G(T,d). \tag{2}
$$
Here $T>0$. To check the identity, multiply by $2dT^3$ and sum $(T-id)^2(T+2id)$. Consecutive values of $T r(d-r)(d-2r)-r^2(d-r)^2$ telescope as $r$ falls by $d$. The terminal remainder is exactly $T-d\lfloor T/d\rfloor$. The full sum is zero on both sides before the first label. [Finite polynomial identity and reflection](PALRH/ReflectedCells.lean)

Write $P_h(X)=\sum_{p,j}p\,h(3^jp^2/(2X))$ for the first pass, with $p=2^a3^b$. For the raw stream take $p=1$ alone. This quantity is nonnegative. In the difference of the two reference sums in (2), the even ordinary multipliers cancel, then the signed divisor sum on each remaining odd product leaves just the powers of 3. Since the difference of the two linear ramps is $Xw(k/X)/(2k)$, one obtains
$$
 \frac X2\,S(X)=P_h(X)+\sum_{k\le2X}a(k)[G(2X,k)-G(2X,2k)]. \tag{3}
$$
The single physical head $T=2X$ serves both labels $k$ and $2k$. At integer $X$ the latter remainder equals $G(X,k)$. Labels before a half-turn and after it need different signs in the first part of (1). [Actual square-pass identity](PALRH/ReflectedCarry.lean)

## Which labels can be paid before the sign test?

For $d\le T$ put $v=d/T$, $q=r/d$. The error is $v^2q(1-q)(1-2q)/2-v^3q^2(1-q)^2/2$. Thus $|G(T,d)|\le(d/T)^2$. Also $\sum_{k\le D}|a(k)|\le\sum_p p\lfloor D/p^2\rfloor\le3D$. With $X=j^4$ choose the largest integer $D$ with $D^3\le j^{10}$ (equivalently $D=\lfloor X^{5/6}\rfloor$). The omitted part from product labels $k\le D$ in (3) costs at most
$$
 \frac{15D^3}{4X^2}\le \frac{15}4\sqrt X. \tag{4}
$$
Consequently it suffices that the known positive source plus the **retained signed sum over $D<k\le2X$** be nonnegative at every sufficiently late fourth power. The actual reading then stays above $-15/(2\sqrt X)$ at those samples. A fixed debt of that size fits the already proved fourth-power chord estimate. [Formal retained-label implication](PALRH/ReflectedCarry.lean) · [Square-root debt at the sample](PALRH/CubicFourth.lean)

We tested this retained inequality, including a price for every removed term, at $X=432{,}000{,}000{,}000$ and at every twelfth power $j^{12}$ for $1\le j\le10$. At $10^{12}$ the full positive source is about $39{,}116{,}710.89$. The retained result is still above $35{,}273{,}659$ even after charging the full possible earlier contribution. The twelfth-power samples also test the [sparser paper criterion](how-far-a-negative-run-must-travel.md), for which the same actual reading is used. They leave its all-scale condition open.

At the earlier 432-billion head, the raw $XS_0(X)/2$ lies between $-3{,}350$ and $-3{,}310$. The same finite arithmetic with only the odd part of (1) reflected gives a value between $2{,}625$ and $2{,}743$. The full first-pass source is about $24{,}838{,}774.23$ at this head. Its odd and even adjustments are separately recorded, along with the four-reading inverse on each component. Direct directed sums of the modular formula at smaller heads independently cross-check the polynomial moment calculation.

### A saving from the actual signed marks

The pointwise allowance in (4) needs no cancellation. A known short-interval bound lets the discarded range grow to $D=X^{5/6}(\log X)^{1/12}$ for sufficiently large $X$, still at cost $O(\sqrt X)$. This is a paper estimate.

Write $a=\mu*c$ with $c(n)\ge0$ supported on $2,3$-smooth labels. Its factors come from the rough restriction and the square pass, so $\sum c(n)n^{-3/5}<\infty$ by geometric summation. For $y^{2/3}\le h\le y$, one has $\sum_{y<n\le y+h}a(n)\ll h/(\log y)^{1/4}$. To check the transfer, in the convolution first take $d\le y^{1/12}$. The inner interval of length $h/d$ is at least $(y/d)^{3/5}$ there. Apply the uniform Möbius estimate with $\theta=3/5$ and $\epsilon=1/12$, then sum the convergent weights $c(d)/d$. The rest costs $O(hy^{-1/30}+y^{3/5})$ by counting at most $h/d+1$ integers and using the displayed $3/5$ moment. [Matomäki and Teräväinen, Theorem 1.1](https://arxiv.org/pdf/1911.09076#page=1)

For a numerator $T=X$ or $2X$ split $X^{4/5}<d\le D$ into dyadic bands $d\asymp Y$. Within a band split again where $\lfloor T/d\rfloor$ changes. A complete cell has width comparable to $Y^2/X\gg Y^{3/4}$. Every partial sum of the marks on that cell costs $O((Y^2/X)/(\log Y)^{1/4})$. For a subinterval shorter than $O(Y^{2/3})$, count absolute marks by the square dilations, giving $O(Y^{2/3}+\sqrt Y\log(2Y))$. This fits the same allowance. The at most two clipped cells at a band edge use their full cell allowance. Formula (1) and its derivative on a single fractional turn bound the supremum plus total variation of $G(T,d)$ by $O((Y/X)^2)$. Partial summation over $O(X/Y)$ cells and then geometric summation over bands give a total $O(D^3/[X^2(\log X)^{1/4}])$. Labels through $X^{4/5}$ cost $O(X^{2/5})$ by (4). This pays the asserted larger cutoff with actual signs and no RH hypothesis.

## One angular sector at one trillion

Take $X=10^{12}$ and $8X/5<d\le5X/3$. On this entire interval $G(X,d)=0$. The argument $2X/d$ lies between $6/5$ and $5/4$. Its fractional part $q$ lies between $1/5$ and $1/4$, and
$$
 G(2X,d)=\frac{q(1-q)}{2z^2}\left(1-2q-\frac{q(1-q)}{z}\right)
 \ \ge\ \frac{3}{250},\qquad z=2X/d .
$$
There are at least **13,183,894,191** squarefree labels coprime to six in the sector. Count the labels coprime to six with $g(n)=n-\lfloor n/2\rfloor-\lfloor n/3\rfloor+\lfloor n/6\rfloor$. If the interval contains $L$ integers, removing multiples of prime squares costs at most $L\sum_{p\ge5}p^{-2}+\sqrt{5X/3}$. Every such prime is $6j-1$ or $6j+1$, so the reciprocal-square sum is at most $(1/25+1/36)\sum_{j\ge1}j^{-2}\le61/450$. Each surviving label has $|a(d)|=1$. This proves an unsigned bill of at least $158{,}206{,}730.292$ on the actual stream. The same bounds give a positive constant times $X$ at all large heads, whereas the full source is $O(\sqrt X(1+\log X))$ by summing the smooth square roots and their powers-of-three copies.

For the signed number, the floor is exactly 1 throughout the sector. Substituting that value into (2) gives $G(T,d)=T/(2d)-3/2+3d^2/T^2-2d^3/T^3$ with $T=2X$. We evaluated the signed moments of orders $-1,0,2,3$ at the two exact endpoints. One recurrence uses all ordinary multipliers and a smooth source. The other uses only multipliers coprime to six and the unit source, with a different sieve cutoff. Both reconstruct the moments on **this same sector**, including their true signs. [Reproducible moments, integer bound and enclosures](../receipt-archives/check_pal_reflected_cells.py)

## A complete interval needs only the squared remainder

There is also a way to eliminate the odd part legitimately. Set $b(t)=(1-t)_+^3$ and let
$$
 E(T,d)=\frac{r^2(d-r)^2}{4dT^2}\quad(1\le d\le T),\qquad E(T,d)=0\quad(d>T).
$$
This energy has the same value in the two orientations. The elementary calculation preceding (2) now takes the form
$$
 \frac{(T-d)_+^2}{4d}-T\sum_{i\le T/d} b(id/T)=E(T,d). \tag{5}
$$
Indeed $u^2(u-d)^2-(u-d)^2(u-2d)^2=4d(u-d)^3$. Sum that single identity and the last term is $r^2(d-r)^2$.

Let $P_b$ denote the same positive source as $P_h$ with the cubic $b$ in its place, and let $Q(T)=\sum_k a(k)[E(T,k)-E(T,2k)]$. At integers $X<Y$, the exact area of the true readings is
$$
 \int_X^Y yS(y)\,dy =
 2Y P_b(Y)-2X P_b(X)+Q(2Y)-Q(2X). \tag{6}
$$
The known part is positive. To prove (6) on a pencil grid, $yS(y)$ is affine between adjacent half-integers. Its trapezoid sum is exact. In half-row indices $2X\le n\le2Y$ the weight of $S(n/2)$ is $n/4$ in the interior and $n/8$ at the two ends. Outside the interval the weights vanish. Equation (5) gives these same weights by two finite differences of its left-hand ramp in the reciprocal grid. Thus (6) measures the original rows themselves while requiring only the even residue. [Finite quadrature and window theorem](PALRH/EvenWindows.lean)

Between wrap points the derivative of $E(T,d)$ with respect to its real numerator $T$ is exactly $G(T,d)$. At a wrap the first derivative extends continuously. Integrating that identity is why an interval can carry the same signal with an even potential at its two ends. It also transports the signed logarithmic improvement above to the window, multiplying its cost by the width in $T$.

For $X=j^4$, $Y=X+j^2$, the same cutoff $D=\lfloor X^{5/6}\rfloor$ suffices. Let $s_t=(t\bmod d)(d-(t\bmod d))$. It stays between 0 and $d^2$ and changes by at most $d$ in one integer step, including the wrap back to zero. For $d\le A\le B$, it follows that
$$
 |E(B,d)-E(A,d)|\le(B-A)d^2/A^2.
$$
For example, split $|s_B^2/B^2-s_A^2/A^2|/(4d)$ into the change of the numerator and the change of its reciprocal weight. Use $|s_B^2-s_A^2|\le2(B-A)d^3$ and $1/A^2-1/B^2\le2(B-A)/(A^2B)$. With $A=2X$, $B=2Y$, insert both $d$ and $2d$ and sum over the earlier product labels. Their total cost is at most $15(B-A)D^3/A^2\le8X$.

If (6) with just the **retained** product labels $k>D$ is nonnegative in every sufficiently late such interval, its actual integral is at least $-8X$. Its positive trapezoid weights have total mass at least $(B-A)A/8=j^6/2$. Some real half-row reading is therefore at least $-16/j^2$. The starting fourth-power reading can differ downwards by at most another $6/j^2$ by the previous relative variation theorem. This gives a sufficient arithmetic test using only $r^2(d-r)^2$ on the retained bands. [Retained even-remainder deduction](PALRH/EvenRemainders.lean) · [Independent rational statement](checks/even-window/EvenWindowChallenge.lean)

Over the million physical units starting at side 432 billion, (6) is strictly negative on the raw stream. The known positive part exceeds 49 million, while the actual integral lies between $-6.693$ and $-6.627$ billion. The change of the even energy alone carries the sign reversal. The same interval is strictly positive after one pass. The signs were independently bounded by integrating the actual initial signed band with every possible admission and exit charged. All nine complete windows between the tested successive twelfth powers also have positive passed integrals. The squared-remainder test on $[j^4,j^4+j^2]$, with its early terms removed and priced, also passes at each tested root $j=n^3$, $1\le n\le10$.

## Unresolved

Control the signed high-modulus sector at arbitrarily late scales. Absolute values fail even on a single fixed sector. The reflection formula states exactly what direction contributes to a point, and the window version shows how to transfer that obligation into changes of squared distances at its two endpoints. Neither finite calculation settles the late behavior. [What the signs would have to do if RH failed](how-far-a-negative-run-must-travel.md)
