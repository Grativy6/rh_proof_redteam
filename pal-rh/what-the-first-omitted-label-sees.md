# What the first omitted label sees

Christopher Daniel Pang and Hearthline, 25 November 2026. Pang’s question was whether a layer can carry a distinction that its next reading appears to erase. His PAL v2.4 spine, APCI comparison on identical inputs, RPL square scales and BLA boundary accounting suggested changing one ordinary label and pricing the change on the same arithmetic rows. The calculations use the project’s original Möbius reading and its reversible square pass. [Corpus roles](CORPUS-ROUTES.md) · [Original four-row inverse](how-many-square-passes-the-sign-needs.md)

At side **432,000,000,000**, one positive average of the actual rows has value about **23.85338**. Remove one sixth of the contribution attached to its first ordinary label and the result is still positive. Remove one fifth and it is negative. Every row weight in both averaging rules is nonnegative. The exact difference, including its sign, can be recovered from four positive readings after the square pass.

There is also a shorter route to the stock RH statement. Make the square pass once. If its rational reading is nonnegative at every sufficiently late fourth power $j^4$, then RH follows. The negative and positive blocks below give actual tests of this proposal.

## Build the weights with a pencil

Write $w(t)=\max(0,\min(1,2-t))$, $m(d)=\mu(d)\mathbf1_{(d,6)=1}$ and $S_0(y)=\sum_d m(d)w(d/y)/d$. For the averaging rule use the cubic $b(t)=(1-t)_+^3$. Let
$$
 B_M(z)=\sum_{r>M}b(r/z),\qquad B=B_0,\qquad z>0 .
$$
The ordinary label $r$ is the multiplier in this sum. $M=1$ deletes just the summand $b(1/z)$. For the full rule put $n=\lfloor z\rfloor$. Differentiating on a unit interval gives
$$
 B''(z)=\frac6{z^5}\sum_{j=1}^n j(z-j)(2j-z)
       =\frac{3n(n+1)(z-n)(n+1-z)}{z^5}\ge0. \tag{1}
$$
The last equality follows by summing $j,j^2,j^3$. At an integer the entering cubic and its first two derivatives vanish. For $j<z/2$ each summand of the curvature is nonpositive. For $z/2\le j\le z$ it is nonnegative. Removing an initial segment therefore preserves nonnegative curvature. Either only nonpositive terms have been removed, or all the terms left are nonnegative. This proves $B_M''(z)\ge0$ for every $M$ and every $z>0$. The quadratic version already fails at $z=7/4$, where the second derivative of $(1-1/z)^2$ is negative. [Finite curvature identity](PALRH/CubicWindow.lean) · [Nonnegative physical weights](PALRH/CubicWeights.lean)

For an integer side $X\ge1$ set $T=2X$, $b_n=B_M(T/n)$ and $s_n=n(n+1)(b_n-b_{n+1})/2$ for $n\ge1$. The weight of the half-row $n/2$ is $s_{n-1}-s_n$ for $2\le n\le T$. These are rational numbers. Indeed $s_n$ is $X$ times the secant slope of $B_M$ between $T/(n+1)$ and $T/n$. Its difference from the next secant in increasing $z$ has the sign given in (1).

To see what the weights buy, apply them to just the input with label $d$. Its taper increases from $n$ to $n+1$ by exactly $2d/[n(n+1)]$ on $d\le n<2d$ and by zero elsewhere. Summation by parts gives
$$
 \sum_{n=2}^{T}(s_{n-1}-s_n)w(2d/n)=d(b_d-b_{2d}). \tag{2}
$$
Values $b_j$ vanish once $j\ge T$, and $w(2d)=0$ at the unused first sample. The same formula holds for any profile vanishing there. Multiplying by $m(d)/d$ and summing over $d$ uses the actual half-row values of $S_0$. [Finite summation on the original grid](PALRH/CubicQuadrature.lean)

For any real side $X>0$ the same sum has an integral form,
$$
 V_M(X)=X\int_0^{2X} S_0(X/z)B_M''(z)\,dz
       =\sum_d m(d)[B_M(2X/d)-B_M(X/d)]. \tag{3}
$$
In one summand, the taper $w(z/t)$ with $t=X/d$ is constant through $t$ and then has slope $-1/t$ through $2t$. Two integrations by parts, or one ordinary integration on each segment, give $(B_M(2t)-B_M(t))/t$. All sums in (3) are finite. The integral reproduces (2) at integer heads.

At $X=2$ the entire calculation fits on three rows. The full weights at sides $1,3/2,2$ are $7/64,15/64,6/64$. All three original readings are 1. Their total $28/64$ equals $b(1/4)+b(3/4)$. Removing the first ordinary label leaves weights $9/64,0,0$. At this head the total stays positive.

## The first label changes the arithmetic

In the full difference $B(2X/d)-B(X/d)$, the even multiples in the first sum reproduce the entire second sum. At an odd product $n=rd$, the remaining coefficient is $\sum_{d\mid n}m(d)$. Each prime other than 3 dividing $n$ pairs a divisor containing that prime with one omitting it among the nonzero squarefree contributions. Precisely the powers of 3 survive. Thus
$$
 P(X)=V_0(X)=\sum_{j\ge0} b(3^j/(2X))\ge0,\qquad
 V_1(X)=P(X)-[C(2X)-C(X)],\quad C(x)=\sum_d m(d)b(d/x). \tag{4}
$$
For example, the original coefficient at product 10 is zero because the odd-multiple sum has no even products. After the first label is removed, the coefficient there is $-m(10)+m(5)=-1$. At $X=432{,}000{,}000{,}000$ the change is visible in the entire sum.

| Fraction of the first label removed | Result in the units of (3) |
| ---: | ---: |
| 0 | 23.853381271793 |
| $1/6$ | 0.085370246547 |
| $1/5$ | −4.668231958502 |
| 1 | −118.754684879683 |

The table rounds exact rational values. The first label contributes $142.608066151476$ before its removal. Each partial deletion is a convex combination of the full rule and the rule deleting the whole label. Both have nonnegative weights on the same grid.

In the original physical normalization put $U(X)=V_1(X)/X$ and pass its readings through the same square scales $4^a9^b$ with weights $2^{-a}3^{-b}$. This commutes with applying the averaging rule to $S_1$ in (3), by the substitution of $X/(4^a9^b)$ there. At the displayed $X$ the four transformed physical readings at $X,X/4,X/9,X/36$ are respectively about $0.00006002995605$, $0.00011301665165$, $0.00016316483869$, and $0.00030519824664$. Apply the coefficients $1,-1/2,-1/3,+1/6$ and multiply by $X$. The exact result is the last line of the table. This sign change belongs to the omitted-label measurement of $S_0$. The calculation gives positive measured values at the four named arguments after one pass. [Full fractions and signs](../receipt-archives/2026-11-25-pal-cubic-window.json)

The large computation needs only 274 integer quotient arguments. At each it computes $A_j(n)=\sum_{d\le n}m(d)d^j$ for $j=0,1,2,3$. Expanding the cubic evaluates $C$ exactly. Two independent divisor recurrences produce identical four moments at all 274 arguments. With all multipliers $r$, the sum of $r^jA_j(\lfloor n/r\rfloor)$ is the sum of $d^j$ over $2,3$-smooth $d\le n$. With only $(r,6)=1$, the corresponding sum is 1. In each case the $r=1$ term is the sought value and the rest use smaller quotients. Modular results reconstruct unique signed integers since $|A_j(n)|\le n^{j+1}$. Small heads are independently summed on every physical half-row. [Exact replay](../receipt-archives/check_pal_cubic_window.py) · [Quotient arithmetic](../receipt-archives/cubic_window_moments.cpp)

### The original readings at the same side

The measurement is a different mathematical object from the original reading. We evaluated both at this same $X$. Directed rational enclosures give
$$
 -1.551\times10^{-8}< S_0(X)<-1.532\times10^{-8},\qquad
 0.00011478528<S_1(X)<0.00011478559 .
$$
For the physical calculation let $U(n)=\sum_{d\le n}m(d)/d$ and $M(n)=\sum_{d\le n}m(d)$. Expanding the original taper at any real side $t>0$ gives
$$
 S_0(t)=2U(\lfloor2t\rfloor)-U(\lfloor t\rfloor)
       -[M(\lfloor2t\rfloor)-M(\lfloor t\rfloor)]/t .
$$
Both divisor recurrences also compute $U$, using harmonic block weights. For the large harmonic endpoints the integral of $1/t$ on each centered unit interval exceeds its midpoint value. The sum of the midpoint errors beyond the direct cutoff $B$ is at most $1/B^2$, by bounding the second derivative by $2/(r-1/2)^3$ on the cell at $r$. This bounds $H_n-H_B$ between $\log[(2n+1)/(2B+1)]-1/B^2$ and that logarithm. Range reduction and the positive atanh series enclose the logarithm with integer arithmetic. The replay keeps both directed endpoints in each recurrence and intersects the two independent intervals. The four physical passed readings return an interval overlapping the direct value of $S_0(X)$. [Reciprocal bounds](../receipt-archives/cubic_reciprocal_bounds.hpp) · [All four physical enclosures](../receipt-archives/2026-11-25-pal-cubic-window.json)

At the same input we can establish the sign for **whole intervals** without extrapolating from a sample. For a stream of integer marks $a(d)$ the derivative away from the half-rows is $D(y)/y^2$, where $D(y)=\sum_{y<d\le2y}a(d)$. The integral of this derivative gives the exact change, including across corners. For the first pass, $a(p^2d)=p\,m(d)$ for $p=2^i3^j$ and $(d,6)=1$, with zero otherwise. For $A<n\le B$ count all possible marks by
$$
 \sum_{\substack{p=2^i3^j\\p^2\le B}} p\,[G(\lfloor B/p^2\rfloor)-G(\lfloor A/p^2\rfloor)],
 \quad G(z)=z-\lfloor z/2\rfloor-\lfloor z/3\rfloor+\lfloor z/6\rfloor .
$$
For the original stream use $p=1$ alone. On either side of $X$, the change of $D$ is bounded by the two such counts at the lower and doubled endpoints. Integrating the adverse bound against $dy/y^2$ yields the following strictly signed intervals. The band sums at $X$ are respectively $27{,}680$ and $-23{,}449{,}622$.

| Actual reading | Left endpoint | Right endpoint | Consecutive half-rows, inclusive |
| --- | ---: | ---: | ---: |
| $S_0<0$ | 431,946,507,226 | 432,053,471,715 | 213,928,979 |
| $S_1>0$ | 429,332,169,208 | 434,676,543,390 | 10,688,748,365 |

The second interval contains both $810^4$ and $811^4$ and all the real sides between them. Its endpoints mark how far the displayed absolute-count estimate alone goes. They need not be actual sign crossings.

## A zero which the full rule erases

Use $u=\log X$, $F_i(u)=e^{u/2}S_i(e^u)$ and $K_M(v)=e^{3v/2}B_M''(e^v)$. Then $(K_M*F_0)(u)=e^{-u/2}V_M(e^u)$. For the Laplace variable $z$ put $s=z+1/2$. The profile $e^{-v/2}B(e^v)$ has transform $\mathcal M b(s)\zeta(s)$ on $\Re s>1$, with $\mathcal M b(s)=6/[s(s+1)(s+2)(s+3)]$. Applying $\partial_v^2-1/4$ gives $K_0$. Removing the first term subtracts 1 from the Dirichlet series. With fraction $\eta$ removed the multiplier is
$$
 s(s-1)\mathcal M b(s)[\zeta(s)-\eta].
$$
At every nontrivial zeta zero $\rho$ the full multiplier vanishes. With any fixed $\eta>0$ the same value is
$$
 -\frac{6\eta(\rho-1)}{(\rho+1)(\rho+2)(\rho+3)}\ne0. \tag{5}
$$
The positive receiver can therefore be kept while restoring sensitivity to every off-line zero. The taper's transform has no vanishing numerator there, and the original square pass has neither a zero nor a pole in $\Re z>0$. [Formal nonvanishing calculation](PALRH/CubicWindow.lean) · [Source transform](what-the-last-two-rows-carry.md)

In fact, for the original rows **every fixed positive deletion fraction** gives both positive and negative weighted totals at unbounded integer heads. In normalized units the response $V_\eta(X)/\sqrt X$ has strictly positive limsup and strictly negative liminf. Its Laplace transform is
$$
 \frac{2^s\mathcal M b(s)}{1-3^{-s}}\left(1-\frac{\eta}{\zeta(s)}\right). \tag{6}
$$
It is regular on the real axis $z\ge0$ and has a pole at $z=i\gamma$ for any critical-line zero $1/2+i\gamma$. On $0<s<1$ the sign of the alternating eta series gives $\zeta(s)<0$. At $s=1$ its reciprocal has a zero. To see why the pole forces the asserted liminf, suppose the normalized response were eventually at least $-\epsilon$ for every $\epsilon>0$. Add $\epsilon$ on $u\ge0$ and correct the bounded initial segment to make a nonnegative function. Its transform has no positive real singularity. By the elementary argument with the nonnegative Taylor coefficients of its Laplace integral, that integral converges throughout $\Re z>0$. There its modulus at $\sigma+i\gamma$ is at most its value at $\sigma$ for $\sigma>0$. Multiplication by $\sigma$ and passage to zero bounds the modulus of a nonzero simple residue by $\epsilon$, or contradicts a higher-order pole immediately. Taking $\epsilon$ arbitrarily small is impossible. Apply the same argument to the opposite sign. Values between integer heads transfer to integer heads since $|C'(x)|\le3$ for $x\ge1$ by summing its coefficients absolutely, and $P'(x)=O((1+\log x)/x)$. The lower bound on negative excursions and $P(X)=O(1+\log X)$ imply that the maximal removable fraction can be $O(\log X/\sqrt X)$ along an unbounded sequence. [Laplace positivity argument](what-the-last-two-rows-carry.md) · [Hardy’s critical-line zeros](https://fr.wikisource.org/wiki/Page:Comptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences,_tome_158,_1914.djvu/1014)

## Positive rows at arbitrarily large sides, after one pass

The same weights prove more about the original one-pass readings. There are positive blocks near **every** sufficiently large side. Start with an explicit estimate using the cubic. Write $h_1=\log4$, $h_2=\log9$, $u=\log X$, and $F_1(u)=\sqrt X\,S_1(X)$. In this normalization a pass adds $F_0(u-a h_1-b h_2)$ with coefficient one. The full positive source is $Q(v)=e^{-v/2}P(e^v)$. Each integer $0\le b\le\lfloor\log_9 X\rfloor$ has an $a\ge0$ with $1\le X/(4^a9^b)<4$. At this residual argument $P$ includes at least $(1-1/2)^3=1/8$, and division by the square root costs at most 2. Thus
$$
 (K_0*F_1)(u)=\sum_{a,b\ge0}Q(u-ah_1-bh_2)
 \ \ge\ \frac{1+\lfloor\log_9 X\rfloor}{16},\qquad X\ge1. \tag{7}
$$
The kernel vanishes on $v\le0$. Formula (1) gives $0\le K_0(v)\le(3/2)e^{-3v/2}$ for $v\ge0$, with integral at most 1. The seed satisfies $|S_0|\le1$, and the pass costs at most $(\sum 2^{-a})(\sum 3^{-b})=3$ in this norm. For $Z=12X^{1/4}$ the part of the convolution with $v\ge\log Z$ therefore has absolute value at most $(9/4)\sqrt X/Z^2=1/64$. The portion left in (7) proves the unconditional inequality
$$
 \max_{X^{3/4}/12\le y\le X}\sqrt y\,S_1(y)
 \ \ge\ \frac{3}{64}(1+\lfloor\log_9 X\rfloor). \tag{8}
$$
This uses the same first pass at every head, with no zeta-zero hypothesis.

There is an explicit straight line in this positive reading. Average it over one full turn of each clock,
$$
 J(u)=\frac1{h_1h_2}\int_0^{h_1}\int_0^{h_2}(K_0*F_1)(u-r-t)\,dt\,dr
     =\frac1{h_1h_2}\int_{-\infty}^{u}(u-v)Q(v)\,dv .
$$
The two sums of translates in (7) tile the two nonnegative axes when the full turns are integrated. In particular $J''=Q/(h_1h_2)>0$ for $u>-\log2$. Removing just the affine part gives the exact positive remainder
$$
 J(u)-a u-b_0=\frac1{h_1h_2}\int_u^\infty (v-u)Q(v)\,dv
              =O((1+u)e^{-u/2})\qquad(u\ge1).
$$
Here $a=(\int Q)/(h_1h_2)=32\sqrt2/[35(1-1/\sqrt3)h_1h_2]\approx1.0043531$ and $b_0=-(\int vQ(v)\,dv)/(h_1h_2)\approx-4.1780749$. To recover the constants, evaluate $2^s\mathcal M b(s)/(1-3^{-s})$ and its derivative at $s=1/2$. The two-clock backward difference annihilates any affine function of $u$ exactly. The slope explains a feature of the averaged data across all scales. What remains when the turns are undone still has to be priced.

A faster decaying positive weight brings the interval closer to $X$. Replace the cubic by $b(t)=e^{-\pi t^2}$ in (3), now integrating to infinity. For $B(z)=\sum_{n\ge1}b(n/z)$, the resulting $K(v)=(\partial_v^2-1/4)[e^{-v/2}B(e^v)]$ is the classical Riemann xi kernel in this log coordinate. Here is why it has the needed signs. The Gaussian theta identity makes $K$ even, since reflecting the bracket changes it by a linear combination of $e^{v/2},e^{-v/2}$. On $v\le0$ its summands are $e^{-v/2}(4t^2-6t)e^{-t}$ with $t=\pi n^2e^{-2v}\ge\pi$. They are positive. On both tails $K(v)\ll\exp(-\pi e^{2|v|}/2)$, by summing the Gaussian series and absorbing the polynomial prefactors. The integration by parts in (3) still applies. The Gaussian tails justify absolute regrouping of the double sum for every fixed $X$. The full response is again $X^{-1/2}\sum_{j\ge0}b(3^j/(2X))$ in log units. [Rodgers and Tao, theta kernel normalization](https://arxiv.org/abs/1801.05914)

Exactly the same choice of $a$ for each $b$ in (7) gives $(K*F_1)(u)\gg 1+u$ for $u\ge0$, with an absolute positive constant. Set $R=\tfrac12\log(1+u)$. From $|F_1(u-v)|\le3e^{(u-v)/2}$, the entire integral over $|v|>R$ is $O(e^{u/2-\pi e^{2R}/4})=o(1)$. The remaining integral uses a finite positive kernel mass. Consequently some $y$ in $[X/\sqrt{1+\log X}, X\sqrt{1+\log X}]$ satisfies $\sqrt y\,S_1(y)\gg\log X$. Applying this at center $X/(2\sqrt{1+\log X})$ gives a preceding positive reading at $y\gg X/(1+\log X)$ and $y\le X/2$ for all sufficiently large $X$.

These witnesses cover intervals of genuine half-rows. For $0<x\le y$, pad the two seed sums to $d\le2y$. The taper is 1-Lipschitz, $|m(d)|\le1$, and the change of a single summand is at most $(y-x)/(xy)$. Counting the terms, then adding the positive square shifts, gives
$$
 |S_0(y)-S_0(x)|\le2(y-x)/x,\qquad |S_1(y)-S_1(x)|\le6(y-x)/x. \tag{9}
$$
Starting at the witness $y$, the second inequality keeps $S_1$ positive for at least $c\sqrt y\log y$ further units for an absolute $c>0$. Reducing $c$ if necessary gives a block of consecutive positive half-rows strictly before $X$. This controls a whole interval near each sufficiently large head. Equations (8) and (9) also give a polynomial-window version using only the elementary cubic kernel. [Formal scale bound](PALRH/CubicGaps.lean)

## How long can a negative run be?

A sufficient condition for RH concerns the **length** of negative runs. For every $\epsilon>0$, suppose every positive integer $n$ has a preceding nonnegative half-row $m/2$, $1\le m\le n$, with $n-m=O_\epsilon(n^{1/2+\epsilon})$ for the fixed first pass. At large $n$ this puts $m\ge n/2$ on choosing $\epsilon<1/2$. Equation (9), applied from $m/2$ to the real side $x\in[n/2,(n+1)/2]$, gives $S_1(x)\ge -O_\epsilon(x^{-1/2+\epsilon})$. Any finite prefix is absorbed by the implied constant, using the zero reading at $1/2$.

For the return to RH, recall the signed rectangle weight $1/5\le g\le1$. If $f(x)\ge-Cx^{-1/2+\epsilon}$, then $|f(y)|\le5g(H/y)f(y)+6C y^{-1/2+\epsilon}$ for $0<y\le H$, by treating the two signs of $f(y)$. Integrating with $dy/\sqrt y$ prices its gross area by five times the signed rectangle plus $6CH^\epsilon/\epsilon$. At one pass the rectangle costs $O((1+\log(2H))^2)$, by counting pairs of clock shifts in the known bounded seed rectangle. Undoing the pass costs at most 4. An off-line zero of real part $\beta>1/2$ would cost at least $c_\rho H^{\beta-1/2}$ at every sufficiently large head. Taking $\epsilon<\beta-1/2$ proves the implication. [Earlier finite lower bound](what-the-two-signs-cost-together.md) · [Lean deduction](PALRH/CubicGaps.lean)

Conversely, such a zero would force **consecutive negative half-rows in intervals of length at least $c'_\rho y^\beta$ at unbounded sides $y$**. The same area estimates force $\int_0^H(-S_1)_+\,dy/\sqrt y\ge cH^{\beta-1/2}$ for all sufficiently large $H$. If $(-S_1(y))_+<b y^{\beta-1}$ everywhere beyond a fixed side, integrating gives an upper coefficient $b/(\beta-1/2)$ at that power. A sufficiently small $b>0$ contradicts the lower estimate. At the resulting negative sides $y$, (9) keeps the sign strictly negative on $[y,y+c'_\rho y^\beta]$. Many isolated negatives would have no such consequence.

The formal condition uses rational signs and ordinary integer powers. For each positive integer $q$ a positive integer $A$ must work across all finite heads. For each half-row index $n$ there must be an earlier nonnegative $m$ with
$$
 n^q(n+1-m)^{2q}\le A\,n\,m^{2q}. \tag{10}
$$
Taking a $2q$th root bounds the relative gap $(n+1-m)/m$ by $A^{1/(2q)}n^{-1/2+1/(2q)}$. Conversely the stated additive gap bound implies (10), by choosing a smaller exponent, using $m\ge n/2$ eventually, and enlarging $A$ for the initial finite range. A late interval can contain many negative samples and still pass (10). The exact exported theorem is `rh_of_integer_gaps`. [Fixed rational samples](PALRH/SquareSignRows.lean) · [Integer gap theorem](PALRH/CubicGaps.lean)

## One rational sign at each fourth power suffices

The marks give a stronger geometric allowance than (9). On $h\le x\le h+L$ choose the common interpolation weight $t\in[0,1]$ that makes $1/x=(1-t)/h+t/(h+L)$. A seed taper with label $d$ is affine in $1/x$ unless $d$ or $d/2$ lies in this interval. At most $3L+2$ integer labels have such a corner, by counting the two intervals separately. Each corner's distortion, including its reciprocal coefficient, is at most $1/h-1/(h+L)$. This proves the seed estimate
$$
 |S_0(x)-(1-t)S_0(h)-tS_0(h+L)|
 \le \frac{L(3L+2)}{h(h+L)}. \tag{11}
$$

For the pass, replace $h,x,h+L$ by their quotients by $p^2$ and give the result weight $1/p$. The same $t$ works. Terms with $p^2\ge 2(h+L)$ are zero throughout the interval. The total price is at most
$$
 \frac{9L^2+2L\sum_{p^2\le2(h+L),\ p=2^i3^j}p}{h(h+L)} . \tag{12}
$$
For $y\ge1$ the sum of smooth integers $p\le y$ is at most $2y(1+\log_3 y)$, by summing powers of 2 first. At $h=j^4$ the next fourth power has $L\le15j^3$. Therefore (12) is $O(1/j^2)$ uniformly. The three-quarter power comes from equating the chord price $L^2/h^2$ with the required size $1/\sqrt h$. Two nonnegative endpoint readings can cover that entire gap. An alternative bound used in Lean is $\sum_{p\le y}p\le y^{3/2}\sum_p p^{-1/2}$, whose last factor is the product of two fixed geometric series. If both endpoint readings of $S_1$ are nonnegative, the entire interval is bounded below by $-O(1/j^2)=-O(1/\sqrt x)$. The negative area is then $O(1+\log H)$ through head $H$. The signed rectangle and the four-reading inverse give the earlier contradiction at any off-line zero.

Thus the only additional assumption in this route is
$$
 \boxed{\text{For every sufficiently large integer }j,\quad S_1(j^4)\ge0.} \tag{13}
$$
Each entry is an explicit rational number. One pass is used for every $j$. A finite number of initial violations would be affordable. For an integer root $j$ the canonical evaluation uses $N=1+\lfloor\log_2(j^4)\rfloor$ for $j>0$. Increasing $N$ adds only zero terms on that head. A separate Mathlib reference specifies the hypothesis directly as a finite sum over $a,b,d$ with the physical cutoff $d\le 2j^4$. The solution proves that formula agrees with the construction before applying the conditional theorem. [Fourth-power interpolation and stock-target deduction](PALRH/CubicFourth.lean) · [Standalone fixed statement](checks/square-sign/SquareSignChallenge.lean)

A direct forward sieve through $2\cdot128^4=536{,}870{,}912$ checked **every** root $1\le j\le128$. A separate quotient computation checked the 40 roots dividing 1,680, up to $1680^4=7{,}965{,}941{,}760{,}000$. All these samples were strictly positive. At the largest side the outward interval is contained in $(0.0000298307,0.0000298313)$. The overlapping roots agree, and the sign interval at 432 billion covers the additional roots 810 and 811. Positive results throughout this list leave open what happens after an arbitrary starting root.

One tempting shortcut would be monotonicity of $\sqrt x S_1(x)$ on all physical sides. It fails. At $x=262{,}440$ the true right-hand band is $D_1(x)=-8{,}358$. The exact reciprocal enclosures put $2\sqrt x\,(\sqrt xS_1(x))'_+=S_1(x)+2D_1(x)/x$ strictly between $-0.000321$ and $-0.000319$. The normalized values at consecutive fourth powers increased throughout the first 128 roots tested. The derivative calculation explains why that observation cannot be extended to all intermediate sides by monotonicity. [Sampled fourth powers and derivative witness](../receipt-archives/2026-11-25-pal-cubic-window.json)

The count of consecutive negative samples also improves. The absolute-mark formula in the preceding section gives, at $y\asymp H$ and $|z-y|\le l\le H/2$,
$$
 |D(z)-D(y)|\ll l+\sqrt H\,\log(2H).
$$
Indeed each square dilation contributes at most $O(l/p+p)$ to either endpoint band. When following a positive reading, choose the direction in which the current slope is favorable. Over distance $l$ its largest possible adverse change in the reading is $O(l(l+\sqrt H\log(2H))/H^2)$ after dropping that favorable slope. The same argument follows a negative reading in the direction of decreasing values. The derivative formula holds almost everywhere, so a corner at the initial side causes no difficulty.

The unconditional positive witness of size $c\log y/\sqrt y$ therefore supplies a block of length at least $c' y^{3/4}\sqrt{\log y}$ in one direction. The center chosen above leaves room on both sides. A zero of real part $\beta>1/2$ would similarly force a negative block of length at least $c_\rho y^{(1+\beta)/2}$ at unbounded $y$. In particular an upper bound $O_\epsilon(y^{3/4+\epsilon})$ on all negative runs, for every $\epsilon>0$, would suffice independently of their total count. Successive fourth powers near $y$ are separated by $O(y^{3/4})$. The unconditional positive block therefore contains at least $c''\sqrt{\log y}$ **consecutive positive fourth-power samples** for all sufficiently large heads in the localization above. A hypothetical off-line zero would force at least $c_\rho j^{2\beta-1}$ consecutive negative fourth-power samples at unbounded roots $j\asymp y^{1/4}$. In particular (13) can be weakened on paper to subpower lengths of the negative runs in the fourth-root index. These length estimates follow from the actual changes in the band sums.

## Unresolved

The most direct arithmetic target is (13), the sign of the same first pass at the fourth powers. The alternative is to bound the lengths of negative runs at the three-quarter scale. The unconditional positive blocks in neighboring multiplicative windows leave this spacing issue open. The new finite calculation settles the response to withdrawing one ordinary label at the stated side. The real-variable localization, the xi-kernel version, and the recurrent sign changes of the omitted-label raw response are paper results. The companion Lean modules establish the finite reciprocal quadrature, convexity, the slope estimates, and the conditional deductions from (10) and (13).
