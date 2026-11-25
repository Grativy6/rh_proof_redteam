# The signed matrix inside a square

Christopher Daniel Pang and Hearthline · 25 November 2026

At side $H=1024$, the rough squarefree integers up to $H^2$ made entirely of primes at most $H$ sum to **$-16{,}226$**. Those with one larger prime sum to **$+16{,}097$**. Their actual signed total is $-129$. There is an independent way to recover the same number using only the signs already available through $1024$. A square matrix made from them has integer quadratic value $35$, and $2(-47)-35=-129$. [Exact square census](../receipt-archives/check_pal_core_squares.py)

## What the old frame can compute

Put $g(n)=[\gcd(n,6)=1]$, $m_n=g(n)\mu(n)$, $R(x)=\sum_{n\le x}m_n$ and
$$
C(t)=\sum_{1\le k\le t}g(k)
=\lfloor t\rfloor-\lfloor t/2\rfloor-\lfloor t/3\rfloor+\lfloor t/6\rfloor .
$$
For $1\le i,j\le H$ form $A_{ij}(x)=C(x/(ij))$, and put $F_H(x)=\sum_{i,j\le H}m_i m_j A_{ij}(x)$. Then
$$
R(x)=2R(H)-F_H(x),\qquad H\le x<(H+1)^2
$$
for integer $x$. This is Huxley and Watt’s two-factor hyperbola identity applied to the completely multiplicative filter $g$. Their published matrix identity is a mathematical input here. Pang’s square shell and the two-clock calculation tell us which filter to apply and which boundary readings to keep. [Huxley and Watt, Theorem 1 and its two-factor specialization](https://arxiv.org/abs/1807.05890) · [Lean derivation on this branch](PALRH/CoreMatrix.lean)

Here is the finite proof. The sum $\sum_{i j k\le x}m_i m_jg(k)$ equals $R(x)$ by the identity $\sum_{d\mid n}\mu(d)=[n=1]$ and multiplicativity of $g$. Either $i\le H$ or $j\le H$. In the part with $i\le H$, summing over $j,k$ gives exactly one at each $i$, hence the part sums to $R(H)$. The same holds with the two indices reversed. Their intersection is precisely $F_H(x)$. This derivation genuinely uses only the earlier Möbius values in the matrix.

A quantitative consequence is that a two-sided $O_\epsilon(H^{1+\epsilon})$ bound on $F_H(H^2)$ implies RH. Between adjacent squares there are only $2H$ further integer positions before the next square. Also $|R(H)|\le H$. The four-core transfer then controls the full Möbius primitive. These steps, including the implication to the bare stock proposition, are formalized. [Four-core transfer and square coverage](PALRH/RoughSquares.lean) · [Matrix implication](PALRH/CoreMatrix.lean)

## The first unpaid product can reverse sign

Keep the coefficients through $H$ fixed and continue the same formula past its earned window. For any integer $x\ge H$, inclusion–exclusion gives exactly
$$
R(x)-\{2R(H)-F_H(x)\}
=\sum_{\substack{i,j>H\\ij\le x}}m_i m_j C(x/(ij)).
$$
Equivalently write $a(n)=m_n[n\le H]$ and use ordinary Dirichlet convolution $*$, whose coefficients are finite divisor sums. The inverse law is $m*g=\delta_1$. The updated coefficient list $b=2a-a*a*g$ satisfies the algebraic identity $m-b=(m-a)*(m-a)*g$. The new error really does consist of **two copies of the unpaid tail**. A convolution square can have negative cumulative readings.

A pencil-sized example fixes $H=30$. The next nonzero marks are $m_{31}=-1$ and $m_{35}=+1$ since $35=5\cdot7$. At 961 only $(31,31)$ has entered; the true total is $-43$ and the inherited formula gives $-44$. At 1085 both $(31,35)$ and $(35,31)$ have entered. Their two minus signs take the cumulative unpaid reading from $+1$ to $-1$. The true total is now $-48$ and the inherited formula gives $-47$. At 1147 the two orderings of $31\cdot37$ carry it back to $+1$. This explicitly breaks a proposed **nonnegative** remainder rule for this construction on its genuine inputs. [General tail identity and the first two signs in Lean](PALRH/CoreMatrix.lean) · [Exact small pair list](../receipt-archives/check_pal_core_squares.py)

## A bounded kernel needs a lower estimate only

The rough census has average density $1/3$. Write $K(t)=C(t)-t/3$. This is a real, zero-mean, 6-periodic sawtooth with $|K|\le2/3$. Its only jumps occur at integers congruent to $1$ or $5$ modulo 6. The form separates exactly as
$$
F_H(H^2)=\tfrac13\left(H\sum_{i\le H}m_i/i\right)^2+
Q(H),\qquad Q(H)=\sum_{i,j\le H}m_i m_j K(H^2/(ij)).
$$
The first term is nonnegative for the actual real signs. Therefore the single estimate
$$
\forall\epsilon>0,\qquad Q(H)\ge -C_\epsilon H^{1+\epsilon}\quad(H\ge1)
\tag{1}
$$
implies RH. Indeed (1) gives $R(H^2)\le2H+C_\epsilon H^{1+\epsilon}$. Interpolating between adjacent squares gives the **upper** bound $R(x)\le C'_\delta x^{1/2+\delta}$ for every $\delta>0$.

The passage from this one-sided bound to RH is the classical Landau argument. Here are its hypotheses and proof in these coordinates. For real $\alpha\in(1/2,1)$ suppose $R(x)\le Cx^\alpha$ for all $x\ge1$, enlarging $C$ on a finite interval if necessary. The nonnegative function $P(x)=Cx^\alpha-R(x)$ has Mellin integral
$$
L(s)=\int_1^\infty P(x)x^{-s-1}\,dx
=\frac{C}{s-\alpha}-\frac{1}{s(1-2^{-s})(1-3^{-s})\zeta(s)}
\qquad(\Re s>1).
$$
If a zeta zero with real part $\beta>\alpha$ existed, the right expression would have a pole there. The integral’s abscissa of convergence $\sigma_c$ would then be at least $\beta$, by absolute convergence and the identity theorem. On the positive real axis above $\alpha$ the expression is regular. The reciprocal zeta has a zero at one. For $0<s<1$ the positive paired alternating series for $(1-2^{1-s})\zeta(s)$ excludes a real zero. The other factors are nonzero there.

A nonnegative Mellin integral must have a singularity at its finite real abscissa. To see this, suppose a holomorphic disk crosses that real boundary, choose a real center $c>\sigma_c$ sufficiently near it, and take a Taylor displacement $r>c-\sigma_c$ still inside the disk of convergence at $c$. Differentiation on the convergent side gives the Taylor coefficients for $L(c-r)$ as the nonnegative integrals of $P(x)x^{-c-1}(r\log x)^n/n!$. Monotone convergence sums them to $\int P(x)x^{-(c-r)-1}dx<\infty$. This contradicts the definition of $\sigma_c$. This proves the one-sided implication on paper. Conversely RH gives $R(H^2)=O_\epsilon(H^{1+\epsilon})$ and $\sum_{i\le H}m_i/i=O_\epsilon(H^{-1/2+\epsilon})$ by partial summation, so it implies (1) as well. [Classical oscillation theorem discussed by Kaczorowski and Pintz](https://personal.math.ubc.ca/~gerg/teaching/592-Fall2018/papers/1986.Kaczorowski_1.pdf) · [Formal inequality from the centered estimate to the upper square bound](PALRH/CoreMatrix.lean)

## Exact boundary hits cancel

For $H<x<(H+1)^2$, taking the difference of the two finite matrix identities gives
$$
F_H(x)-F_H(x-1)=-m_x .
$$
On the left this counts every pair with $ij\mid x$ and $g(x/(ij))=1$, weighted by $m_i m_j$. In particular **the entire signed jump at $x=H^2$ is zero for every $H>1$**, since $\mu(H^2)=0$. For a side coprime to 6 there can be many such pairs. For $H=35$ their underlying indices are exactly the divisors of 35 and the total is $(1-1-1+1)^2=0$. With an even side a rough pair cannot absorb the factor 2 of the square, so no such pair crosses. More generally smoothing the threshold over $H^2-H+1,\ldots,H^2+H$ with nonnegative weights summing to one changes the true quadratic value by at most $H$ for $H\ge2$. The exact finite identities locate every sign and give that allowance. [Formal threshold-jump theorem](PALRH/CoreMatrix.lean)

The same identity permits a finite oscillatory version of (1). At continuity points, the symmetric Fourier series of $K$ is
$$
K(t)=\frac{2}{\pi}\sum_{n\ge1}\frac{\cos(\pi n/3)}{n}\sin(\pi nt/3).
$$
At its jumps the series gives the midpoint. This follows by integrating the two unit jumps per period against the characters; the constant derivative $-1/3$ contributes only to mode zero. The discrepancy of $1/2$ from the right-continuous value cancels in the full quadratic sum by the exact jump theorem. After $L$ modes, summation by parts of the geometric series bounds each of the two shifted sine tails by $O(1/(L\|(t\pm1)/6\|_{\mathbb R/\mathbb Z}))$ away from its own jump, and that shifted sine series is exactly zero at the jump itself.

For $t=H^2/(ij)$ a distance to a near jump $q\equiv\pm1\pmod6$ is $|H^2-qij|/(ij)$. For each nonzero integer difference $b=H^2-qij$ and positive $q$ nearest to the corresponding progression, the number of triples is at most $\tau_3(H^2-b)$. Here $1\le H^2-b\le4H^2$. The bound $\tau_3(n)\ll_\delta n^\delta$ follows from $\tau_3(p^v)=\binom{v+2}{2}$: for large primes this is at most $p^{\delta v}$, and the finitely many small primes cost a constant at any fixed exponent. Nonpositive nearest points are bounded away from $t\ge1$ and cost $O(1/L)$ per pair. Summing $1/|b|$ and using $ij\le H^2$ gives total truncation error $O_\epsilon(H^{2+\epsilon}/L)$ for coefficients $|m_i|\le1$, after the signed midpoint correction. **Modes $1\le n\le H$ suffice for (1)**. All exact hits and the entire higher-frequency tail have a proved allowance. The same divisor count permits removal of the original bounded-kernel entries within integer product deficit $|H^2-qij|\le H$ at total cost $O_\epsilon(H^{1+\epsilon})$. Neither statement gives a sign bound for the remaining frequencies.

## What fails if the signs are replaced

Take rough squarefree indices in $I=[0.47H,0.49H]$ and $J=[0.39H,0.40H]$. The uncentered matrix takes precisely the values $1,2,2$ on $I^2,I\times J,J^2$ respectively. If the sums of the chosen coefficients on the two blocks are $U,V$, the contribution from their union is $(U+2V)^2-2V^2$. Replacing the signs on the same supports by $-1$ on $I$ and $+1$ on $J$ gives a negative contribution of order $H^2$ for large $H$. The two block sizes have asymptotic ratio two and positive density. Centering subtracts a nonnegative square, so this also defeats any proposed $O_\epsilon(H^{1+\epsilon})$ lower allowance for **arbitrary** sign vectors of absolute value at most one, even on the right support. At $H=1536$ the genuine two block sums are $-1,-2$ and their uncentered value is $17$. The sign replacement gives $-31$. The unmet estimate (1) is specific to the Möbius signs.

A second way of removing a positive term keeps a different piece of the geometry. Subtract the matrix of all ones from $A$. The part with $ij>H^2/5$ then vanishes exactly, because 5 is the next rough cofactor after 1. Its quadratic form $P_H=F_H(H^2)-R(H)^2$ satisfies
$$
R(H^2)=1-(R(H)-1)^2-P_H .
$$
Thus a subpower-times-$H$ lower bound for $P_H$ is also sufficient. For each outer row $j\le H$ with $\lfloor H^2/j\rfloor<5(H+1)$, the remaining row dotted with the **actual** side vector is exactly $1-R(\lfloor H^2/j\rfloor)$. All omitted indices $i>H$ in the full divisor convolution see only cofactor 1. This ties the surviving cross term to a neighboring signed walk. At $H=1024$ the proposed bound $P_H\ge-H$ already fails: $P_H=35-(-47)^2=-2174$. This failure of the particular constant leaves the growth-exponent question open. [Exact outer-row calculation](PALRH/CoreMatrix.lean)

### The actual three primes and the part left over

There is a failure even before changing any signs. At side $1024$ the primes in $I$ are $487,491,499$. Their combined centered quadratic value is
$$
9-\frac{1024^2}{3}\left(\frac1{487}+\frac1{491}+\frac1{499}\right)^2
=\frac{-170012659158074293}{42711345478502067}<-3 .
$$
Charging one unit for each of those three genuine marks already runs short on this subset. The remaining rough squarefree inputs in the **same** interval are $485=5\cdot97$, $493=17\cdot29$ and $497=7\cdot71$, all with positive signs. The unweighted sum of the six is zero. The surviving reciprocal sum is exactly
$$
\frac{2}{485\cdot487}-\frac{2}{491\cdot493}+\frac{2}{497\cdot499}.
$$
The centered quadratic value of the six is the negative square of this quantity times $1024^2/3$, between $-1/40000$ and zero. This is a trace of the locations of the pairs after their counts have canceled.

At arbitrary large sides, real prime pairs in $I$ alone contribute at most $-cH^2/\log^2 H$ with an absolute $c>0$, by the prime number theorem on this fixed relative interval. All inputs in the full $I^2$ have the two-moment formula $U^2-(H^2/3)(\sum_{i\in I}m_i/i)^2$. The unconditional Mertens estimate below and partial summation reduce that whole signed value to $O_A(H^2/\log^A H)$ for any fixed $A$. This pays the prime-pair term at every fixed inverse-log order. Bound (1) demands the stronger side-length scale.

### A whole part of the square paid from the previous frame

Let $r=\lfloor H/2\rfloor+1$, $S(k)=R(k)-R(r-1)$, and $U=S(H)$. On $r\le i,j\le H$ every uncentered entry is one. Summation by parts gives
$$
H\sum_{i=r}^{H}\frac{m_i}{i}=U+Z,\qquad
Z=H\sum_{k=r}^{H-1}\frac{S(k)}{k(k+1)} .
$$
The centered contribution of this entire outer square is therefore
$$
U^2-\tfrac13(U+Z)^2=\tfrac23(U-Z/2)^2-\tfrac12 Z^2
\ \ge\ -\tfrac H2\,W_{\mu_6}(\lfloor H/2\rfloor).
$$
Indeed the mass $\sum_{k=r}^{H-1}1/[k(k+1)]=1/r-1/H$ is at most $1/H$, and all these rows are in the preceding doubling window. This bounds a whole two-dimensional contribution from the **actual measured one-dimensional price on the side**, without a separate estimate for $U$. Across the first boundary at cofactor five an additional signed correlation enters. [Formal upper-half bound](PALRH/OuterBlock.lean) · [A test of extending this rule across that boundary](what-the-fifth-boundary-needs.md)

## Why the two square branches cannot be paid separately

Set $X=H^2$ and take $H\ge3$. In the part containing a prime larger than $H$, that prime is unique. Its signed sum is
$$
L(X)=-\sum_{a\le H}m_a\{\pi(X/a)-\pi(H)\}.
$$
It has the unconditional asymptotic $L(X)=3X/\log^2 X+O(X/\log^3 X)$. The remaining rough squarefree part, made of smaller primes only, has $-3X/\log^2 X+O(X/\log^3 X)$. Both signed amounts grow faster than the required side-length scale. The positive sign of the one-new-prime account is a consequence of the signed old cofactors.

Here are the arithmetic inputs and the computation of the coefficient 3. Unconditional prime-number-theorem and Mertens error estimates give $\pi(x)-\operatorname{li}(x)=O_A(x/\log^A x)$ and $M(x)=O_A(x/\log^A x)$ for each fixed $A$. The Mertens bound passes to $R(x)$ through its sum of $2^a3^b$ dilations. For factors up to $\sqrt x$ use $\log(x/(2^a3^b))\ge(\log x)/2$; the larger factors have total reciprocal mass $O(x^{-1/4})$ by the convergent sum of their reciprocal square roots. [Johnston and Yang on prime counts](https://arxiv.org/abs/2204.01980) · [Unconditional Mertens estimates](https://arxiv.org/abs/2208.06141)

Replacing the prime counts by logarithmic integrals in $-L(X)$ costs $O_A(X/\log^{A-1} X)$ by absolute summation, since $X/a\ge\sqrt X$. The logarithmic-integral sum is exactly
$$
X\int_1^{\sqrt X}\frac{R(u)}{u^2(\log X-\log u)}\,du .
$$
Write $I_h=\int_1^\infty R(u)(\log u)^h\,du/u^2$. These integrals converge absolutely at each fixed $h$ by the preceding bounds. Expanding the denominator through the linear term gives $X(I_0/\log X+I_1/\log^2 X)+O(X/\log^3 X)$; on this interval $\log u\le(\log X)/2$, and the truncated moment tails are smaller than any prescribed inverse-log power. For real $s>1$, $s\int_1^\infty R(u)u^{-s-1}du=1/[(1-2^{-s})(1-3^{-s})\zeta(s)]$. At $s=1$ the right side has a simple zero with derivative $3$. Taking the value and derivative by dominated convergence gives $I_0=0$ and $I_1=-3$. Restoring the minus sign proves the claimed main term. The old-prime amount is $R(X)-L(X)$. The [depth allowance](where-prime-depth-can-stop.md) changes either subtotal by at most $H$; it therefore preserves these leading terms.

## What remains

Pang's PAL supplied the retained frame, RPL-T02 the square shell, and boundary-ledger accounting the instruction to evaluate a loss on the common old and new labels. The square identity is credited above to Huxley and Watt. Landau's one-sign mechanism and the two unconditional analytic bounds are classical. The exact rough-core application, boundary accounting, signed branch comparison and controls were developed on this branch. [Corpus and registered editions](CORPUS-ROUTES.md)

The remaining question can be stated as the lower bound (1) on the actual bounded kernel at integer sides. The displayed two-sided matrix implication and finite row identities are in Lean. The one-sided Landau implication, Fourier range and asymptotic comparison are paper arguments. No estimate establishing (1) for all sides has been obtained.
