# What a positive reference must lose

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). This tests a possible shortcut in our independent PAL construction. Choose a positive reference profile, generate its divisor readings, then charge all differences by magnitude. Pang’s question about where a claim gets paid led us to compare the resulting lower bound directly with the true arithmetic.

**The shortcut fails for every nonnegative profile, even one chosen afresh at every head.** At fourth-power side $X=(10^6)^4$, it loses at least **2,671,673,470,616,640** relative to the true reading in the normalization below. The asymptotic loss is at least a positive constant times $X$. On the actual signed source there is a workable alternative. All negative contributions in the first 40 million inverse arguments can be paid simultaneously at every head with at most **one thirty-sixth** of one specified positive partner per negative contribution.

## The exact bill

Set $T=2X$ and $R(y)=[(y-1)_+-(y/2-1)_+]/2$. Use $a(v^2s)=v\mu(s)$ for $v=2^i3^j$, $(s,6)=1$, with $a=0$ on other labels. The true target is $V_T=\sum_d a(d)R(T/d)=XS_1(X)/2$. All sums on an integer label beyond $T$ are zero. For a proposed reference $f_T(n)$, group its powers of 3 into one function
$$
 u(d)=\sum_{j\ge0}f_T(3^jd),\qquad
 (Du)(d)=\sum_{(k,6)=1}u(kd),\qquad E(d)=R(T/d)-(Du)(d).
$$
The original odd multiples of $f_T$ appear exactly once in $Du$. Any signed $u$ of this finite support can be represented, by setting $f_T(d)=u(d)-u(3d)$. A nonnegative $f_T$ implies $u\ge0$.

The known source is $P=\sum_v v\,u(v^2)$. Indeed at $v^2s$ the inner divisor coefficients sum to $\sum_{k\mid s}\mu(k)$ for rough $s$, which is 1 at $s=1$ and 0 otherwise. Consequently $V_T=P+\sum a(d)E(d)$. The lower bound obtained by unsigned payment is $C_T=P-\sum|a(d)E(d)|$. There is an exact measure of what it loses,
$$
 V_T-C_T=2\sum_d [a(d)E(d)]_+ . \tag{1}
$$
A negative correction is charged once at its actual cost. A positive correction changes from a credit to a debt. This identity includes any increase a proposed reference might buy in its own source.

Write $m(k)=\mu(k)\mathbf1_{(k,6)=1}$. The unique inverse of $D$ on the finite multiples of $d$ is $\sum_k m(k)E(kd)$. The inverse value forced by the true target is
$$
 U(y)=\sum_{k\le y}m(k)R(y/k)=\frac{y}{4}S_0(y/2),\qquad
 \sum_k m(k)E(kd)=U(T/d)-u(d). \tag{2}
$$
Here $S_0$ is the original rough Möbius reading before the square pass. The inverse follows by grouping products and using $\sum_{k\mid s}\mu(k)$. [Divisor inverse, prime sign, actual raw reading and margin in Lean](../pal-rh/PALRH/ReferencePrice.lean)

## A negative interval the profile has to answer for

The calculation gives $U(y)<-16$ throughout the real interval
$$
 A=33{,}400{,}000\le y\le35{,}300{,}000=B .
$$
Take any prime $q>B$ with $T/q$ in this interval. Each nonzero term on the left of (2) now uses a physical integer $kq$ with $k\le B$. Its actual sign is $a(kq)=-m(k)$. Therefore the sum of the **signed** residual contributions on these same integers equals $u(q)-U(T/q)$. If $u(q)\ge0$, the positive contributions among them exceed 16. The sets for distinct such primes are disjoint, since $q$ is the largest prime at every one of its occupied labels. Equation (1) loses at least 32 per prime, even when other parts of the profile have arbitrary signs.

| Fourth-power root | Primes in $[\lceil T/B\rceil,\lfloor T/A\rfloor]$ | Guaranteed loss in (1) |
| ---: | ---: | ---: |
| 10,000 | 1,597,281 | 51,112,992 |
| 100,000 | 10,965,097,912 | 350,883,133,184 |
| 1,000,000 | 83,489,795,956,770 | 2,671,673,470,616,640 |

At the last head the loss exceeds $2671\sqrt X$. This finite comparison is relative to $V_T$. It does not require an estimate for the size or sign of $V_T$ at that head. [Endpoint counts and arithmetic record](../receipt-archives/2026-11-25-pal-reference-price.json)

The obstruction is actually linear. Allow a squarefree $d$ with an odd number of prime factors, every one larger than $B$. Again $a(kd)=-m(k)$ on the occupied labels. The factors of $kd$ of size greater than $B$ recover $d$ uniquely, so all these sets also remain disjoint. The density of squarefree integers with every prime factor larger than $B$ is
$$
 \Delta_B=\prod_{p\le B}(1-1/p)\prod_{p>B}(1-1/p^2).
$$
Finite sieving followed by the bound $\sum_{p>Z}1/p^2\to0$ gives the product. Half of this density has either parity. To justify the half, remove the finitely many primes up to $B$ from the Möbius summatory function by convolution with integers supported on those primes. Their reciprocal series converges. The ordinary estimate $\sum_{n\le z}\mu(n)=o(z)$ and dominated convergence give $o(z)$ for the restricted signed sum as well. The fixed band has length $T(1/A-1/B)$. It follows that **every** sequence of nonnegative profiles satisfies
$$
 \liminf_{T\to\infty}\frac{V_T-C_T}{T}
 \ \ge\ 16\Delta_B(1/A-1/B)>8\cdot10^{-10}.
$$
The finite small-prime product was bounded by integer arithmetic and the remaining product is at least $1-1/B$. Since $\sum a(n)/n=0$ with inverse-logarithmic tails, $V_T=o(T)$. Thus the proposed lower bound goes negative by a linear amount at all sufficiently late heads. Even if only the prime sites are inspected, any profile producing a square-root lower floor must have $u(q)<-16+\epsilon$ at a proportion tending to one of the primes in the displayed band, for every fixed $\epsilon>0$. This follows from (1), (2), the prime number theorem and $V_T\ll_D T/\log^D T$ for all fixed $D$. [Cofactor tails for this stream](why-one-large-prime-leaves-nine.md) · [Ordinary prime count](https://dlmf.nist.gov/27.12) · [Unconditional Mertens estimate](https://arxiv.org/abs/2208.06141)

## Allow the signs to travel

Two less restrictive problems have exact answers. If only $P\ge0$ is required, the least possible unsigned bill at a fixed head is $[-V_T]_+$. Set $u(d)=U(T/d)$, then add $[-V_T]_+$ at $d=1$. If each physical source $u(v^2)$ must be nonnegative, the minimum is instead
$$
 B_{\rm rays}(T)=\sum_v v[-U(T/v^2)]_+ . \tag{3}
$$
For each fixed $v$ the signed error on its rough labels is $v[U(T/v^2)-u(v^2)]$. These sets are disjoint. Their negative parts lower-bound the bill. Equality follows by keeping the exact inverse at all other labels and replacing $U(T/v^2)$ by its positive part. A correction at $v^2$ affects just that label under $D$, since a multiplier coprime to 6 dividing $v^2$ can only be 1. In both minimizations all the corrections at equality enter with a negative sign, giving $C_T=V_T$. Optimizing over such fitted signed profiles can therefore return the original unanswered number exactly.

Even the minimum in (3) outgrows $\sqrt T\log T$. For a fixed $K$, the normalized contribution from $1\le T/v^2\le K$ tends to
$$
 \frac{1}{\log4\log9}\int_1^K \frac{[-U(y)]_+}{y^{3/2}}\,dy .
$$
To see this, put $t=\log T$ and sum the compactly supported function $[-U(e^z)]_+e^{-z/2}$ at $z=t-i\log4-j\log9$. Periodize in $i$ with period $\log4$. There are $t/\log9+O_K(1)$ full rows in $j$. Their mean tends to the period mean, uniformly in the starting phase. For each nonconstant Fourier exponential this follows from the bounded geometric sum since $\log9/\log4$ is irrational. Continuous approximation above and below handles the two interval endpoints. The [earlier sign-area proof](../pal-rh/what-the-two-signs-cost-together.md) gives $\int_{1/2}^Z [ -S_0(x)]_+\,dx/\sqrt x\to\infty$. Changing variable $y=2x$ in (2) proves the assertion by taking $K$ arbitrarily large after the limit in $T$. In particular positive contributions from any fixed bounded range of inverse arguments have only $O_K(\sqrt T\log T)$ available and cannot cover all negative rays at every late head.

## An actual payment that survives the obstruction

For $1\le y\le12{,}000{,}000$ the true $U(y)$ is nonnegative. On the whole range $1\le y\le40{,}000{,}000$ it stays above $-32$. Suppose a term $vU(y)$ in that range is negative, where $y=T/v^2$. Send it to the actual smooth root $2304v$, since $2304=2^8 3^2$. Its inverse argument $y/2304^2$ lies between 2 and 8. On that short interval $U(z)\ge1/2$. Only $1,5,7$ can enter (2), and checking the endpoints of the affine pieces proves the bound. The partner offers at least $1152v$. Spending at most **one thirty-sixth** covers $32v$. Distinct negative inputs have distinct partners, and every partner has positive sign. Thus all negatives in the stated range are paid simultaneously at every real head.

There is a quantitative true credit left over. For each $3^j\le\sqrt X$, take the largest $v=3^j2^i\le\sqrt X$. All these distinct $v$ lie in $(\sqrt X/2,\sqrt X]$, with $2\le T/v^2<8$. At least $35/36$ of each of their positive contributions remains. For $K=40{,}000{,}000$ and $X\ge1$ this gives
$$
 \sum_{v:\,T/v^2\le K} vU(T/v^2)
 \ \ge\ \frac{35}{144}\sqrt X\,\bigl(1+\lfloor\log_3\sqrt X\rfloor\bigr).
$$
The actual limiting credit divided by $\sqrt T\log T$ lies between **1.06195200 and 1.06195207**. Use the same period mean with $U$ in place of its negative part. The integral can be evaluated from three finite moments. For $h=\lfloor K/2\rfloor$ write $M_n=\sum_{k\le n}m(k)$, $s_n=\sum_{k\le n}m(k)/k$ and $b_n=\sum_{k\le n}m(k)/\sqrt k$. Integration of the two linear pieces of $R$ gives
$$
 \int_1^K U(y)y^{-3/2}\,dy
 =\sqrt K(s_K-s_h/2)+(M_K-M_h)/\sqrt K-2b_K+\sqrt2\,b_h .
$$

The next RH obligation on this route is to bound the signed sum of the **remaining** $vU(T/v^2)$ at each sufficiently late $X=j^4$, after crediting the displayed amount. A further fixed $C\sqrt X$ of debt is affordable. The Lean theorem splits the actual reading at this inverse cutoff and transfers such bounds to stock Mathlib RH. [Exact split and conditional implication](../pal-rh/PALRH/ReferencePrice.lean)

## Arithmetic replay

The function $U$ is affine between consecutive integers. The C++ replay encloses every integer endpoint through 40 million using two formulas. The first evaluates $4U(n)=2ns_n-2M_n-ns_{\lfloor n/2\rfloor}+2M_{\lfloor n/2\rfloor}$. The second integrates the slope changes $[m(n)-\mathbf1_{2\mid n}m(n/2)]/(2n)$ starting at $U(1)=0$. A directed bound on each reciprocal uses integer division at scale $2^{80}$. For $b_n$ the initial square-root estimate is corrected and bounded by integer squares. The Python replay checks finite reference games by exact fractions, including signed targets where the different minima are genuinely positive. [Endpoint scan](../receipt-archives/reference_obstruction.cpp) · [Exact reference games and credit calculation](../receipt-archives/check_pal_reference_prices.py)
