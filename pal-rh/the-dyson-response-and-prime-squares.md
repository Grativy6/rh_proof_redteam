# The Dyson response and the prime-square bias

Christopher Daniel Pang and Hearthline, 26 November 2026 (New York). The [four-point example and the finite prime sums](../proofs/what-one-doubling-hears-in-the-primes.md) are the reader edition. This note proves the stated equivalences and identifies the inputs used in each direction.

## One aperture and its two observing frames

Set $L=\log 2$, $w(u)=(L-|u|)_+$, and
$$
 K(z)=\int_{\mathbb R}w(u)e^{zu}\,du
 =\left(\int_0^L e^{zt}\,dt\right)\left(\int_0^L e^{-zt}\,dt\right)
 =\frac{e^{Lz}+e^{-Lz}-2}{z^2}.
$$
The overlap of two intervals of length $L$ is $w$ at their translation distance. The value at zero is $L^2$. For $\Re z>0$ the factor $(e^{Lz}-1)^2$ is nonzero. For $z=i\gamma$ the two integrals are complex conjugates. This preserves the amplitude of every possible off-line pole and gives a nonnegative real weight on every on-line frequency.

Define $T(x)=\sum_{n\ge2}\Lambda(n)n^{-1/2}w(\log(n/x))$ and let $P(x)$ be its restriction to primes. All these sums are finite. Put $c=K(1/2)=4(\sqrt2+1/\sqrt2-2)$. Let $\rho$ run through the nontrivial zeros with multiplicity, and write $z_\rho=\rho-1/2$. The two-frame response
$$
 Z(u)=\sum_\rho K(z_\rho)e^{u z_\rho}
$$
is real and even by the two zeta symmetries. It converges absolutely for each fixed real $u$ since $K(z_\rho)=O((1+|\Im\rho|)^{-2})$ and the zero count through height $t$ is $O(t\log(2t))$.

For $x>2$ the explicit formula gives
$$
 T(x)=c\sqrt x-Z(\log x)-E(x),\qquad
 E(x)=\sum_{m\ge1}K(-2m-1/2)x^{-2m-1/2}>0 .
$$
For a general exponent $\alpha$ and aperture $b>0$, the input is $f(t)=t^{-\alpha}(b-|\log(t/x)|)_+$ with Mellin transform $x^{s-\alpha}K_b(s-\alpha)$, where $K_b$ is the same expression with $b$ in place of $L$. When $x>e^b$ the support lies strictly above one. The pole supplies $x^{1-\alpha}K_b(1-\alpha)$. The archimedean integral in the multiplicative explicit formula expands using $t/(t^2-1)=\sum_{m\ge0}t^{-2m-1}$. The term at zero cancels the reflected pole contribution, leaving precisely the negative even integers in $E$. A smooth convolution in log scale approximates this continuous triangular test: it preserves compact support away from one for small smoothing radius, its Mellin multiplier is uniformly bounded on the critical strip, and the $O((1+|\Im\rho|)^{-2})$ majorant permits passage to the limit. At a support endpoint the tent itself vanishes. [Bombieri, §2, Guinand–Weil explicit formula](https://www.bdim.eu/item?fmt=pdf&id=RLIN_2000_9_11_3_183_0) · [Connes and Consani, Appendix B, archimedean normalization](https://alainconnes.org/wp-content/uploads/Selecta.pdf)

Thus under RH, $Z$ is the Fourier transform of a finite positive measure of mass $Z(0)$. In particular $|Z(u)|\le Z(0)$. The two-observer matrix with diagonal $Z(0)$ and off-diagonal $Z(u)$ is positive semidefinite. To test it one needs only the sum and the difference of the two observing amplitudes.

## The price at zero can be read without a prime

At $x=1$ use the full formula with the self-dual test $f(t)=t^{-1/2}w(\log t)$. Its prime terms vanish: 2 is the first prime and its logarithm is an endpoint. The pole and the continuous term at infinity give
$$
 Z(0)=2c-(\log(4\pi)+\gamma_E)L+L\log3+
       \int_0^L \frac{L-e^{s/2}(L-s)}{\sinh s}\,ds .
$$
Indeed the real-place integral over $t>2$ is $2L\int_2^\infty dt/(t^2-1)=L\log3$. On $1<t<2$ put $s=\log t$. Log-scale smoothing can also be used at this center. The smoothing is uniformly Lipschitz, so the subtracted integrand at $t=1$ has an integrable majorant. This evaluation makes no RH assumption.

The integral is enclosed by factoring its integrand as
$$
 \frac{s}{\sinh s}
 \left(e^{s/2}-\frac L2\int_0^1e^{st/2}\,dt\right).
$$
The first positive factor decreases. The second is positive and increases, as seen by differentiating and using $L<1$. At the two endpoints of each of 32,768 panels, integer Taylor enclosures therefore bound the entire panel. The result is
$$
 0.127106908\ \le Z(0)\le\ 0.127115434 .
$$
An independent, looser conditional estimate uses the Hadamard product of $\xi$. The difference of its logarithmic derivatives at 1 and 0 is $\sum_\rho1/[\rho(1-\rho)]=2+\gamma_E-\log(4\pi)$. To see the constant, reflection doubles $\xi'(1)/\xi(1)$; insert the Laurent expansion at the pole and $\psi(1/2)=-\gamma_E-2\log2$. Under RH the sum is $\sum_\rho|\rho-1|^{-2}$. Since $K(i\gamma)\le L^2$ and $\gamma^2K(i\gamma)\le4$, this gives $Z(0)\le(4+L^2/4)(2+\gamma_E-\log(4\pi))<0.191$. [Bombieri and Lagarias, the zero-sum and logarithmic-derivative identities](https://websites.umich.edu/~lagarias/doc/bombieri.pdf) · [Directed constants](../receipt-archives/2026-11-26-pal-dyson-octave.json)

For $x=j^2\ge9$, $E(x)\le (2/9)^{5/2}/[(5/2)^2(1-(2/9)^2)]<0.004$. RH therefore gives the fifth-unit two-sided bound at every $j\ge3$ with room to spare. The four terms at $j=2$ are evaluated directly.

## Why a bounded error on either side reaches the actual zeros

For $\Re s>1/2$ the Euler product and absolute convergence give
$$
 \int_1^\infty (T(x)-c\sqrt x)x^{-s-1}\,dx
 =-K(s)\frac{\zeta'(s+1/2)}{\zeta(s+1/2)}-\frac{c}{s-1/2}.
$$
The lower integration limit is exact because $T(x)=0$ for $x\le1$. The pole at $s=1/2$ cancels because $K(1/2)=c$. The right side is regular at every positive real $s$ by the alternating zeta series and the simple pole of zeta. An off-line zero with real part $>1/2$ gives a pole with a nonzero residue, even when the zero has multiplicity greater than one.

Suppose either side of the fifth-unit estimate holds on every square. The tent is Lipschitz with constant one in $\log x$. On $j^2\le x<(j+1)^2$ the distance in log scale is at most $2/j$. The crude bound $\Lambda(n)\le\log n$ gives $\sum_{x/3<n<3x}\Lambda(n)/\sqrt n=O(\sqrt x\log(2x))$. The finite initial cases are harmless. Consequently the corresponding one-sided centered error on all reals is $O(\log(2x))$.

Choose a large positive multiple of $1+\log x$ and subtract the upper-bounded error from it (or add the lower-bounded error). This nonnegative function has a Mellin transform regular on the positive real axis. A finite real abscissa of convergence must be singular for a nonnegative Mellin integral: expanding at a real point just to its right and moving left makes the logarithmic-moment terms nonnegative, so an analytic Taylor extension across the abscissa would contradict it by monotone convergence. The integral is therefore holomorphic for $\Re s>0$. The detected off-line pole is impossible. Reflection about $1/2$ finishes the implication. The same argument shows that the pair test $|Z(\log j^2)|\le Z(0)$ for each $j\ge2$ is equivalent on paper to RH, and either one of those two inequalities suffices. The local matrix at a single shift is only a measurement at that shift.

The formal analytic bridge uses $f(s)=(s-1)\zeta(s)$ with its value at 1 filled in. If the centered prime-power response extends holomorphically, it gives an identity $A f'=B f$ on the full right half-plane, with $A=(s-1)K(s-1/2)$. At a hypothetical zero of positive order, $A$ is nonzero and differentiation lowers the order by one, whereas the right side has at least the original order. The independent challenge fixes the input series on $\Re s>1$ using stock von Mangoldt. [Lean proof](PALRH/DysonOctave.lean) · [Independent fixed challenge](checks/dyson-response/DysonChallenge.lean)

## Proving the primes-only statement is equivalent

For every square the repeated powers are nonnegative. Their total is bounded uniformly without RH. For squares use $\vartheta(y)=\sum_{p\le y}\log p\le3y$. This follows by bounding the primes in $(n,2n]$ by the central binomial coefficient and summing over successive powers of two. For powers of order at least three their total is $O(x^{-1/6}\log^2(2x))$. Hence an upper bound $P(j^2)\le cj$ gives a constant upper bound on the *full* centered response. The argument above yields RH.

For the other direction we give explicit coverage, since the claim concerns **every** square. Let $S_2(j)$ denote the prime-square contribution to $T(j^2)$. Compare it with
$$
 A(j)=2\sum_{n\ge2}\frac{\Lambda(n)}n [L/2-|\log(n/j)|]_+ .
$$
The terms where $n$ is prime are precisely $S_2(j)$. At $j\ge32768$, apply the same explicit formula to $\alpha=1$, $b=L/2$. The main term is $2b^2=L^2/2$. Under RH the nontrivial zero contribution has absolute value at most
$$
 2(e^{b/2}+e^{-b/2}+2)\,(2+\gamma_E-\log(4\pi))/\sqrt j<0.5/\sqrt j .
$$
The trivial-zero terms are at most $2\sum_{m\ge1}(\sqrt2/j)^{2m+1}/(2m+1)^2<1/j$ in that range.

The extra terms $A(j)-S_2(j)$ come from bases raised to at least the second power. Using $\vartheta(y)\le3y$ gives
$$
 A(j)-S_2(j)\le
 \frac{3\sqrt2L}{j}\big[(\sqrt2j)^{1/2}
                       +\log_2(\sqrt2j)(\sqrt2j)^{1/3}\big].
$$
This is at most $3(222+16\cdot37)/32768<0.075$ for all $j\ge32768$. To check monotonicity divide each summand by $j$ first; both $j^{-1/2}$ and $j^{-2/3}\log(\sqrt2 j)$ decrease here. Thus $S_2(j)>0.16>Z(0)$, and $P(j^2)<cj$.

For $2\le j<32768$ a directed sieve of the prime squares gives $S_2(j)>0.128$ apart from **4 and 9**. Direct addition at these two exceptional roots gives $P(16)-4c$ between −0.281678 and −0.281677, and $P(81)-9c$ between −0.311309 and −0.311308. This completes the necessity proof. The arithmetic record also checks the looser threshold 0.191 through 99,999 and evaluates all nine exceptions to that comparison. These finite checks contribute to the implication *from* RH. They do not establish the primes-only inequality at unbounded heads independently. [Sieve, directed logs and separate small-head additions](../receipt-archives/check_pal_dyson_window.py)

## A shortfall that must recur, unconditionally

The diagonal is also a sharp obstruction. Under RH write $Z(u)=\sum_\gamma c_\gamma e^{i\gamma u}$ with $c_\gamma=K(i\gamma)\ge0$ and $\sum c_\gamma=Z(0)<\infty$. On any finite list of ordinates there are arbitrarily large integers $m$ for which all phases $e^{2imL\gamma}$ come back arbitrarily close to one. This is simultaneous approximation on a finite torus. For an elementary proof, pigeonhole the first $Q^r+1$ points in a partition into $Q^r$ boxes for $r$ frequencies. As $Q$ increases, the resulting return times are unbounded, or one is an exact return and all its multiples work. Take increasing finite lists and let the total omitted weight tend to zero. No rational independence of the ordinates is required.

It follows that $Z(2mL)\to Z(0)$ on a sequence $m\to\infty$. More generally $Z(u+2mL)\to Z(u)$ there for every fixed $u$. The trivial-zero term tends to zero. Since also $|Z(u)|\le Z(0)$, RH implies
$$
 \liminf_{j\to\infty}[T(j^2)-cj]=-Z(0),\qquad
 \liminf_{j\to\infty}[P(j^2)-cj]=-Z(0)-L^2/2 .
$$
In each case the infimum limit is attained along a subsequence of the ordinary roots $j=2^m$. The second equality uses the independently earned prime-square limit and decay of higher powers.

If RH fails, a finite eventual lower bound for *either* centered reading would imply RH by the pole argument. Its liminf must then be $-\infty$. A finite eventual upper bound would give the same contradiction, so its limsup is $+\infty$. We obtain an unconditional statement in both cases: **arbitrarily large integer squares have full prime-power shortfall greater than 0.127, and arbitrarily large integer squares have primes-only shortfall greater than 0.367.** One cannot close the proof by demanding a uniformly tighter reading than the actual diagonally returning signal permits.

There is also an unconditional surplus. Direct prime arithmetic at root 565 gives $T(565^2)-565c\ge0.07565665$. By the explicit formula and $E>0$, $-Z(2\log565)$ exceeds that value. Under RH the translations above reproduce this signed amplitude at arbitrarily large roots $565\cdot 2^m$. If RH fails, the upper excursions are unbounded on the full sequence of squares. Thus $T(j^2)-cj>0.07565$ for arbitrarily large roots without assuming RH. The dichotomy gives existence on the square heads; the dyadic subsequences in this argument use RH.

## What the following prime powers carry

For each fixed $k\ge2$, the contribution of $p^k$ at head $x$ is asymptotic to
$$
 \frac1k K(1/k-1/2)\,x^{1/k-1/2}.
$$
Partial summation against the prime number theorem on the fixed-ratio interval $p\asymp x^{1/k}$ gives the integral. Substitute $t=p^k$, then $t=xe^u$. Powers of order at least $k+1$ contribute $O_k(x^{1/(k+1)-1/2}\log^2(2x))$, by counting all candidate bases. After the actual squares have been removed, the next nonvanishing scale is therefore $x^{-1/6}$ and its coefficient is $K(1/6)/3$. Keeping track of each exponent explains both the permanent square bias and the decaying higher-power remainder.

At a boundary a mark can have zero weight and still determine what happens on the next step. As a function of $\log x$, the contribution of $p^k$ starts rising at $\log(p^k)-L$, turns at $\log(p^k)$ and stops falling at $\log(p^k)+L$. The slope changes in the proportions $+1,-2,+1$. At $x=4$, 8 has weight zero and begins to enter as the head increases. At every dyadic knot $x=2^k$ with $k\ge2$, three powers of 2 meet. Their net slope change is $L\,2^{-k/2}(\sqrt2+1/\sqrt2-2)>0$. This is an actual trace left at a zero-weight edge.

## A direct attempt to pay the remaining prime bill

The factorial identity $\log(\lfloor t\rfloor!)=\sum_n\Lambda(n)\lfloor t/n\rfloor$ is an exact possible source. A nonnegative combination of these divisor readers is nonincreasing as a function of its input label. Our weight $v_x(t)=t^{-1/2}w(\log(t/x))$ increases on $(x/2,x)$ and decreases on $(x,2x)$. A nonnegative nonincreasing upper envelope must be at least $L/\sqrt x$ everywhere below $x$. Even the best such envelope spends an extra continuous mass of
$$
 L\sqrt x-\int_{x/2}^x \frac{\log(2t/x)}{\sqrt t}\,dt
 =(4-2\sqrt2-L)\sqrt x.
$$
By the prime number theorem the same leading excess applies to that envelope priced against prime log-masses. A nonnegative nonincreasing lower envelope of this compactly supported window is identically zero. A single signed central-binomial row $\lfloor2x/d\rfloor-2\lfloor x/d\rfloor$ also fails as a coefficientwise upper comparison: at $x=4,d=3$ it assigns zero to a prime with strictly positive tent weight. A successful factorial argument would have to explain how its signed cancellations return the correct weight on these actual labels.

Changing the width gives another exact falsifier. At square 100 take log half-width $b=2\log(101/100)$. Only prime 101 lies in the window. Its contribution is $\log(101)\log(101/100)/\sqrt{101}$ while the continuous price is $40(101/100+100/101-2)=2/505$. The prime contribution strictly exceeds that price. Thus applying the primes-only upper rule at arbitrary chosen widths already fails on a single ordinary prime. The fixed one-doubling aperture in the theorem has mathematical content. [Outward comparison](../receipt-archives/check_pal_dyson_window.py)

There is a separate unconditional interpolation gain. Away from its finitely many corners on each compact interval,
$$
 \frac{d}{dj}\big[P(j^2)-cj\big]
 =\frac2j\left[\sum_{j^2<p\le 2j^2}\frac{\log p}{\sqrt p}
 -\sum_{j^2/2<p\le j^2}\frac{\log p}{\sqrt p}\right]-c=o(1)
$$
as the real variable $j$ tends to infinity. Partial summation and the ordinary prime number theorem supply the leading terms $2j(\sqrt2-1)$ and $2j(1-1/\sqrt2)$. Their difference with its prefactor is exactly $c$. Thus a fixed negative margin at one selectable sample in each bounded-width interval of roots would propagate to every sufficiently late square. The outstanding work is an upper bound for the genuine prime sum on sufficiently many such roots, independent of RH.
