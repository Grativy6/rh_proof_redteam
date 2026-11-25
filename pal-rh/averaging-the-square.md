# What averaging the square actually buys

Christopher Daniel Pang and Hearthline · 25 November 2026

The hard cofactor-five boundary can produce a large negative reading from two old sides with individually small walks. We changed what the next square measures and tried the same inputs again. For the same 26,868 assigned signs at side $4{,}194{,}304$, the hard centered form lies between $-6{,}948{,}370$ and $-6{,}941{,}386$. The new centered form lies between $-255.164$ and $-255.163$. There is an all-scale reason: the entire averaged square has a bound in terms of the earlier side walk. A separate Mellin argument connects the averaged target to RH. [Hard boundary experiment](what-the-fifth-boundary-needs.md) · [Exact rational replay on identical inputs](../receipt-archives/check_pal_smoothed_square.py)

## Keep the finite arithmetic and change the threshold weight

Use the rough marks $m_n=\mu(n)[(n,6)=1]$, census $C(u)$, density $\rho=1/3$, and $K(u)=C(u)-\rho u$ from the [square identity](the-signed-matrix-inside-a-square.md). For $X>0$ put
$$
R_2(X)=\sum_{n\le X}m_n(1-n/X)^2,\qquad C_2(t)=\sum_{k\le t}\mathbf1_{\gcd(k,6)=1}(1-k/t)^2.
$$
At $X=H^2$ the complete two-factor calculation is
$$
R_2(X)=2\sum_{i\le H}m_i(1-i/X)^2
       -\sum_{i,j\le H}m_i m_j C_2(X/(ij)).
$$
To check it on paper, give the triple $(i,j,k)$ the weight $(1-ijk/X)_+^2$. At least one of $i,j$ is at most $H$ whenever the term is nonzero. Summing an unrestricted factor against the census uses $m*g=\delta_1$ with $g(k)=[(k,6)=1]$. The overlap gives exactly the displayed matrix. All entries at the square are rational. [Finite threshold identity and the actual squared weights](PALRH/Smoothed.lean)

An upper bound $R_2(H^2)=O_\epsilon(H^{1+\epsilon})$ at every side would suffice for RH. Between squares, $|R_2'(X)|\le2X^{-2}\sum_{n\le X}n=O(1)$ for $X\ge1$. On $\Re s>1$ the Mellin integral of $R_2(X)$ against $X^{-s-1}dX$ equals
$$
\frac{2}{s(s+1)(s+2)}\,
\frac{1}{(1-2^{-s})(1-3^{-s})\zeta(s)} .
$$
The new rational factor has no zero in the relevant half-plane. The one-sided Landau proof in the square paper therefore applies to this target as well. Conversely the classical Mertens bound under RH passes to this positive average by partial summation.

## An earlier side pays for the whole averaged matrix

Write $C_2(u)=\rho u/3+G(u)$. Set $F(u)=u^{-1}\int_0^u K(v)\,dv$. Two integrations of the threshold give
$$
G(u)=\frac2{u^2}\int_0^u(u-v)K(v)\,dv.
$$
If $|K|\le b$, both $|F|,|G|\le b$. For the logarithmic derivative $D=u\,d/du$,
$$
DG=2F-2G,\qquad D^2G=2K-6F+4G .
$$
The second equality holds away from the jumps and almost everywhere. The first logarithmic derivative is locally absolutely continuous, so integrating the second across a jump is legitimate. In particular $|DG|\le4b$ and $|D^2G|\le12b$.

Now take **any real side coefficients** $a_i$, let $A(i)=\sum_{j\le i}a_j$, $U=|A(H)|$ and $L=\sum_{i<H}|A(i)|/i$. On the genuine grid $G_{ij}=G(X/(ij))$, a unit step in $i$ has logarithmic length $\log(1+1/i)\le1/i$. The last row and column differences are bounded by $4b/i$ at their respective indices. A mixed difference across a unit rectangle is bounded by $12b/(ij)$ by integrating the mixed derivative. Apply finite summation by parts first to the columns and then to the rows. It gives the full estimate
$$
\left|\sum_{i,j\le H}a_i a_j G_{ij}\right|
\le bU^2+8bUL+12bL^2.
$$
For $|A(i)|\le c\sqrt i$ through the side, $L\le2c\sqrt H$ and the result is at most $65bc^2H$. The same calculation gives $O_{\epsilon,b}(H^{1+2\epsilon})$ under a side bound $c_\epsilon i^{1/2+\epsilon}$. This is the transfer the hard kernel failed on the reciprocal packets. The finite summation theorem is in Lean; the displayed derivative calculation verifies its hypotheses for this averaged kernel on paper. [Finite matrix transfer](PALRH/Smoothed.lean)

For the actual marks the leading matrix term is the nonnegative square $(\rho X/3)(\sum m_i/i)^2$. Dropping it costs nothing in the **upper** estimate for $R_2$. For example, an earlier side with $|R(i)|\le c\sqrt i$ pays $R_2(H^2)\le 2H+65bc^2H$ at that square. To iterate this statement one must supply that earlier-side hypothesis.

There is a further exact reduction for this particular mask. Let $B_3(v)=v^3-3v^2/2+v/2$. For every $t>0$,
$$
C_2(t)=\frac t9+\frac1{3t}
-\frac1{3t^2}\sum_{d\mid6}\mu(d)d^2 B_3(\{t/d\}).
$$
Expand $K(t)=-\sum_{d\mid6}\mu(d)\{t/d\}$. Its first ordinary integral is a sum of periodic second Bernoulli polynomials plus the constant $\sum_{d\mid6}\mu(d)d/12=1/6$. The second integral of the periodic parts uses $B_3'=3B_2$, $B_3(0)=B_3(1)=0$ and gives the displayed identity. Thus **two** separable matrix terms have favorable signs, the second being $(\sum i m_i)^2/(3X)$. After dropping them, all entries with $ij\le H^{5/3}$ cost at most $O(H\log H)$ even in absolute value: the remaining kernel is $O((ij/H^2)^2)$ and $\sum_{ij\le Z}(ij)^2\ll Z^3(1+\log Z)$. The earlier one-sided budget absorbs this entire product range.

## Run the smoothing backward

Let $F_H(x)$ be the hard integer form and $B(x)$ its unnormalized twice-integrated version. A summand that enters at integer $q$ contributes $(x-q)_+^2$. Its centered second difference at $x$ is twice the midpoint of the hard step. Therefore
$$
B(H^2+1)-2B(H^2)+B(H^2-1)=2F_H(H^2)\qquad(H>1),
$$
because the signed hard jump at $H^2$ vanishes. At side 1024 the left side is **70**, exactly twice the original hard value 35. Reversing the smoothing reinstates the very joint reading whose boundary needed funding. [Formal reversal](PALRH/Smoothed.lean)

There is no general norm argument that converts the small averages back into small raw side walks. For example, at rapidly separated integers $Y$, insert $\lfloor Y^{2/3}\rfloor$ positive unit steps followed by the same number of negative steps; take zero elsewhere. The raw primitive has peaks of order $Y^{2/3}$. Its triangular areas up to $x$ sum to $O(x^{4/3})$ if, for example, each new $Y$ is at least twice its predecessor. The twice-averaged reading is bounded by $2x^{-1}$ times that area, hence $O(x^{1/3})$. The positive square-transfer estimate is valid. Supplying its raw side inputs recursively is a separate task.

## A Gaussian alternative with only a short spectral range

There is a stronger paper reduction if the target itself is allowed a rapidly decreasing tail. Set $\phi(v)=e^{-\pi v^2}$, $L=1+\lfloor\log_2 H\rfloor$, $A=\lceil\sqrt L\rceil$, and $Y=H^2/(2A)$. Use $R_\phi(Y)=\sum_n m_n\phi(n/Y)$. Its Mellin multiplier is $\tfrac12\pi^{-s/2}\Gamma(s/2)$, nonzero in $\Re s>1/2$.

The Gaussian tends to zero faster than every power at the small-$X$ end, so changing the lower integration limit from zero to one adds an entire function. The same triple convolution now leaves terms with both $i,j>H$. Their absolute sum is at most
$$
\sum_{n>H^2}\tau_3(n)e^{-\pi(n/Y)^2}
\le e^{-\pi H^4/(2Y^2)}\sum_{n\ge1}n^2e^{-\pi n^2/(2Y^2)}
=O(1).
$$
Here $\tau_3(n)\le n^2$, the Gaussian sum is $O(1+Y^3)$, and $H^4/(2Y^2)=2A^2\ge 2\log H$. Thus the matrix handoff retains a uniform allowance for the true uninspected tail.

Poisson summation on the two residue classes $\pm1\bmod6$ gives
$$
\sum_{(n,6)=1,\ n\ge1}e^{-\pi(n/t)^2}
=\frac t6+\frac t6\sum_{k\ge1} c_6(k)e^{-\pi(kt/6)^2},
\qquad c_6(k)=2\cos(\pi k/3).
$$
The coefficients for $k\bmod6=0,1,\ldots,5$ are $2,1,-1,-2,-1,1$. The zero-frequency term is again a favorable rank-one square. The Fourier transform of $e^{-\pi x^2}$ in the $e^{-2\pi i x\xi}$ convention is itself. [Poisson summation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/PoissonSummation.html) · [Gaussian normalization](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.html)

For $t=Y/(ij)$, the following two cuts cost $O(1)$ in the **whole quadratic form**, uniformly in $H$. Drop $ij\le H^2/(48L)$ and drop dual indices $k>48L$. On the first range $t\ge12\sqrt L$ since $A\le2\sqrt L$. On the second, $kt/6\ge2\sqrt L$ even at $i=j=H$. In either case factor out $e^{-2\pi L}$ and sum the remaining half-Gaussian, at most $O(1+1/t)$. Multiplication by $t$ and summation over at most $H^2$ pairs costs at most $O(H^4 e^{-2\pi L})$. The cutoff lowers the range of product scales and frequencies; many actual integer pairs can still lie inside the retained region.

Consequently a concrete sufficient condition is a one-sided $-O_\epsilon(H^{1+\epsilon})$ bound on just
$$
\frac Y6\sum_{\substack{1\le i,j\le H\\ij>H^2/(48L)}}\frac{m_i m_j}{ij}
\sum_{k=1}^{48L}c_6(k)\exp\!\left(-\pi\left(\frac{kY}{6ij}\right)^2\right).
$$
It bounds $R_\phi(Y)$ above after restoring the rank-one square, the $O(1)$ allowance and two side sums of size at most $H$. The sampled $Y$ tends to infinity. Each upward step has size at most $O(H/A)=O(\sqrt Y)$; increases of $A$ only make a step smaller. The derivative of the Gaussian-smoothed count is $O(1)$ by absolute summation, so its upper bound transfers from the first sample crossing a given $x$ to all $x$, with the harmless logarithmic factors absorbed in the exponent. Landau's argument then excludes right-side zeros. Conversely RH bounds the Gaussian-smoothed primitive by partial summation and bounds the balanced-out reciprocal square by $O_\epsilon(H^{1+\epsilon})$. This is a criterion on the true side data. A positive scalar Gaussian weight alone does not give a positive-semidefinite product kernel: the two-by-two determinant for $e^{-\lambda u_i u_j}$ is negative at distinct positive $u_i,u_j$.

The Gaussian reduction is a paper proof for the fixed rough frame $P=6$. The [standard-library calculation](../receipt-archives/check_pal_smoothed_square.py) compares outward rational enclosures of the direct and reciprocal Gaussian sums at five rational scales. A changing prime modulus changes the dual spacing. It needs its own estimate before the same spectral cutoff can travel with it.

## Source and unresolved claim

Pang’s RPL and Compactification Costs ask which noise gets removed by changing the receiving boundary and what has to travel back. The fixed square identity is Huxley and Watt’s; Riesz means, Bernoulli polynomials and Gaussian Poisson summation are classical. The side-window transfer, its exact reversal, and the present cuts are derived here for the PAL construction. [Corpus roles](CORPUS-ROUTES.md)

The [balanced Newton handoff](the-balanced-newton-handoff.md) supplies compatible side lists for a different explicit observation and gives a [finite test of its direction](when-a-drop-would-count.md). For the averaged matrix here, the remaining estimate concerns the signed correlations of the true Möbius coefficients in the retained high-side range. No bound closing those correlations for all sides has been obtained. The explicit soft transfer can also be used without inverting it, provided its earlier side inputs are funded independently.
