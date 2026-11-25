# What the ordinary primes still owe

Christopher Daniel Pang’s PAL research program, 25 November 2026. RPL’s square cut distinguishes a new prime from another visit to an old prime. BLA asks for the cost of carrying each visit across the same boundary, and DARK for what remains after subtracting a known response. We apply those questions to the [signed area that a zeta zero must charge](what-the-two-signs-cost-together.md). The log weights below come from the classical von Mangoldt identity. [Corpus and editions](CORPUS-ROUTES.md)

**Every repeated prime power can be paid for at once.** We can also remove any fixed list of small primes and a range of simple primes that grows with the side. The remaining measurement compares ordinary primes with the continuous counting weight on precisely the same older values of the arithmetic edge. Its maximum and its accumulated magnitude each recover the same power exponent as the original problem.

## Where the first repeated visit goes

As before, $m(n)=\mu(n)\mathbf1_{(n,6)=1}$, $w(v)=1$ through 1, $2-v$ through 2, and zero thereafter. Write $S(x)=\sum_n m(n)w(n/x)/n$ for $x>0$. It is zero up to $1/2$. A prime occurrence at multiplier $r=p^k$ reads the genuine earlier side $S(x/r)$ and contributes $(\log p) S(x/r)/r$.

At side $x=13$, the only repeated prime multiplier inside $2x=26$ is $5^2=25$ in this rough frame. Its old side is $13/25$. Only the mark 1 is visible there, with taper $2-25/13=1/13$. The entire repeat contribution is therefore **$\log(5)/325$**. [Finite arithmetic and general coefficient identity](PALRH/PrimeRenewal.lean)

Set $\Lambda_6(p^k)=\log p$ for $p\ge5$, $k\ge1$, and zero elsewhere. For Dirichlet convolution, $m*g=\delta_1$ with $g(n)=\mathbf1_{(n,6)=1}$. Multiplication of a coefficient by $\log n$ obeys the product rule because $\log(ab)=\log a+\log b$. Applying it to $m*g$ and using $\sum_{d\mid n}\Lambda(d)=\log n$ gives $m(n)\log n=-(m*\Lambda_6)(n)$. On multiplying by the actual taper, this is the finite identity
$$
\log x\, S(x)+\sum_{p\ge5,\,p^k\le2x}\frac{\log p}{p^k}S(x/p^k)
=\sum_{n\le2x}\frac{m(n)}n w(n/x)\log(x/n).
$$
The sums over powers here and below take $p$ prime and $k\ge1$ unless restricted. [Classical divisor identity in the pinned Mathlib source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean)

## Compare the prime clock with the continuous clock

Put $U(x)=\sum_{n\le x}m(n)/n$, and $J(x)=x^{-1}\int_0^x U(t)\,dt$. Then $S(x)=\int_1^2 U(vx)\,dv=2J(2x)-J(x)$, so $J(x)=\sum_{k\ge1}2^{-k}S(x/2^k)$. At fixed $x$ this last sum ends. For the untapered $U$, termwise integration gives $\sum_{n\le x}m(n)\log(x/n)/n=\int_1^x U(x/t)\,dt/t$ for $x\ge1$. Extend that integral by zero below 1. Average the resulting log equation at $vx$ for $1\le v\le2$. The extra average of $\log v\,U(vx)$ equals $2\log2\,J(2x)-\int_1^2 J(vx)\,dv$ by integration by parts.

Choose any fixed $R\ge1$. Write $u=\log(2x)$ and $Y=\max(R,(u/80)^2)$ for $x\ge1/2$. The discrepancy left after removing small multipliers is
$$
P_R(x)=\int_{Y<t\le2x} S(x/t)\frac{dt}{t}
 -\sum_{\substack{Y<p\le2x\\p\ge5}}\frac{\log p}{p} S(x/p).
$$
Both quantities are zero when the range is empty. Write $E_R(x)$ for the same difference on the complementary range $1\le t\le\min(Y,2x)$, $Q(x)$ for the sum over $p^k\le2x$ with $k\ge2$, and $K(x)=\int_1^2 J(vx)\,dv-\log2\,J(x)$. The recovered equation is
$$
u S(x)=P_R(x)+E_R(x)-Q(x)+K(x). \tag{1}
$$
Each $J(vx)$ in $K$ uses only $S(vx/2^k)$ at arguments $\le x$.

There is another way to read precisely the remaining signed measurement. Put
$$
B_R(t)=\log(t/Y)-\sum_{Y<p\le t,\;p\ge5}(\log p)/p,\qquad
D(y)=\sum_{y<n\le2y}m(n).
$$
Here $Y$ stays fixed at the chosen input $x$. Since $dS(x/t)/dt=-D(x/t)/x$ off its corners, integration by parts gives
$$
P_R(x)=\frac1x\int_Y^{2x} B_R(t)D(x/t)\,dt \quad (Y<2x). \tag{2}
$$
Both terms use the very same reciprocal arguments. The lower boundary term vanishes at $Y$ and the upper one at $S(1/2)=0$. This formula retains the cofactor sign wherever the prime count overshoots or undershoots its continuous clock.

## What can already be afforded

Only elementary prime counting is needed for the following allowances.

- Let $\theta(T)=\sum_{p\le T}\log p$. The central binomial coefficient gives $\theta(2n)-\theta(n)\le2n\log2$, hence $\theta(T)\le4T$ by summing over powers of 2. Partial summation gives $\sum_{p\le T}\log p/\sqrt p\le8\sqrt T$. The matching continuum has mass at most $2\sqrt T$. [Formal square-root weight bound](PALRH/PrimeRenewal.lean) · [Mathlib’s Chebyshev bounds](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean)
- The repeat weights at critical scaling have cumulative mass
$$
\sum_{p\ge5,\,k\ge2,\,p^k\le T}\frac{\log p}{p^{k/2}}
=\tfrac12\log T+O(1)\quad(T\ge1),
$$
with upper bound $\tfrac12\log T+27$. For squares, take $p\le\sqrt T$. The identity $\sum_{d\le N}\Lambda(d)\lfloor N/d\rfloor=\log(N!)$ and $\psi(N)\le12N$ give $\sum_{d\le N}\Lambda(d)/d\le\log N+12$. The bound on $\psi$ follows by summing $\theta(N^{1/k})$ and using $\log_2 N\le2\sqrt N$. Conversely $\log(N!)/N\ge\log N-1$, and the harmonic contribution of $k\ge2$ is bounded by $\sum_{n\ge2}\log n/[n(n-1)]$. Thus the square term has the stated leading coefficient. Powers $k\ge3$ cost at most $(1-2^{-1/2})^{-1}\sum_{n\ge2}\log n/n^{3/2}<15$, by integral comparison. The two omitted primes change only the constant in the asymptotic. [Finite floor proof of the square upper allowance](PALRH/PrimeRenewal.lean)
- Set $M(X)=\sup_{1/2\le x\le X}\sqrt x\,|S(x)|$. The dyadic expression for $J$ bounds $\sqrt x\,|K(x)|$ by $C_K M(X)$, with $C_K=(1+\sqrt2)\{2(\sqrt2-1)+\log2\}<4$. The identical factor bounds its accumulated absolute cost, by substituting $y=vx/2^k$ before summing $2^{-k/2}$.

Define $N_R(X)=\sup_{1/2\le x\le X}\sqrt x\,|P_R(x)|/(1+\log(2x))$. In (1) the normalized magnitude of the three removed terms is at most
$$
(5u/8+C_R)\,M(X),\qquad C_R=32+10\sqrt R .
$$
Indeed the simple-prime and continuum mass is at most $10\sqrt R+u/8$, repeats contribute $u/2+27$, and the average contributes less than 4. For $u\ge8C_R$, division by $u$ leaves a fraction at most $3/4$ of $M(X)$ and at most $2N_R(X)$ from the measured term. The bounded initial interval has a finite maximum depending on $R$. Taking the supremum proves
$$
M(X)\ll_R 1+N_R(X),\qquad N_R(X)\ll_R M(X). \tag{3}
$$
This is a bound at every cutoff on the actual arithmetic. It assumes no decay law for the old sides. The repeated terms have nonzero values. Their combined allowance leaves a strict margin in the same inequality.

## The accumulated discrepancy also suffices

For $U_0=\log(2X)$ define
$$
A(U_0)=\int_{1/2}^X |S(x)|\,\frac{dx}{\sqrt x},\qquad
P(U_0)=\int_{1/2}^X |P_R(x)|\,\frac{dx}{\sqrt x},\qquad
I(U_0)=\int_0^{U_0} A(v)\,dv .
$$
The log-weighted area on the left of (1) is $L(U_0)=U_0 A(U_0)-I(U_0)$.

For the small simple multipliers, change variables $x=ty$ before adding the absolute costs. Multipliers $t\le R$ cost at most $10\sqrt R\,A(U_0)$. On the remaining small range $\sqrt t\le u/80$ and $\log t\le u/2$, so $\sqrt t\le\log(2y)/40$. At fixed $y$ the eligible prime and continuum mass is at most $10\log(2y)/40$. This charges at most $L(U_0)/4$ to the same physical scale. For repeats the multiplier mass at fixed $y$ is at most $\frac12\log(X/y)+27$. Integration charges $I(U_0)/2+27A(U_0)$. These are finite applications of Fubini to nonnegative majorants. Incorporating $K$ yields
$$
\tfrac34 L(U_0)\le P(U_0)+\tfrac12 I(U_0)+C_R A(U_0). \tag{4}
$$

Set $d=4C_R/3$. For $d+1\le u\le U_0$, monotonicity of $P$ turns (4) into $(u-d)I'(u)\le\frac53 I(u)+\frac43P(U_0)$. Thus
$(I(u)+\frac45P(U_0))(u-d)^{-5/3}$ is nonincreasing. Evaluating it at both ends and applying (4) at $U_0$ proves
$$
A(U_0)\ll_R(1+U_0)^{2/3}(1+P(U_0)).
$$
Solving (1) for $P_R$ and applying the triangle inequality gives $P(U_0)\le(7U_0/4+C_R)A(U_0)$. The finite initial interval is absorbed into the first constant. In particular, for every $\epsilon>0$ a bound $P(\log(2X))\le X^\epsilon$ at arbitrarily late $X$ would imply bare RH. The [all-cutoff zero bill](what-the-two-signs-cost-together.md) gives the full limit $\log(1+A(\log(2X)))/\log X\to\Theta-1/2$. The two bounds prove the same limit for the retained discrepancy. They also give $P(U_0)\gg_R U_0^{1/3}$ for all sufficiently large $U_0$, because $A(U_0)\gg U_0$ follows from a critical-line zero. Even after the pruning, a uniformly bounded accumulated discrepancy is impossible.

## A finite test that stays on the original quotient grid

There is also a version with no continuum input in the test. Fix an integer $R\ge1$. At positive rational $x\ge1/2$ let $L(x)$ count the whole doublings up to $2x$, namely $\lfloor\log_2(2x)\rfloor$. Use the integer cutoff
$$
Y^\#(x)=\max\{R,\lfloor L(x)/160\rfloor^2\}.
$$
Since $\log 2\ge1/2$, its square root is at most $\max(\sqrt R,u/80)$. Compute
$$
T_R(x)=\sum_{n\le2x}\frac{m(n)}n w(n/x)\log(x/n)
 -\sum_{\substack{Y^\#(x)<p\le2x\\p\ge5}}\frac{\log p}{p} S(x/p).
$$
For a positive integer $H$, take exactly $x=H/d$ for $1\le d\le2H$. Let $q_R(H)=\ell/H$, where $\ell$ is the least nonnegative integer for which **every** one of these finite rows satisfies
$$
H\lceil\sqrt{x}\rceil\,|T_R(x)|\le\ell\,\log(4x). \tag{5}
$$
All log arguments are positive rationals and all their coefficients are rational before the integer norm in (5). The two inequalities obtained by removing the absolute value can be compared exactly by clearing coefficient denominators, exponentiating and cross-multiplying integer products. Rounding the maximum up costs less than $1/H$. The script instead encloses logs with rational series and recognizes exact ties by prime factorization. No sum or supremum over unobserved real sides enters it.

Write $M_H=\max_{d\le2H}\sqrt{H/d}\,|S(H/d)|$ with $d\ge1$. The finite logarithmic identity shows that $T_R(x)-(\log x)S(x)$ is exactly the sum of the excluded small-prime and repeat charges. Each $S(x/r)$ needed here has index $dr\le2H$ in the **same** finite grid. The normalized omitted mass is at most $8\sqrt R+u/10+u/2+27$. For $u$ larger than a constant depending only on $R$, dividing by $\log x=u-\log2$ thus costs at most three quarters of $M_H$. The bounded initial range has a uniform bound on $\sqrt x |S(x)|$. Also $\sqrt x\le\lceil\sqrt x\rceil\le(1+\sqrt2)\sqrt x$ and $\log(4x)=u+\log2$. Taking the maximum and then reversing the triangle estimate gives
$$
M_H\ll_R1+q_R(H),\qquad q_R(H)\ll_R1+M_H.
$$

In particular the nonnegative rational total $T(J)=\sum_{j\le J}q_R(j^4)/j$ is another finite target. Either signed account from the preceding paper is at most $C_R(1+\log J+T(J))$, by using $d=1$. Under RH, $|S(y)|\ll_\epsilon y^{-1/2+\epsilon}$ for $y\ge1$, and the initial compact range is bounded. Hence $T(J)\ll_\epsilon J^\epsilon$ for every $\epsilon>0$ after renaming the exponent. Conversely, arbitrarily late $T(J)^k\le J$ for every positive integer $k$ suffice by the previous signed-area theorem. More generally $\log(1+T(J))/\log J\to4\Theta-2$. The lower bound at a right-side zero follows from the signed account, and the upper bound uses $|S(y)|\ll_b y^{b-1}$ for $\Theta<b<1$, or the uniform bound on the edge at $\Theta=1$. [Finite signed checkpoint implication](PALRH/FourthAccounts.lean)

Many quotient rows can be paid before evaluating (5). Put $b(H)=\min\{H,(1+\lfloor\log_2 H\rfloor)^2\}$ and keep only $H/d\ge b(H)$. Write $\widehat q_R(H)$ for the resulting price. Since $S$ is the average of $U$ on $[x,2x]$ and all the sharp reciprocal sums have magnitude at most one, skipped rows have $\sqrt x |S(x)|\le\sqrt{b(H)}$. In the preceding maximum argument only the row attaining $M_H$ matters. If that row was skipped, this explicit bound pays it. If it was kept, the same absorption applies with $\widehat q_R(H)$. Thus replacing $q_R$ by $\widehat q_R$ adds at most $O_R((1+\log J)^2)$ to the signed-account bound and preserves the cofinal RH test and the power exponent.

At side 625 and $R=31$, the full test reads 1,250 quotient rows. Its largest required price is $1986/625$ on the row with cofactor $625/17$. The paid age cutoff is 100. Only six rows remain and their exact price is $1682/625$, attained at cofactor $625/6$. The test examines the surviving simple primes in each retained row's logarithmic comparison. Trimming a row is distinct from deleting individual prime contributions inside a larger retained row. [Exact price grids at six heads](../receipt-archives/check_pal_prime_renewal.py)

## Testing the actual prime and cofactor

On $x<t\le2x$, for $x\ge1$, the old side consists of the single mark 1 and $S(x/t)=2-t/x$. Before a moving small-prime cut is imposed, this whole terminal interval contributes
$$
2\log2-1-\sum_{x<p\le2x,\;p\ge5}\frac{\log p}{p}(2-p/x).
$$
The continuum term is the same positive constant at every such side. The discrepancy is positive at $x=4$ and negative at $x=10$. Taking absolute values of the two clocks separately would already lose a constant on this one interval at every large $x$.

The [arithmetic replay](../receipt-archives/check_pal_prime_renewal.py) expands (1) and (2) into rational coefficients of individual prime logarithms plus a rational constant. It obtains (2) both from the prime sum and by integrating the integer cofactor count between its actual corners. Every coefficient agrees at the seven stated rational or integer scales, including 512. The signed terminal examples use outward log bounds. [Results and exact scope](../receipt-archives/2026-11-25-pal-prime-renewal.json)

## An interaction that survives trimming both ends

There is a stronger pointwise test for **fixed** cutoffs. Choose any fixed $a,b\ge1$ and retain only $t>a$ and $x/t>b$ in the continuum-minus-prime comparison, using the orientation of $P_R$. Arbitrarily large $x$ give values greater than $c\,x^{-1/2}\log x$, and arbitrarily large $x$ give values less than $-c\,x^{-1/2}\log x$, for some $c>0$. The onset can depend on the cutoffs. Equation (4) supplies the bound for the moving cutoff.

To see why, set $s=1+z$ and $G(s)=(1-2^{-s})(1-3^{-s})\zeta(s)$. The edge has Mellin transform $\Phi(z)=W(z)/G(s)$, with $W(z)=(2^{z+1}-1)/(z(z+1))$. The signed prime measure $dt/t-\sum_{p\ge5}(\log p)/p\,\delta_p$ has transform
$$
\Psi(z)=\frac1z+\frac{G'(s)}{G(s)}-\frac{G'(2s)}{G(2s)}
       +\sum_{p\ge5,\;k\ge3\ {\rm odd}}(\log p)p^{-ks}.
$$
This follows in $\Re z>0$ from the Euler product, with the even powers grouped exactly. The remaining series converges absolutely for $\Re s>1/3$. The transform of the retained comparison is the product of $\Phi$ and $\Psi$ after subtracting from each its integral on the omitted compact range. Those subtractions are entire.

Take any critical-line zero $\rho=1/2+i\gamma$ of multiplicity $m$. At $z=\rho-1$, $\Phi$ has order $m$ as a pole, while $\Psi$ has a simple pole of residue $m$. The even powers are regular there because $2\rho$ lies on the zero-free one-line away from 1. Their product has order $m+1$ with its top coefficient intact after both compact subtractions. At the real point $z=-1/2$ the product has at most a simple pole from the even powers. The real interval above it is regular, including the cancellation at $z=0$. [Edge transform and sign argument](what-the-last-two-rows-carry.md) · [One-line nonvanishing in the pinned library](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/Nonvanishing.lean)

Apply the nonnegative-transform argument from the edge paper to an eventual upper bound $c\,x^{-1/2}\log x$, and then apply it with the sign reversed. The real comparator has a double pole with top coefficient $c$. At the nonreal pole, multiplying by $(\Re z+1/2)^2$ leaves the nonzero double-pole coefficient if $m=1$ and an unbounded value if $m>1$. A sufficiently small $c$ contradicts the absolute-value bound on the nonnegative transform. This explains why trimming any fixed collection of primes **and** any fixed collection of small cofactors cannot remove the logarithmic-size swings. Both growing coordinates participate.

## Unresolved

Bound the joint reading (2) at arbitrarily large cutoffs in (3) or (4). The [Lean deduction](PALRH/OrdinaryPrimeGrid.lean) starts with finite-support integer bids on the retained fourth-power quotient grids. It pays the repeats and every discarded row before deriving stock Mathlib RH. The bids still need a proof of the required growth bound. The integral transfer and the signed oscillations after trimming both ends are paper results.
