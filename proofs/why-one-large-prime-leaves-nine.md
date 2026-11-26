# Why one large prime leaves nine

**There is a positive signed surplus in every sufficiently late fourth-power block for the part of the PAL stream carrying one large prime and a small cofactor. Its leading coefficient is exactly 9.** The first term cancels. The next term remembers that a larger cofactor puts its companion prime lower down, where primes are denser. At one trillion this distinction isolates about **+8.55 million** on one side of the previously measured sector cancellation and **−8.59 million** on the other.

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). Pang’s PAL and BLA questions asked what travels with a prime and whether an unresolved distinction can leave a second trace. His APCI comparisons suggested moving the frame while keeping the labels fixed. Hearthline derived the surplus, its complementary deficit and the carrier described below. The analytic inputs are the ordinary zeta pole, a classical unconditional Möbius estimate and a prime number theorem in short intervals.

## What is counted

Let $Y=m^4$, $L=(m+1)^4-m^4$, and fix $0<\gamma<11/26$. Each member of the family is an integer $n=cq$ in $(Y,Y+L]$, with $q$ prime and $c\le Y^\gamma$. The prime $q$ is larger than $c$ eventually, so each member has a unique large prime. Use the actual first-pass weights
$$
 a(v^2u)=v\mu(u),\qquad v=2^i3^j,\quad (u,6)=1,
$$
and put $a=0$ elsewhere. On this family $a(cq)=-a(c)$ for sufficiently large $Y$. The signed sum in the block satisfies
$$
 \boxed{\displaystyle\sum_{\substack{Y<cq\le Y+L\\c\le Y^\gamma\\q\ {\rm prime}}}a(cq)
       \ \sim\ \frac{9L}{(\log Y)^2}.} \tag{1}
$$
For the unpassed rough weight $\mu(u)\mathbf1_{(u,6)=1}$ the coefficient is 3. At the endpoint $\gamma=0$, only $c=1$ is allowed and the sum is asymptotic to $-L/\log Y$. A fixed positive exponent, however small, changes which term survives. All logarithms are natural.

## The two threes

Write $W=\log Y$. For a fixed $c$ the available prime interval has length $L/c$ and starts at $Y/c$. Its expected count is $L/[c(W-\log c)]$. The first two terms of the reciprocal have a direct meaning,
$$
 \frac1{W-\log c}=\frac1W+\frac{\log c}{W^2}
      +\frac{(\log c)^2}{W^2(W-\log c)}.
$$
The first term treats every prime search as if it started at the original height. The second accounts for the change of height. What matters is the ordinary signed cofactor weight in front of each.

For real $s>1$ the Dirichlet series of $a(c)$ is
$$
 A(s)=\frac{1}{\zeta(s)(1-2^{-s})(1-3^{-s})(1-2^{1-2s})(1-3^{1-2s})}.
$$
The first pair of local factors comes from removing 2 and 3 from the Möbius stream. The second comes from summing the weights $v$ at $v^2$. At $s=1$ each reciprocal pair contributes $1/[(1-1/2)(1-1/3)]=3$. Finally $h\zeta(1+h)\to1$ as $h\downarrow0$. On the real axis this follows just by bounding the decreasing positive sum between $\int_1^\infty x^{-1-h}\,dx=1/h$ and $1+1/h$. Therefore $A(1)=0$ by continuity and $A'(1)=3\cdot3=9$. The simple-pole argument only uses zeta near 1. [Euler product](https://dlmf.nist.gov/27.4) · [Pole and Laurent expansion](https://dlmf.nist.gov/25.2) · [Lean calculation with the ordinary zeta function](../pal-rh/PALRH/LargePrimeSurplus.lean)

These give ordinary convergent cofactor sums,
$$
 \sum_{c\ge1}\frac{a(c)}c=0,\qquad
 \sum_{c\ge1}\frac{a(c)\log c}{c}=-9. \tag{2}
$$
Here is the convergence argument. The unconditional Mertens estimate $\sum_{n\le x}\mu(n)\ll_B x/\log^B(2x)$ holds for every fixed $B$. Write $a=\mu*b$, where $b$ has the four positive geometric factors displayed above. Since $\sum b(n)n^{-3/4}<\infty$, splitting the convolution at $n=\sqrt x$ gives the same logarithmic saving for $\sum_{c\le x}a(c)$. For the large divisors use $\sum_{n>\sqrt x}b(n)/n\ll x^{-1/8}$. Partial summation now gives tails $O_B(1/\log^B(2U))$ beyond $U$ in either sum in (2), choosing the original exponent large enough. The same bounds give convergence uniform as $s$ decreases to 1 for the series and its first derivative. This identifies their sums with the two values of $A$. [Unconditional Mertens bounds of Lee and Leong](https://arxiv.org/pdf/2208.06141)

## Why the expansion applies to the actual primes

Put $\lambda(Y)=-\sum_{c\le Y^\gamma}a(c)/[c(W-\log c)]$. For every fixed $B>0$ the signed count in any initial fraction $t$ of the block is
$$
 tL\lambda(Y)+O_{\gamma,B}(L/W^B),\qquad 0\le t\le1. \tag{3}
$$
To verify this replacement, divide the block into $\lceil W^{B+3}\rceil$ equal pieces. At each $c\le Y^\gamma$ the prime intervals around $x\asymp Y/c$ have lengths $h\asymp L/(cW^{B+3})$. The worst power exponent is $(3/4-\gamma)/(1-\gamma)>17/30$, and $h<x^{0.99}$ eventually. Corollary 1.3 of Guth and Maynard bounds the error per interval by $O_\gamma(h\exp(-(\log x)^{1/4}))$. Integer endpoints change estimates by at most a constant per piece and cofactor. Over all pieces and cofactors those rounding errors are $O(W^{B+3}Y^\gamma)$ times the bounded average absolute cofactor multiplicity, which is negligible compared with $L/W^B$. Replacing the log of the local start by $\log(Y/c)$ has relative error $O(L/(Y\log Y))$. Sum the other errors using $\sum_{c\le Y^\gamma}|a(c)|/c\ll W$. A partial last piece costs $O(L/W^{B+3}+\sqrt Y\log Y)$ in total absolute physical marks by the elementary smooth-divisor count. This proves (3) uniformly. [Guth and Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552) · [Absolute physical weight of a subinterval](../pal-rh/how-much-can-travel-with-a-prime.md)

To evaluate $\lambda(Y)$ choose $U=\exp(W^{1/4})$, which lies below $Y^\gamma$ eventually. In the part $U<c\le Y^\gamma$, partial summation using the first tail in (2) and the bounded variation $O_\gamma(1/W)$ of $1/(W-\log c)$ makes the contribution smaller than any fixed inverse power of $W$. For $c\le U$ the remainder in the reciprocal expansion contributes at most $O(W^{-3}(\log U)^3)=O(W^{-9/4})$, since $\sum_{c\le U}|a(c)|/c\ll\log U$. Use (2) to extend the first two sums back to infinity. Thus
$$
 \lambda(Y)=0/W+9/W^2+o(W^{-2}).
$$
The sign is positive because adjoining the large prime changes the sign of $a(c)$ a second time. This proves (1), including its version against bounded Lipschitz functions of the normalized block coordinate by partial summation. Removing the square-pass pair from $A$ gives the asserted coefficient 3.

## A single prime family can carry the remaining five moments

On each sufficiently large block keep a fraction of the labels $5q$, and spend all other marks in the displayed large-prime family. The fraction may differ across the five bins of the [prime transport](which-prime-labels-cancel.md). Each $5q$ is a positive ordinary mark. Its distribution has density $b(Y)=1/[5\log(Y/5)]$ up to the same errors as (3). The ideal fraction is $\lambda(Y)/b(Y)\sim45/\log Y$.

For exact weights take $M$ to be the actual five-by-five Bernstein moment matrix of the $5q$ bins and $h$ the full signed column of the growing family. Both use the original functions $(Y/n){4\choose i}t^i(1-t)^{4-i}$. Dividing $M$ by $Lb(Y)$ gives the invertible limiting integral matrix from the preceding proof. Integration of (3) against the five test functions shows $h-M\mathbf1\,\lambda(Y)/b(Y)=O_B(L/W^B)$ for any $B$. The inverse has size $O(W/L)$, so each component of $M^{-1}h$ equals $\lambda(Y)/b(Y)+O_B(W^{1-B})$. All five rational fractions are strictly between 0 and 1 eventually. This leaves a positive stream supported entirely on the specified semiprimes. One can instead retain only $385q$ with $385=5\cdot7\cdot11$, leaving fractions asymptotic to $3465/\log Y$ and covering every semiprime in the family eventually.

The spent stream annihilates all five moments on each whole block. Its signed cumulative count in every partial block is $O_B(L/W^B)$ by the same density comparison, since its leading term is removed. Consequently its moving-head cost satisfies, for every fixed $B>0$,
$$
 \left|\sum_n w(n)G(T,n)\right|\ll_{\gamma,B}\frac{\sqrt T}{\log^B(2T)} .
$$
Indeed the [cutoff argument](../pal-rh/how-much-can-travel-with-a-prime.md) already pays $O(T^{2/5})$ for the early range and the quadratic cutoffs. At the one remaining ramp, partial summation multiplies the signed cumulative bound by $O(L/T)$. Homogeneity covers $G(T,2n)$ at the same physical head. This stronger error applies to the stream spent by this operation.

## Where the opposite sign went

The whole physical stream has $\sum_{n\le Z}a(n)\ll_B Z/\log^B Z$ by the convolution estimate above. In a dyadic interval $(Z,2Z]$ the selected family contributes $(9+o(1))Z/\log^2 Z$ by summing (1) block by block. The entrance and exit blocks cost $O(Z^{3/4})$. Its complement must therefore contribute $(-9+o(1))Z/\log^2 Z$ there. This last statement is a dyadic average. It makes no assertion of a negative sign in every individual fourth-power block.

The same reasoning works for the actual increasing price $g(z)=1/(2z)-3/2+3z^2-2z^3$ in the sector $8X/5<n\le5X/3$, where $z=n/(2X)$. One may use the common cutoff $c\le X^\gamma$ across this sector since $X$ and the block heights differ only by fixed factors. Partial summation for the full stream and (3) for the family give opposite leading contributions
$$
 \pm\frac{18X}{\log^2 X}\int_{4/5}^{5/6}g(z)\,dz,\qquad
 \int_{4/5}^{5/6}g(z)\,dz=\tfrac12\log(25/24)-31789/1620000>0 .
$$
The result locates two genuinely opposite arithmetic populations in the measured sector. RH on this route still needs control after their leading terms cancel, down to the fourth-power allowance.

## Finite signs can run either way

With $\gamma=3/8$ the cofactor cutoff on a fourth-power block is $\lfloor\sqrt{m^3}\rfloor$. Here are exact signed multiplicities.

| Block begins at | Maximum cofactor | Signed marks in family | Available $5q$ labels |
| ---: | ---: | ---: | ---: |
| $20^4$ | 89 | −3,057 | 665 |
| $100^4$ | 1,000 | −66,189 | 48,222 |
| $577^4$ | 13,860 | +2,979,812 | 6,465,124 |
| $1100^4$ | 36,482 | +33,859,737 | 40,381,469 |
| $2663^4$ | 137,422 | +543,061,786 | 504,913,348 |

A positive-only remainder is impossible in the first two rows. All five moments can already be placed on $5q$ at $577^4$ and $1100^4$. At $2663^4$ even the constant moment exceeds the entire $5q$ supply by **38,148,438**. Allowing the positive $rq$ groups for all primes $5\le r\le347$ pays the five moments there. A successful finite fit at one head gives no threshold for later heads.

At the original trillion sector the fixed cutoff is 31,622. Its signed multiplicity is **+361,604,668**. The actual price contribution is between **+8,548,713.431 and +8,550,054.784**. Subtracting from the independently obtained full-sector value bounds the complement between **−8,595,682 and −8,594,130**. Here the five moments also fit on the $5q$ labels alone. No extrapolation from the asymptotic formula enters any of those finite bounds. [Counting program](../receipt-archives/large_prime_block.cpp) · [Direct small calibration and exact capacity replay](../receipt-archives/check_pal_large_prime_surplus.py) · [Numerical and formal record](../receipt-archives/2026-11-25-pal-large-prime-surplus.json)
