# How many square passes does the sign need?

Christopher Daniel Pang and Hearthline, 25 November 2026. Pang asked whether a layer could carry its own trace and still be read back after the next turn. The PAL v2.4 spine supplies the requirement that each return have a price. RPL supplies the square scale, APCI the same-input test, and the earlier two-clock work supplies the two independent periods. The four-row inverse below permits a different research target: at each finite head the arithmetic question is whether any row is negative. A pass adds smaller copies of the very same list. Because we can subtract them back out, we can measure how much that change costs. [Corpus sources](CORPUS-ROUTES.md) · [Earlier signed-area theorem](what-the-two-signs-cost-together.md)

## Make one pass and undo it

Start with the actual $S_0(x)=\sum_{d\le2x}\mu(d)\mathbf1_{(d,6)=1}w(d/x)/d$, with $w(t)=\max(0,\min(1,2-t))$. Define
$$
 S_{k+1}(x)=\sum_{a,b\ge0}2^{-a}3^{-b}S_k\bigl(x/(4^a9^b)\bigr).
$$
The sum ends at $4^a9^b\le2x$. Four readings undo a pass at any side.
$$
 S_k(x)=S_{k+1}(x)-\tfrac12 S_{k+1}(x/4)-\tfrac13 S_{k+1}(x/9)
                 +\tfrac16 S_{k+1}(x/36). \tag{1}
$$
Indeed subtracting the first shift removes precisely the terms with $a\ge1$. Subtracting the second removes those with $b\ge1$. The last term restores the overlap. At $x=4$ the new reading is $57/70+S_0(1)/2=46/35$. Its reading at 1 is 1 and both smaller rows in (1) vanish. The recovered value is $57/70$.

Each coefficient keeps its provenance. At $n=4^a9^b d$ with $(d,6)=1$, the new numerator after $k\ge1$ passes is
$$
2^a3^b\binom{k+a-1}{a}\binom{k+b-1}{b}\,\mu(d).
$$
Other indices have zero coefficient. The two binomial coefficients count the ways to distribute the two exponents among the passes. The rough sign is attached to the unique remaining factor $d$.

## A finite sign test at growing heads

Take a positive integer $q$ and an arbitrarily late starting index $B$. Find integers $N\ge B$ and $k\ge1$ with $qk\le N$ such that
$$
 S_k(n/2)\ge0\qquad(1\le n\le2^{N+1},\ n\in\mathbb N). \tag{2}
$$
Each reading in (2) is rational. A complete pass can extend across as many different scales as are actually present, and (1) recovers the input on the identical physical grid. The late-index condition prevents any fixed finite data set from settling the problem.

**Theorem.** The stated condition for every $q$ and every $B$ implies RH. Under RH, for each fixed integer $q\ge1$, every sufficiently large $k$ passes the entire interval $0<x\le2^{qk}$. Without assuming RH, $S_k$ is strictly positive throughout $1/2<x\le12^k$ for all sufficiently large $k$. Equation (8) gives an additional growing range. The reading is zero through $1/2$.

Between consecutive half-integers each $S_k$ is affine in $1/x$. Every summand's corners are integer multiples of a half, and finitely many summands occur on each bounded interval. The endpoint signs in (2) therefore suffice for the whole interval.

Put $H=2^N$, and write $A(f,X)=\int_0^X |f(y)|\,dy/\sqrt y$. A dilation $p^{-1}f(y/p^2)$ has precisely the area $A(f,X/p^2)$. Equation (1) gives $A(S_0,H)\le4^k A(S_k,H)$. Against the positive rectangle weight from the signed-area proof write
$$ D(f,X)=\int_0^X f(y)g(X/y)\frac{dy}{\sqrt y},\qquad
g(v)=\frac{\lfloor v\rfloor}{\sqrt v}-\frac12\sum_{n\le v}n^{-1/2}.
$$
For $v\ge1$, $1/5\le g(v)\le1$. The arithmetic seed obeys $0\le D(S_0,X)<7$ and has zero output through $1/2$. The same exact change of variables transports $D$ under each square shift. For every $\delta>0$ this gives the unconditional bound
$$
0\le D(S_k,H)\le 7(2H)^\delta
   \left[(1-4^{-\delta})(1-9^{-\delta})\right]^{-k}. \tag{3}
$$
To check it, start with $D(S_0,x)\le7(2x)^\delta$, valid also below $1/2$. Sum at the divided arguments. The factors are just two convergent geometric series.

The passed rows make $S_k$ nonnegative on $[0,H]$, including the initial zero interval. There $|S_k|\le5g(X/y)S_k$ when the rectangle is taken at $X=H$. Combining the estimates gives
$$
 A(S_0,H)\le 35(2H)^\delta
 \left[\frac{4}{(1-4^{-\delta})(1-9^{-\delta})}\right]^k . \tag{4}
$$
For a requested power $\epsilon>0$, take $\delta<\epsilon/3$ and then $q$ large enough that the fixed factor raised to $k\le N/q$ costs less than $H^{\epsilon/3}$. At sufficiently late heads the fixed constants fit too. At a zero of real part $\beta>1/2$ the already derived lower bound is $A(S_0,H)\ge c_\rho H^{\beta-1/2}$ at every $H\ge2$. Taking $\epsilon<\beta-1/2$ rules out that zero. [The rectangle and finite zero bill](what-the-two-signs-cost-together.md)

A fixed rate has a measurable consequence. Write $C_\delta=4/[(1-4^{-\delta})(1-9^{-\delta})]$. If (2) holds at arbitrarily late heads for one $q$, comparison with the lower bound from a zero gives
$$
 \beta\le\tfrac12+\delta+\frac{\log_2 C_\delta}{q}. \tag{4a}
$$
For $\delta=1/8$, $4^{-1/8}<6/7$ and $9^{-1/8}<7/9$, as one can check by taking fourth powers. Thus $C_{1/8}<126<128$. **Nineteen doublings per pass at arbitrarily late heads would exclude every zero with real part at least $151/152$.** Repeating the observed rate of 23 doublings cofinally would exclude every real part at least $171/184$. At 56 doublings the threshold is $3/4$. Each conclusion requires an unbounded sequence of successful heads with $q$ fixed.

A different route would fix one $k$ and study just its tail. If that tail eventually stays nonnegative, its earlier negative part costs a fixed finite amount $E_k=\int_0^\infty(-S_k(y))_+\,dy/\sqrt y$. Since $1/5\le g\le1$, one has $A(S_k,H)\le5[D(S_k,H)+2E_k]$. Equations (1) and (3) then give subpower growth of $A(S_0,H)$ and hence RH. A hypothetical off-line zero would therefore force negative readings at unbounded half-integers for **each fixed** number of passes. The additional late negatives would have to appear beyond every finite interval already tested.

## How many negative rows can the same estimate carry?

One can allow failures of the sign test and count them on the actual grid. At an integer head $H$ let $L_k(H)$ be the number of negative half-integer readings among $1\le n\le2H$. If a real reading is negative, one of its two half-row endpoints is negative, by the reciprocal interpolation. Each negative endpoint touches at most two intervals of length $1/2$. Thus the real set on which $S_k<0$ has total length at most $L_k(H)$ below the head. Moving those intervals toward zero gives the largest possible weight $1/\sqrt y$. For any set of length $\ell$, this weighted integral is at most $\int_0^\ell dy/\sqrt y=2\sqrt\ell$ by integrating the lengths of the level sets.

A pass multiplies the sup norm by at most $(\sum_a2^{-a})(\sum_b3^{-b})=3$, and $|S_0|\le1$. Consequently the negative area is at most $2\cdot3^k\sqrt{L_k(H)}$. Using $|f|=f+2(-f)_+$ against the rectangle and then undoing all the passes gives the explicit estimate
$$
 A(S_0,H)\le35(2H)^\delta C_\delta^k+20\cdot12^k\sqrt{L_k(H)}. \tag{4b}
$$
In particular it suffices to have $N_j\to\infty$, $k_j=o(N_j)$ and $\log(1+L_{k_j}(2^{N_j}))=o(N_j)$. In (4b) take any fixed $\delta>0$. Both the inverse cost and the number of failures have subpower cost, and $\delta$ can be arbitrarily small. Conversely, a zero of real part $\beta>1/2$ would force **at least $c_{\rho,k}H^{2\beta-1}$ negative half-rows at every sufficiently large integer head**, for each fixed $k$. To see this, use any $\delta<\beta-1/2$ in (4b) and absorb its first term in half the lower bound from that zero. This counts how many holes would have to remain even if they could be moved to the most expensive possible positions.

## Why the sign is already controlled over a growing interval

In the coordinate $u=\log x$, set $F(u)=e^{u/2}S_0(e^u)$ and $h_1=\log4$, $h_2=\log9$. A pass on this normalized reading adds earlier values at $u-a h_1-b h_2$, with coefficient one. At any $\lambda>0$ introduce independent geometric counts with probabilities $(1-e^{-\lambda h_i}) e^{-a\lambda h_i}$ for $a=0,1,\ldots$. The sum $V$ of their two clock readings has mean
$$
 m(\lambda)=\frac{h_1}{e^{\lambda h_1}-1}+\frac{h_2}{e^{\lambda h_2}-1}.
$$
It decreases continuously from infinity to zero. Write $Z(\lambda)=[(1-e^{-\lambda h_1})(1-e^{-\lambda h_2})]^{-1}$. For independent copies $V_i$ and $G_\lambda(v)=e^{-\lambda v}F(v)$, the exact finite reading satisfies
$$
 e^{u/2}S_k(e^u)= Z(\lambda)^k e^{\lambda u}
    \mathbb E_\lambda\,G_\lambda\!\left(u-\sum_{i=1}^k V_i\right). \tag{5}
$$
For each $u/k$ in the chosen range, use the unique $\lambda$ with $m(\lambda)=u/k$. The sign on the right is then set, at large $k$, by the integral of $G_\lambda$. In this construction the integral is positive:
$$
 \int_{\mathbb R}G_\lambda(v)\,dv=
 \frac{W(\lambda-1/2)}
 {(1-2^{-(\lambda+1/2)})(1-3^{-(\lambda+1/2)})\zeta(\lambda+1/2)},
 \quad W(z)=\frac{2^{z+1}-1}{z(z+1)}. \tag{6}
$$
For $\lambda>1/2$ this is an absolutely convergent calculation with positive numerator and denominator. At $\lambda=1/2$ the limit is 3. The unconditional bound $|S_0(x)|\ll\exp(-c\sqrt{\log x})$ provides absolute convergence and passage to the limit there. Under RH the preceding edge estimate gives $|S_0(x)|\ll_\eta x^{-1/2+\eta}$ for every $\eta>0$. It justifies (6) by continuation for every $\lambda>0$. On $0<\lambda<1/2$ numerator and denominator are both negative, the latter by the alternating eta series at a positive real argument. [Edge transform and decay bounds](what-the-last-two-rows-carry.md)

The two clocks in (5) have irrational period ratio because unique factorization rules out $4^a=9^b$ for positive integers $a,b$. Uniformly for $\lambda$ in a compact subinterval of the stated convergence region and $u=k m(\lambda)$, one obtains
$$
 \sqrt k\,\mathbb E_\lambda G_\lambda(u-V_1-\cdots-V_k)
 =\frac{\int G_\lambda}{\sqrt{2\pi\,\operatorname{Var}_\lambda(V)}}+o(1). \tag{7}
$$
This is the nonlattice local limit mechanism. The following details supply uniformity for the changing real parameter in this particular family. [Stone, *On local and ratio limit theorems*](https://digicoll.lib.berkeley.edu/record/113081/files/math_s5_v2_p2_article-15.pdf)

Let the total counts of the two geometric variables be $a,b$. Their independent mass functions are $\binom{k+a-1}{a}(1-r)^k r^a$ with $r=e^{-\lambda h_i}$. On these compact parameter intervals the ratios stay bounded away from 0 and 1. Stirling’s formula, expanded to second order for deviations at most $M\sqrt k$ from the two means, gives the two Gaussian densities times $1/\sqrt k$ with uniform relative error $O_M(k^{-1/2})$. In particular the largest point mass of either count is $O(k^{-1/2})$, using unimodality at its mode.

Condition on $a$. Any interval of length one contains at most $1+\lceil1/h_2\rceil$ possible values of the other clock. Thus after multiplication by $\sqrt k$ the tails of $G_\lambda$ cost at most a constant times the sum of their suprema over unit intervals. This tends uniformly to zero by the decay used in (6), also at the unconditional endpoint. For a continuous compactly supported cutoff of $G_\lambda$, values $|a-\mathbb E a|>M\sqrt k$ cost $O(1/M^2)$ after this same normalization, by Chebyshev’s inequality. In the remaining range the relevant $b$ differ from their mean by $-(h_1/h_2)(a-\mathbb E a)+O(1)$. Their Gaussian weight can be frozen over that bounded difference. The remaining periodic factor is the translate of $\sum_{\ell\in\mathbb Z}G_\lambda(h_2(t-\ell))$ evaluated on the rotation by $h_1/h_2$. Its circle mean is $(\int G_\lambda)/h_2$. On intervals of increasing length the rotation averages converge to that mean uniformly in the starting phase. This follows first for trigonometric polynomials by summing a geometric progression and then for these continuous periodizations by uniform approximation, also uniform in $\lambda$ by compactness. Partition the central $a$ range into blocks of length $\lfloor k^{1/4}\rfloor$. The Gaussian weight changes by $o(1)$ within each block in the scaled coordinate. The final one-dimensional Gaussian integral gives (7), with variance $h_1^2r_1/(1-r_1)^2+h_2^2r_2/(1-r_2)^2$.

There is an elementary way to cover the starting interval uniformly in $k$. For the 4-clock alone the coefficient of the $a$th shift after $k$ passes is $c_a=2^{-a}\binom{k+a-1}{a}$. For $1\le x\le 2^{k/4}$ take $a=\lfloor\log_4 x\rfloor$. Then $a\le k/8$ and $1\le x/4^a<4$. The seed on this interval is at least $1-1/5-1/7=23/35$. The still earlier ages $x/4^{a+1},x/4^{a+2},\ldots$ have nonnegative seed. For $1\le j\le a$ we have $c_{j-1}/c_j=2j/(k+j-1)\le1/4$. Since every seed has magnitude at most one, **all** possibly adverse terms together cost at most $c_a/3$. The $a$th term alone covers them. For $1/2<x<1$ the seed is already positive. The 9-clock takes positive combinations of these smaller arguments. This proves positivity through $2^{k/4}$ for every $k\ge1$ without a local limit theorem.

Now $m(1/2)=\log4+\frac12\log9=\log12$. For $2^{k/4}\le x\le12^k$ the saddle parameters run over a compact interval starting at $1/2$. The positive continuous leading term in (7) has positive minimum there, proving the unconditional band. For each fixed $q$ under RH the interval $(\log2)/4\le u/k\le q\log2$ still gives a compact interval of positive $\lambda$. This proves the stronger converse, including every physical half-row of (2). A single clock would sample a periodization depending on its initial phase. The second clock is what lets the full positive mean determine the sign here.

## How far past the factor twelve the estimate goes

There is an absolute $a>0$ such that, for all sufficiently large $k$,
$$
 S_k(x)>0\quad\text{throughout}\quad
 \tfrac12<x\le 12^k\exp\!\left(a\,\frac{k^{5/7}}{(\log(2+k))^{1/7}}\right). \tag{8}
$$
Put $J=k^{5/7}/(\log(2+k))^{1/7}$ and $\psi(v)=v^{3/5}/(\log(2+v))^{1/5}$ for $v\ge1$. The Korobov–Vinogradov bound on the Möbius sum gives $|S_0(e^v)|\ll e^{-c\psi(v)}$. To transfer it, write the rough partial sum as $\sum_{d=2^i3^j\le x}M(x/d)$. Through $d\le\sqrt x$, the logarithms retain at least half their size and $\sum 1/d=3$ over all these smooth integers. The remaining terms cost $O(x^{3/4})$ since $\sum_{d>\sqrt x}1/d\le x^{-1/4}\sum d^{-1/2}$ on this set. Partial summation, the zero limit of the reciprocal sum, and tapering give the stated decay after decreasing $c$. In particular $\int_v^\infty e^{-c\psi(w)}dw\ll e^{-c\psi(v)/2}$ by monotonicity and integrability of the remaining factor. Lee and Leong give the unconditional Mertens estimate for sufficiently large $x$. [Theorem 2.2, equation (23), version 5](https://arxiv.org/html/2208.06141v5#S2.SS2)

Let $u=k\log12+s$ with $0\le s\le aJ$, and take $m(\lambda)=u/k$. Since $m'(1/2)=-\operatorname{Var}_{1/2}(V)<0$, the displacement $d=1/2-\lambda$ satisfies $0\le d\le LaJ/k$ with an absolute $L$. In (5) the sampled residual $v=u-\sum V_i$ never exceeds $u=O(k)$. On $1\le v\le J$ the tilted seed is bounded by $Ce^{-c\psi(v)/2}$. Indeed $v/\psi(v)$ increases and $J^2/k\asymp\psi(J)$, so $dv\le c\psi(v)/2$ for sufficiently small $a$. The unit-interval bound used in (7) makes the normalized contribution outside each fixed compact interval uniformly small on this part.

For the region beyond $J$, the probability of a residual at least $t$ is at most $\exp(-bt^2/k)$ uniformly for $0\le t\le u$. The centered variable $m(\lambda)-V$ has log moment generating function at most $Cz^2$ for $0\le z\le z_0$, uniformly for $\lambda$ near $1/2$. Its mean vanishes and its second derivative on this parameter range is bounded. Apply the exponential Markov inequality with $z=\eta t/k$ for a fixed sufficiently small $\eta>0$. Now $|S_0|\le1$, so the entire contribution from $v\ge J$, after multiplication by $\sqrt k$, has absolute value at most
$$
 \sqrt k\sum_{j=\lfloor J\rfloor}^{\lceil u\rceil}
 \exp\bigl(d(j+1)-bj^2/k\bigr)
 \ll k^{3/2}\exp(-b'J^2/k)\longrightarrow0 .
$$
A sufficiently small $a$ pays the first exponent with half the second. On every fixed compact interval $e^{dv}S_0(e^v)$ tends uniformly to $S_0(e^v)$. The compact part of (7) at the matched mean gives the positive limit $3/\sqrt{2\pi\operatorname{Var}_{1/2}(V)}$. This proves (8). The classical envelope $\psi(v)=\sqrt v$ gives $J=k^{2/3}$ by the same argument. The extra number of doublings grows without bound. Its ratio to the number of passes still tends to zero.

## The first negative row, before and after

The [integer replay](../receipt-archives/check_pal_square_pass.py) checks every half-integer from 1 through $2^{23}=8{,}388{,}608$. There are 1,081,431 strictly negative original readings in those 16,777,215 samples. The first is at $6{,}513{,}932+\tfrac12$. One complete pass makes **all 16,777,215 readings strictly positive**. Either single-clock run also clears this finite interval. The four-term inverse separately recovers every earlier reading through side 160 in three successive passes. Each computation uses the actual Möbius signs. The direct coefficient formula independently prices the largest tested endpoint. [Counts and outward bounds](../receipt-archives/2026-11-25-pal-square-pass.json)

At the first negative half-row $x=13{,}027{,}865/2$, each of the four new readings is positive. Direct summation gives these decimal approximations.

| Argument | New reading $S_1$ | Multiplier in the return |
| --- | ---: | ---: |
| $x$ | 0.01650048806576 | $1$ |
| $x/4$ | 0.02969889085865 | $-1/2$ |
| $x/9$ | 0.04182751345698 | $-1/3$ |
| $x/36$ | 0.07374877107197 | $1/6$ |

Apply those four multipliers and add. Using outward bounds from the exact integer summation, the result is between $-3.89791\times10^{-12}$ and $-3.89783\times10^{-12}$. Direct evaluation of $S_0(x)$ lies inside that same interval. The transformed list kept enough information to distinguish which side of zero this particular reading was on.

## Unresolved

Earn the late sign condition for arbitrarily many doublings per pass. The unconditional range earns $\log_2 12$ doublings per pass plus a growing sublinear number of additional doublings. The finite criterion and its consequence for stock Mathlib RH are [formalized here](PALRH/SquareSignRows.lean). The [area budget](PALRH/SquarePassBudget.lean) uses the coarse constant 16 in place of 7. The converse, the sign range (8), the fixed-rate estimates (4a) and the count of permitted negative rows in (4b) are paper arguments. The finite experiment reaches 23 doublings with a single pass. Its first reversal and its repair give no all-scale extension of that finite range.
