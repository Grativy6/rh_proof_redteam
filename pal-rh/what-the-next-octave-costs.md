# What the next doubling window costs

Christopher Daniel Pang and Hearthline · 25 November 2026

Pang asked us to go upward in the claims the arithmetic can pay for. Here a fit that agrees with a longer head faces a different test. **Its total squared error may grow. Growth slower than every positive power of the exact head length already implies RH.** We also construct finite rational fits for which the error in the next doubling window is an ordinary signed count of squarefree integers.

## Why a hypothetical zero charges every head

Write $\chi(k)=[k\ge1]$, $e(k)=[k=1]$ and $b_d(k)=(k\bmod d)/d$ for $d\ge2$. A fit is a finite rational linear combination of the $b_d$. Its squared error against $T$ is $E=\sum_{k\ge1}|T(k)-F(k)|^2/[k(k+1)]$. Identify row $k$ with $(1/(k+1),1/k]$. If rows $1,\ldots,H$ are exact, the entire discrepancy is supported in $(0,1/(H+1)]$ up to a null set.

At a zero $s=\sigma+it$ with $\sigma>1/2$ and $s\ne1$, the Mellin reading of every fit vanishes. The reading of $\chi$ is $m_s=1/s$, and that of $e$ is $m_s=(1-2^{-s})/s$. Both are nonzero. On the actual remaining interval Cauchy–Schwarz gives
$$
|m_s|^2\le E\int_0^{1/(H+1)}x^{2\sigma-2}\,dx
=E\,\frac{(H+1)^{1-2\sigma}}{2\sigma-1}.
$$
Thus $E\ge (2\sigma-1)|m_s|^2(H+1)^{2\sigma-1}$ **at every exact head and every coefficient width**. If for each $\alpha>0$ there are arbitrarily large heads with $E\le(H+1)^\alpha$, choose $\alpha<2\sigma-1$. The lower bound eventually contradicts that budget. The functional equation reflects the other half of the critical strip. This proves the sufficiency statement for the bare Mathlib proposition. [Interval calculation](PALRH.lean) · [Both target theorems](PALRH/HeadGrowth.lean)

The interval proof also applies to any missed Mellin wave of a proposed construction. The [single-parent theorem](what-one-parent-misses.md) supplies such waves arbitrarily close to real part one. For any fixed finite parent and any $\eta>0$, its scaled copies with an exact head consequently pay $E\ge c_{\eta}(H+1)^{1-\eta}$ on either target, with a positive constant depending on the parent and target. A width increase cannot remove this obstruction while the parent stays fixed.

## One deterministic rational fit

Let $t=1,\ \nu(n)=\mu(n)$ for the occupied target. Let $t=0,\ \nu(n)=\mu(n)-[2\mid n]\mu(n/2)$ for the tick. In both cases $T(k)=\sum_{d\le k}\nu(d)\lfloor k/d\rfloor$. This follows by interchanging two finite sums and using $\sum_{d\mid n}\mu(d)=[n=1]$. At height $H\ge1$ compute
$$
g=\sum_{d\le H}\nu(d)/d,\qquad A=2t+\sum_{d\le H}\nu(d),\qquad
b=\frac{A-(5H+1)g/2}{H},\qquad a=g-b.
$$
Use $c_d=-\nu(d)$ for $d\le H$, $c_d=ad/H$ for $2H<d\le3H$, and $c_d=bd/H$ for $3H<d\le4H$. All other coefficients vanish. The entry at $d=1$ multiplies $b_1=0$ and is convenient for accounting. Both chosen outer blocks are beyond the first doubling window.

The two sums of outer coefficients divided by their moduli are $a,b$. Their unweighted sums are $a(5H+1)/2,b(7H+1)/2$. Thus $\sum c_d/d=0$ and $\sum c_d=2t$ including $d=1$. Writing $b_d(k)=k/d-\lfloor k/d\rfloor$ shows exactly how the supplied slopes cancel. The full-period mean is $t$, because the mean of $b_d$ is $(1-1/d)/2$. This balances the persistent periodic error as well as the initial slope. [Rational construction and exact head](PALRH/Balanced.lean)

Write $M_\nu(k)=\sum_{d\le k}\nu(d)$. Before either outer block opens, the fit is $\sum_{d\le H}\nu(d)\lfloor k/d\rfloor$. The first $H$ rows are exact. For **every** $H<k\le2H$ each omitted $d\le k$ has quotient one. Consequently
$$
T(k)-F_H(k)=M_\nu(k)-M_\nu(H).
$$
This expression uses the same physical fit, on the same row, for every $H$. Its first exact doubling-window price is
$$
W_\nu(H)=\sum_{H<k\le2H}\frac{(M_\nu(k)-M_\nu(H))^2}{k(k+1)} .
$$

## The remote tail is paid at every size

The coefficients have a height-independent bound. For $\mu$, the identity at $H$ gives $|H\sum_{d\le H}\mu(d)/d|\le1+(H-1)$ by bounding the $d>1$ remainders. For the tick the reciprocal sum is the corresponding difference $g_\mu(H)-g_\mu(\lfloor H/2\rfloor)/2$. Hence $|g|\le2$ in both cases, and $|A|\le4H$. The two outer rates satisfy $|a|\le12,\ |b|\le10$, so $|c_d|\le40$ for all $d$. The formal bound $|F_H(k)|\le102H$ also follows directly from the general impulse estimates in the construction.

After row $H^2$ the total squared error is bounded by $103^2$, since the uninspected row weights sum to $1/(H^2+1)$. Thus one entirely **rational** sufficient condition asks, for each positive integer $j$, for arbitrarily large $H$ such that
$$
\left(\sum_{k=1}^{H^2}\frac{|T(k)-F_H(k)|^2}{k(k+1)}\right)^j\le H+1 .
$$
A constant tail allowance is absorbed by any additional positive power at large $H$. No choice of unknown coefficients or infinite numerical tail is part of this test. [Both finite square-window implications in Lean](PALRH/SquareBudget.lean)

There is a shorter unconditional tail estimate on paper. Put $B=4H$. Let $V$ be the full-period mean of $(F_H-t)^2$. The covariance of $b_d,b_l$ is $(\gcd(d,l)^2-1)/(12dl)$. Indeed, conditional on their common residue, the two remaining digits are independent by the Chinese remainder theorem. Expanding $\gcd(d,l)^2$ using the second Jordan totient $J_2$ gives
$$
V=\frac1{12}\sum_{q=2}^B J_2(q)\left(\sum_{q\mid d} c_d/d\right)^2
\le\frac{40^2}{12}\sum_{q\le B}(1+\log(B/q))^2
\le \frac{5\cdot40^2}{12}B.
$$
In the inner sum only $1\le d\le B$ occur. The last inequality integrates the decreasing summand from $0$ to $B$.

The finite Fourier frequencies have reduced denominators at most $B$, so distinct frequencies on the circle are at least $B^{-2}$ apart. Here is an elementary large-sieve bound for any interval of $L$ consecutive rows. Center a tent of integer width $D=\max(L,B^2)$ at an integer midpoint. The tent $[1-|n|/D]_+$ is at least $1/2$ on these rows. Its Fourier transform is $D^{-1}|\sum_{j=0}^{D-1}e^{2\pi ij\theta}|^2$, bounded by $D$ at zero and by $1/(4D\|\theta\|_{\mathbb R/\mathbb Z}^2)$ elsewhere. In either circular direction the $j$th neighbor within a semicircle is at least $j/B^2$ away. Using $\sum j^{-2}<2$, the absolute row sum of this Fourier matrix is at most $D+B^4/D\le2D$. The inequality $2|uv|\le |u|^2+|v|^2$ and finite Parseval now bound the unweighted interval sum by $4DV$. This is the usual separated-frequency large-sieve mechanism. [Montgomery and Vaughan, *The large sieve*](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf)

Apply it to the intervals $[2^j N,2^{j+1}N)$ and use their largest row weights. For every $N\ge2$,
$$
\sum_{k\ge N} w_k|T(k)-F_H(k)|^2
\le V\left(\frac8N+\frac{16B^2}{3N^2}\right).
$$
Thus already at $N=\lceil B^{3/2}\rceil$ the complete remaining tail is $O(1)$ with an absolute constant. The exponent to control is carried by the **finite** band between the protected head and that cutoff.

## Which exponent the whole finite band measures

Let $\Theta$ be the supremum of $1/2$ and the real parts of the nontrivial zeta zeros. For either explicit profile, let $B_H$ denote its squared error on $H<k<\lceil(4H)^{3/2}\rceil$. There is an actual limit
$$
\lim_{H\to\infty}\frac{\log(1+B_H)}{\log(H+1)}=2\Theta-1 .
$$
The limit specifies what the measurement detects. Its numerical value is the unresolved question. The power floor for each right-side zero gives the lower limit for the whole error. Subtracting a nonnegative, uniformly bounded tail changes $\log(1+E)$ by at most a constant. When $\Theta=1/2$ nonnegativity gives the lower limit directly.

For the upper limit, first suppose $\Theta<1$ and fix $\Theta<r<1$. The Balazard–Saias estimate at real part $r$ gives $\sum_{n\le h}\mu(n)n^{-r-it}=O_{r,\eta}((1+|t|)^\eta)$ for every $\eta>0$, uniformly in $h$. To check the uniformity, choose $\Theta\le\alpha<r$ in their lemma and use its case $h=2$ to bound $1/\zeta(r+it)$; insert this in the general estimate. Partial summation then gives $\sum_{n\le H}\nu(n)n^{-1/2-it}\ll H^{r-1/2}(1+|t|)^\eta$ and $M_\nu(H)\ll H^r$. In the tick case use its two scaled copies of the Möbius sum. Since $r<1$, partial summation at one gives $g=O(H^{r-1})$: the full reciprocal sum converges to zero by continuity from $\Re s>1$ at the zeta pole. Thus both outer rates are $O(H^{r-1})$.

On the critical integration line $s=1/2+it$ the finite factor of the fit is $P_H(s)=\sum_{d\le H}\nu(d)d^{-s}-\sum_{d>H}c_d d^{-s}$. Its outer part is $O(H^{r-1/2})$ even after taking absolute values. Mellin–Plancherel gives the full error by integrating $|u_T(s)-\zeta(s)P_H(s)|^2/(2\pi|s|^2)$, where $u_\chi=1$ and $u_e=1-2^{-s}$. The resulting bound is $O_r(H^{2r-1})$. Let $r\downarrow\Theta$. For $\Theta=1$ the unconditional amplitude bound and the exact head already give $E=O(H)$, proving the same upper exponent. [Balazard–Saias estimate and Mellin–Plancherel normalization, §2](https://arxiv.org/pdf/math/0202141)

Only a modest unconditional vertical mean bound is needed in this integral. On $T\le |t|\le2T$, choose $N=\lfloor T^{3/2}\rfloor$. Sum-minus-integral comparison continues $\zeta(s)=\sum_{n\le N}n^{-s}+N^{1-s}/(s-1)+O((1+|s|)N^{-1/2})$ to the critical integration line. Integrating the square of the finite sum gives $O(T\log N+N\log N)$: each off-diagonal pair $m<n$ contributes at most $2\sqrt{n/m}/(n-m)$, and splitting at $m=n/2$ bounds their sum. The two remainder terms have squared integral $O(T^{3/2})$. Consequently $\int|\zeta(1/2+it)|^2(1+|t|)^{2\eta}/(1+t^2)\,dt$ is finite for $0<\eta<1/4$. This proof of the exponent identity is on paper. Its zero-free premise in the upper estimate is indexed by $\Theta$, and the argument never assigns a value to $\Theta$.

## Why the first doubling windows themselves suffice

Consider $W_\mu(h)$ at every positive integer $h$. If $m\le n<2m$, both windows see the rows $n<k\le2m$. Their readings differ there by precisely the fixed baseline $M(n)-M(m)$. Squaring that difference and summing over the common rows gives
$$
(2m-n)|M(n)-M(m)|^2
\le 2(2m)(2m+1)\{W_\mu(n)+W_\mu(m)\}.
$$
Suppose $W_\mu(h)\le C_\delta h^\delta$ at every $h$, for each $\delta>0$. For $n\ge8$ take $m=\lfloor3n/4\rfloor$. The common length is at least $n/4$. The displayed bound gives $|M(n)-M(m)|\le\sqrt{96C_\delta}\,n^{(1+\delta)/2}$. Iterating toward the origin sums a geometric series. Hence $M(n)=O_\epsilon(n^{1/2+\epsilon})$ for every $\epsilon>0$.

To see exactly where this reaches RH, set $\Phi(s)=s\int_1^\infty M(u)u^{-s-1}du$. Under the derived growth bound this integral is absolutely convergent and holomorphic for $\Re s>1/2$, by domination on compact subsets. For $\Re s>1$ ordinary partial summation and the Euler product give $\zeta(s)\Phi(s)=1$. The analytic identity $(s-1)\zeta(s)\Phi(s)=s-1$ extends over the half-plane and excludes a zero away from the pole. The raw Möbius Dirichlet series is used only where it converges absolutely. The analytic continuation uses its signed **primitive**. Stock Mathlib distinguishes these two convergence claims. [Overlap estimate and formal bare-target implication](PALRH/Octaves.lean)

On paper two interleaved families of heads already suffice, $2^j$ and $3\cdot2^{j-1}$ for $j\ge1$. Successive heads grow by $3/2$ or $4/3$, and each consecutive pair shares a fixed positive fraction of its rows. The same overlap estimate controls the saved baselines on that sequence by $O_\epsilon(h^{1/2+\epsilon})$. On $(h,2h]$ at a dyadic $h$, it follows that $\sum|M(k)|^2=O_\delta(h^{2+\delta})$. Cauchy–Schwarz on each dyadic band gives absolute convergence of the displayed primitive integral for $\Re s>1/2$. This version controls all sufficiently late heads of the two families. A single favorable pair of windows would not imply it.

The converse uses classical zero-free information only in its stated direction. Under RH, Littlewood’s Möbius bound gives $M(x)=O_\epsilon(x^{1/2+\epsilon})$, and hence the stated subpower prices on all doubling windows. For the first tick replace $M(x)$ by $M(x)-M(\lfloor x/2\rfloor)$. Its Dirichlet multiplier is $1-2^{-s}$, nonzero in the required half-plane. This identifies an equivalent arithmetic target. The outstanding direction is to bound the true signed prices without assuming a zero-free half-plane. [Littlewood’s result and the Balazard–Saias estimate, as stated by Báez-Duarte in §2](https://arxiv.org/pdf/math/0202141)

## Source and remaining question

Pang’s PAL v2.4 supplies the retained cut and its wider frame. RPL-T02 supplies the square shell, RPL-T07 motivates comparing the same reading on shared rows, and Compactification Costs asks which term survives when a boundary moves. The Mellin and Möbius tools are classical. The explicit late coefficient blocks, the physical budget and the overlap calculations above were developed for this branch. The upstream RH construction supplies the independent comparison target and toolchain. Publication priority for the applications is unassessed. [Corpus routes](CORPUS-ROUTES.md)

Can the signed difference of the real squarefree counts be bounded at this scale? The [integer replay](../receipt-archives/check_pal_growth_windows.py) checks the profile, its row arithmetic and both signs of the reduced product calculation. Finite measurements do not determine the asymptotic exponent.
