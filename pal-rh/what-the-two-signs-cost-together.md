# What the two signs cost together

Christopher Daniel Pang’s PAL research program, 25 November 2026. Pang’s frame question led to a rational number $s_H$ recoverable from the last two physical rows of each side. Here a second census measures the positive and negative readings on the same finite interval. RPL supplies the retained scale, APCI the same-input comparison, BLA the boundary charge and CLEF the question about two readings that share information. The arithmetic below uses Möbius inversion. [Corpus and editions](CORPUS-ROUTES.md) · [Original two-row calculation](what-the-last-two-rows-carry.md)

**Add just the rises, or just the dips.** For $J\ge1$ define the two nonnegative rational sums
$$
A_\pm(J)=\sum_{j=1}^J j\,(\pm s_{j^4})_+,\qquad u_+=\max(u,0).
$$
Both sums ultimately grow at least as fast as a positive constant times $\log J$, without assuming RH. A zero with real part $\beta>1/2$ would force **each** sum to be at least $c_\rho J^{4\beta-2}$ for every sufficiently large $J$. Thus a bounded total is already impossible. To establish RH it would suffice to prove arbitrarily late checks of $A_\pm(J)^k\le J$ for every integer $k\ge1$. The cheaper sign may be chosen afresh at each check. This is a finite rational comparison with no tail supplied to the test.

## Count every multiple of the same edge

Let $m(d)=\mu(d)\mathbf1_{(d,6)=1}$. Write $w(t)=1$ through 1, $2-t$ through 2, and zero beyond. At a real scale $x>0$ the continuous reading $S(x)=\sum_d m(d)w(d/x)/d$ agrees at integers with the actual $s_H$. It vanishes for $x\le1/2$. On changing a physical scale by an integer factor, one must keep $x/r$ at its actual value.

Call the integers $2^a3^b$, $a,b\ge0$, smooth in this paper. For a positive $n$, its signed divisor count $\sum_{d\mid n}m(d)$ equals 1 on these integers and zero elsewhere. Every prime of $n$ other than 2 or 3 pairs a squarefree divisor containing it with the same divisor without it. Consequently
$$
\sum_{r\le2x}\frac{S(x/r)}r=B(x),\qquad
B(x)=\sum_{q\ {\rm smooth}}\frac{w(q/x)}q . \tag{1}
$$
All sums at fixed $x$ are finite. The right side increases to $\sum_q1/q=3$. For example $n=12$ retains only the divisor 1. The divisors of 35 contribute $1-1-1+1=0$. Restricting the multipliers $r$ in (1) to $(r,6)=1$ gives just $w(1/x)$, since the corresponding divisor convolution equals the unit at 1. [Exact aggregation at real and integer scales](PALRH/RectangleBalance.lean)

## A positive price for both signs

For $v\ge1$ and $N=\lfloor v\rfloor$ form
$$
k(v)=\frac{N}{\sqrt v}-\frac12\sum_{n=1}^N\frac1{\sqrt n}.
$$
This number measures the difference between an ordinary count and a count under a square-root weight. For **every** $v\ge1$,
$$
\frac15<\frac1{\sqrt2}-\frac12\ \le k(v)\le1 . \tag{2}
$$
On $N\le v<N+1$ its infimum is $N/\sqrt{N+1}-\frac12\sum_{n\le N}n^{-1/2}$. These infima increase. Squaring the two positive terms in their consecutive difference reduces the sign to $(N+1)^3-(N+1/2)^2(N+2)=3N/4+1/2>0$. The first interval therefore gives the sharp lower constant. For the upper bound use $1/\sqrt n\ge2(\sqrt{n+1}-\sqrt n)$ and telescope. [Uniform kernel bounds](PALRH/RectangleBalance.lean)

For a cutoff $X\ge1$ let $U_\pm(X)=\int_{1/2}^X S_\pm(y)\,dy/\sqrt y$, where $S_\pm=(\pm S)_+$. Apply the change $x=ry$ to each term in (1), first with integration weight 1 and then with $\sqrt{X/x}/2$. Subtract the two answers and divide by $\sqrt X$. This gives the exact signed difference
$$
\begin{aligned}
D(X)&=\int_{1/2}^X \frac{S(y)}{\sqrt y}\,k(X/y)\,dy\\
&=\frac1{\sqrt X}\int_0^X \left(1-\frac12\sqrt{X/x}\right) B(x)\,dx\\
&=\sum_{\substack{q\ {\rm smooth}\\q<2X}}\int_{q/2}^{\min(q,X)}
          \left(t^{-3/2}-\frac{t^{-1}}{\sqrt X}\right)dt . \tag{3}
\end{aligned}
$$
For the last equality integrate by parts against $w(q/x)/q$. Its derivative is $x^{-2}$ on $q/2<x<q$ and zero off that strip. The primitive of the preceding weight is $x-\sqrt{Xx}$ and vanishes at both endpoints. Every integrand in the last line is nonnegative. Increasing $X$ only increases its value and opens more of its interval. Thus
$$
0\le D(X)\ \uparrow\ C=\frac{2(\sqrt2-1)}
 {(1-2^{-1/2})(1-3^{-1/2})}<7 .
$$
In the first line of (3) both signs pass through the same positive weight from (2). Dropping that weight with its two actual bounds gives, at every cutoff,
$$
U_-(X)\le5\,U_+(X),\qquad U_+(X)\le5\{U_-(X)+C\}. \tag{4}
$$
No convergence assumption on either area enters. They can both grow while the difference of the two weighted areas stays below seven.

## What a zero would have to pay at every cutoff

Count odd multiples positively and even multiples negatively. For $s=\rho$ a nontrivial zeta zero with $\beta=\Re\rho>0$ define
$$
K_\rho(v)=v^\rho\sum_{n\le v}(-1)^{n-1}n^{-\rho}.
$$
It is zero for $v<1$ and $|K_\rho(v)|\le1+|\rho|/\beta$ for $v\ge1$. To see the uniform bound, let $p(v)$ be 1 when $\lfloor v\rfloor$ is odd and 0 otherwise. Partial summation writes the finite sum as $v^{-\rho}p(v)+\rho\int_1^v p(t)t^{-\rho-1}dt$. At a zero the integral over $[1,\infty)$ is zero. This follows from the alternating eta identity, or from the Mellin transform of the project's original two-mark residue clock. The remaining integral over $[v,\infty)$ has magnitude at most $v^{-\beta}/\beta$. [Finite alternating reader at a stock zeta zero](PALRH/AlternatingRead.lean)

Let $g(n)=\mathbf1_{(n,6)=1}$ and $h(n)=g(n)-2\mathbf1_{2\mid n}g(n/2)$. Apply the rough version of (1) at $x$ and $x/2$ and subtract. The output $W_0(x)=w(1/x)-w(2/x)$ is positive in the interior of $[1/2,2]$ and vanishes outside that interval. Grouping the same input after integration gives, for $X\ge2$,
$$
X^\rho\int_{1/2}^2 W_0(x)x^{-\rho}dx
=\int_{1/2}^X S(y)\,[K_\rho(X/y)-K_\rho(X/(2y))-K_\rho(X/(3y))+K_\rho(X/(6y))]\,dy . \tag{5}
$$
Indeed $h$ is the alternating sequence after removing the multiples of 2 and 3 by divisor convolution with $\delta_1-\delta_2-\delta_3+\delta_6$. A multiplier $n$ on the right comes from $x=ny$ and contributes $(X/(ny))^\rho$. There is no scale beyond $X$ in (5).

The left moment is elementary. Integrate $(2-1/x)x^{-\rho}$ from $1/2$ to 1 and $(2/x-1)x^{-\rho}$ from 1 to 2. It gives
$$
d_\rho=\frac{(2^\rho-1)(2^{1-\rho}-1)}{\rho(1-\rho)}\ne0
\qquad(0<\beta<1).
$$
Combining this exact nonzero reading with the four bounded readers proves
$$
V(X):=\int_{1/2}^X |S(y)|\,dy
\ \ge\ c_\rho X^\beta,\qquad
c_\rho=\frac{|d_\rho|}{4(1+|\rho|/\beta)}>0 \quad (X\ge2). \tag{6}
$$
In particular $U_+(X)+U_-(X)\ge c_\rho X^{\beta-1/2}$. Equation (4) forces both signs to contribute at that order if $\beta>1/2$. A single critical-line zero also has a consequence at every later endpoint. Integrating (6) by parts gives
$$
U_+(X)+U_-(X)=\frac{V(X)}{\sqrt X}
  +\frac12\int_{1/2}^X\frac{V(y)}{y^{3/2}}\,dy
  \ \ge\ \frac{c_\rho}{2}\log(X/2).
$$
Now (4) forces each sign-area to grow at least logarithmically. This part needs the existence of one critical-line zero. Hardy proved infinitely many. [Hardy’s 1914 paper](https://fr.wikisource.org/wiki/Page:Comptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences,_tome_158,_1914.djvu/1014)

## Exact rational costs at the fourth powers

On $j^4\le y\le(j+1)^4$, the edge lies within $O(j^{-2})$ of the chord between the two true endpoint readings. The [earlier interpolation proof](what-the-last-two-rows-carry.md) supplies this bound and its version in the coordinate $1/y$. For the true rough Möbius signs the latter error is $o(j^{-2})$, using the all-short-interval theorem on the two boundary strips. The chord is a convex combination in either coordinate. Also $\int_{j^4}^{(j+1)^4}dy/\sqrt y=4j+2$. Therefore
$$
U_\pm(J^4) \le O(1)+O(A_\pm(J))+O(\log J).
$$
Using the actual $o(j^{-2})$ remainder replaces the last term by $o(\log J)$. This sharper transfer carries the unconditional logarithmic lower bound to both rational sums. The elementary $O(\log J)$ already suffices for the positive-power obstruction. [Matomäki and Teräväinen, Theorem 1.1](https://arxiv.org/pdf/1911.09076)

There is a converse estimate for the sum of both signs. The integral of the absolute value of a line segment with endpoints $u,v$ on a unit interval is at least $(|u|+|v|)/4$. For opposite signs the exact value is $(u^2+v^2)/(2(|u|+|v|))$. For equal signs it is $(|u|+|v|)/2$. The actual edge differs from the straight chord in $y$ by $O(j^{-2})$ on the interval between the two fourth powers. The integer chord bound and the $O(1/y)$ cost of rounding $y$ prove this even away from integer rows, since the endpoint slopes have magnitude at most one. Also $((j+1)^4-j^4)/(j+1)^2\ge j$ for $j\ge1$. Integrating on these intervals and summing gives
$$
 A_+(J)+A_-(J)\ \ll\ U_+(J^4)+U_-(J^4)+1+\log J .
$$
Consequently either sampled account bounds the other up to an absolute constant factor and an additive $O(1+\log J)$, already at finite $J$. The logarithmic lower bounds then give $A_+(J)\asymp A_-(J)$ for all sufficiently large $J$. This compares their actual sizes as well as their exponents.

Let $\Theta$ be the supremum of $1/2$ and the real parts of the nontrivial zeta zeros. For each choice of sign there is a genuine limit over all terminal indices,
$$
\boxed{\displaystyle
\lim_{J\to\infty}\frac{\log(1+A_\pm(J))}{\log J}=4\Theta-2 .} \tag{7}
$$
The lower bound follows by taking each zero in (6), applying (4), and using the fourth-power transfer. If $\Theta=1/2$, nonnegativity suffices for the exponent. For the upper bound, when $\Theta<1$ the established estimate for the true edge gives $|s_H|\ll_b H^{b-1}$ for every $\Theta<b<1$. Thus $A_\pm(J)\ll_b J^{4b-2}$. Let $b$ tend down to $\Theta$. At $\Theta=1$ the unconditional bound $|s_H|\le1$ gives $O(J^2)$. This upper comparison invokes the Balazard–Saias estimate in the zero-free half-plane indexed by $\Theta$. It assigns no value to $\Theta$. [Derivation for this edge](what-the-last-two-rows-carry.md) · [Balazard–Saias estimate reproduced by Báez-Duarte](https://arxiv.org/pdf/math/0205003)

The smaller of the two sums has the same limit. Consequently the finite criterion in the introduction allows the sign to vary with the checkpoint. If a zero lies off the line, symmetry supplies a zero on its right and both accounts eventually exceed every fixed smaller power in (7).

## An unusually long first plateau

An integer recurrence with outward rounding examines every integer side from 1 through $52^4$. The first strictly negative side is **6,513,933**. Every earlier lower endpoint is positive. A separate direct evaluation of the defining reciprocal sum brackets the readings immediately before and at the crossing. At $J=50$ the sampled negative account is exactly zero. That single checkpoint satisfies every integer-power inequality at once. The theorem still requires arbitrarily late checkpoints. At $J=52$, the positive account is about $2.57916913$ and the negative one about $0.00004374055$. Formula (6) and the short-interval transfer prove both must eventually exceed any fixed number.

For five smaller cuts through $X=144$, two independent integrations enclose the same signed difference in (3). One splits the actual row function at its corners and sign changes. The second uses only the positive smooth labels. At the larger common cut $X=7{,}313{,}664$, the latter difference is about $6.63041593$. Three intervals of width 2,048 have independently enclosed positive, negative and positive contributions there. [Runnable arithmetic](../receipt-archives/check_pal_signed_areas.py) · [Raw intervals and scope](../receipt-archives/2026-11-25-pal-signed-areas.json)

## Trying to close the estimate by a fixed phase

The real kernel has a positive lower bound at every scale. One possible way to finish would be to put its entire complex response in a single open half-plane whose boundary passes through zero. This can be tested on the actual kernel. Direct integration term by term initially for $\Re z>1/2$ gives
$$
F(z)=z\int_1^\infty k(v)v^{-z-1}\,dv
     =\frac{(s-1)\zeta(s)}{2s},\qquad s=z+\tfrac12.
$$
The left side is holomorphic for $\Re z>0$ by (2), so the formula extends there with the removable value at $s=1$. An open half-plane as above would exclude every right-side zero.

At $s=9/16+133i/4$ the real part of $F$ is strictly between $-0.044$ and $-0.018$, and its imaginary part is between $0.211$ and $0.237$. The independent calculation uses $N=256$, the explicit half endpoint, and the integral remainder of the trapezoid rule on each unit interval for $x^{-s}$. That gives
$$
\zeta(s)=\sum_{n<N} n^{-s}+\frac{N^{1-s}}{s-1}+\tfrac12 N^{-s}+R,\qquad
|R|\le\frac{|s(s+1)|N^{-1-\Re s}}{8(1+\Re s)}.
$$
Indeed the error kernel on each interval is bounded by $1/8$ and $|(x^{-s})''|=|s(s+1)|x^{-\Re s-2}$. The Python replay bounds logarithms and exponentials with integer intervals. For positive real $z$, $F(z)$ is positive by (2). A rotation putting that value in the open right half-plane must have positive cosine. The sum of the rotated real parts at the displayed frequency and its conjugate is then negative. Thus **no single rotation can certify this zero exclusion**, even though the physical weights are positive. The nonzero imaginary part keeps the particular tested frequency away from zero. [Enclosures and explicit remainder](../receipt-archives/check_pal_signed_areas.py)

## Unresolved

Show one of the two actual accumulated costs is subpower at arbitrarily late checkpoints. Equality (3) pays their signed difference for every cutoff. Equations (4) and (6) show why the common growth still matters and why a globally bounded account is untenable. The [Lean theorem](PALRH/FourthAccounts.lean) derives bare Mathlib RH from exactly these cofinal rational inequalities, including the choice of sign at each checkpoint. Its dependencies prove the finite zero bill (6), fourth-power interpolation and sign comparison. The formal upper allowance for the smooth source is 16, sufficient for that implication. Equation (3) gives the sharper constant below 7 on paper. The exponent identity and the unconditional logarithmic lower bound are paper results. Smoothed Möbius-convolution criteria have a classical history, and Pintz proved related lower average estimates for the sharp Mertens function. The positive rectangle, alternating test, and rational fourth-power accounts here are given with their derivations and source roles. [Báez-Duarte on convolution criteria](https://arxiv.org/abs/math/0504402) · [Pintz on averages and short ranges](https://matwbn.icm.edu.pl/ksiazki/aa/aa42/aa4214.pdf)
