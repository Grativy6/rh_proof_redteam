# The signed reading of the original ruler

Christopher Daniel Pang and Hearthline · 26 November 2026

The same kernel that prices the two sides of a square gives an exact signed average of the Möbius walk on every board. It also builds upper and lower fits with arbitrarily small total area. The remaining RH question concerns how rapidly the signed counts grow. [Prime-square experiment and precise remaining obligation](../proofs/which-prime-squares-can-change-the-walk.md)

## An all-size equality with the sign attached

Write $M(x)=\sum_{n\le x}\mu(n)$, with $M(x)=0$ below 1. Use the original cutoff $q(t)=(1-t)^5(7t-1)$ for $0\le t\le1$ and zero for $t>1$. Write $w(v)=\sum_{j\ge1}q(jv)$ for $v>0$. Only finitely many terms occur at each input. The earlier curvature proof shows that $w(v)=\mathbb E(V-v)_+$ on $0<v\le1$ for a variable $V\in[0,1]$ with mean $1/2$. Thus $P(v)=-w'(v)$ belongs to $[0,1]$ and decreases. On $0<v\le1/2$ it is at least $9/16$, obtained by evaluating $-q'(1/2)$ since $q'(1)=0$. We also use $w(1)=0$, $w(1/2)=5/64$, $\int_0^1w=1/7$ and $|q|\le1$. [Polynomial, convexity and endpoint values](why-the-doubled-ruler-keeps-seven-eighths.md)

For every real $X\ge1$,
$$
 \int_0^1 P(v)M(Xv)\,dv=\sum_{j\le X}\mu(j)w(j/X)=q(1/X). \tag{1}
$$
Integrate the indicator of $j\le Xv$ against $P$ to get the first equality. Grouping the finite double sum by $m=j\ell$ leaves $q(m/X)\sum_{j\mid m}\mu(j)$. Only $m=1$ remains. At integer $X$ the same identity before interpolation says that each signed prefix is charged the difference between two adjacent integer ruler weights. Stock Lean proves the exact finite equality with its original common denominator. [Finite signed balance](PALRH/RulerBalance.lean)

Replacing the signs with positive squarefree indicators keeps the occupied positions and the squared sizes of all steps. At $X=3$ it changes the left side of (1) by $2w(2/3)=22/729$. This is where the one-sided inference would fail for that control.

## Positive upper and lower fits for any area tolerance

Take an even integer $N\ge2$ and use the integer-grid row
$$
 F_N(t)=\sum_{j<N,\ j\ge1}\mu(j)\,[w(jt)-w(Nt)] .
$$
For $t\ge1/N$, Möbius inversion gives $F_N(t)=q(t)$, including the boundary where $w(1)=q(1)=0$ in the last term as applicable. For $0<u\le1$,
$$
 F_N(u/N)=u\int_0^1 M(Nv)P(uv)\,dv .
 \tag{2}
$$
Integrating one step from $j/N$ to 1 gives $w(ju/N)-w(u)$. Thus $|F_N-q|\le1+D_N$ everywhere, where $D_N=N^{-1}\sum_{j=0}^{N-1}|M(j)|$ is rational.

Set $A_N=(64/5)(1+D_N)$. The two finite rational rows
$$
 F_N(t)-A_N w(Nt/2)\ \le\ q(t)\ \le\ F_N(t)+A_N w(Nt/2) \tag{3}
$$
bracket the target on every real $t>0$. The extra row is at least $5/64$ on the only interval where a correction is required, is nonnegative elsewhere, and vanishes past $2/N$. The exact area between the two brackets is
$$
 \frac{256}{35}\,\frac{1+D_N}{N}.
$$
The signed area of their midpoint is $\frac17\sum_{j<N}\mu(j)(1/j-1/N)$. The prime number theorem for the Möbius sum gives $D_N=o(N)$. Its quantitative version puts the displayed width in $O_A((\log N)^{-A})$ for every fixed $A>0$. This constructs an actual pair for every prescribed positive area tolerance. The root-scale rate is a stronger requirement. At $N=34$ the extra row has label 17, the mean absolute walk is $31/17$ and the exact total width is $6144/10115$. [Directed sample checks and exact coefficients](../receipt-archives/check_pal_square_switches.py) · [Lee and Leong, unconditional quantitative Möbius bounds](https://arxiv.org/pdf/2208.06141v5)

For comparison the earlier linear divisor rows can also earn arbitrary positive area accuracy without an optimizer. Put $H(t)=(1-t)_+$, $U(t)=\sum_{m\ge1}H(mt)$, $g(t)=U(t)-1/(2t)$. On $1/(m+1)<t<1/m$,
$$
 g(t)=-\tfrac12+\tfrac t2\{1/t\}(1-\{1/t\}),\qquad
 g'(t)=\tfrac12[t^{-2}-m(m+1)] .
$$
Consequently $|g|\le1/2$ and $|g'|\le1/t$ also beyond 1. For each fixed positive $t$ the variation of $g(vt)$ over $1\le v\le N$ is at most $\log N$. Summation by parts bounds $\left|\sum_{j<N}\mu(j)g(jt)\right|$ by $(1/2+\log N)\max_{j<N}|M(j)|$. Balance the finite row with coefficient $c_N=-N\sum_{j<N}\mu(j)/j$ at label $N$. At $t=1/N$ exact reconstruction gives $c_N=2[\sum_{j<N}\mu(j)g(j/N)-H(1/N)]$. The true error of the balanced row is therefore at most $R=2+(1+2\lceil\log_2N\rceil)\max_{j<N}|M(j)|$ everywhere and zero from $t=1/N$ upwards.

The balanced pair $U(v)-2U(2v)$ is nonnegative and at least $(1-v)/2$ for $0<v\le1$. Indeed the successive decreases of the convex sequence $(1-mv)_+$ are nonincreasing, and the odd decreases contribute at least half of their total. Add or subtract $4R[U(Nt/2)-2U(Nt)]$. This produces genuine upper and lower rows for the original linear ramp, exact from $2/N$ upwards, with total width $O(R/N)$. The same unconditional decay theorem makes this tend to zero faster than any reciprocal logarithmic power. The previously observed finite gains alone did not give an all-tolerances construction for this one-sided area norm. [Original weights and cost obstruction](../proofs/why-the-old-divisor-rows-have-to-move.md) · [Classical arithmetic approximation and the distinct critical norm, Báez-Duarte](https://arxiv.org/pdf/math/0011254v1)

## Read a hypothetical zero on a finite head

For $\Re s>0$ the Mellin transform of $q$ is
$$
 Q(s)=\frac{720(s-1)}{s(s+1)(s+2)(s+3)(s+4)(s+5)(s+6)} .
$$
Use $q(t)=-[t(1-t)^6]'$ and integrate by parts. For $\Re s>1$, absolute convergence and scaling give $\mathcal M w(s)=\zeta(s)Q(s)$. The bounded compactly supported $w$ has a holomorphic Mellin transform on $\Re s>0$. The zero of $Q$ cancels the pole at 1, so the identity continues to that half-plane.

Fix a nontrivial zero $\rho=\beta+i\gamma$. Retain (2) for real $X\ge1$, with coefficients at positive integers $j<X$ and a single terminal dilation at $X$. Every such finite row has zero Mellin reading at $\rho$. Its difference from $q$ is supported on $t\le1/X$. On multiplying that difference’s integral by $X^\rho$ and substituting $u=Xt$ one obtains
$$
 \int_0^1 K_\rho(v)M(Xv)\,dv
   =-Q(\rho)X^\rho+\sum_{j=0}^6\frac{q_j}{(\rho+j)X^j},
 \quad K_\rho(v)=\int_0^1 u^\rho P(uv)\,du ,
 \tag{4}
$$
where $q(t)=\sum q_jt^j$ on the unit interval. The bounded finite head and $\beta>0$ justify the interchange. Here $|K_\rho|\le1/(1+\beta)$ and $Q(\rho)\ne0$. All seven correction terms are bounded independently of $X$.

For the ordinary Möbius walk János Pintz already proved a quantitative lower bound for $X^{-1}\int_1^X|M(t)|\,dt$ from a single zero. His 2026 paper records the 1982–83 result as equation (2.9) and develops stronger oscillation estimates. Our use for (4) is to retain this specific bounded kernel on the same board when its square labels are changed. [Pintz, equation (2.9)](https://arxiv.org/pdf/2608.24878v2#page=7)

## A complete board can choose its square switches

Choose real switches $\epsilon(p)\in\{-1,0,1\}$ once for each prime, and extend completely multiplicatively with $\epsilon(1)=1$. Factor $n=a^2d$ with $d$ squarefree. The new step at $n$ is $\epsilon(a)\mu(d)$. Its prefix sum is
$$
 S_\epsilon(x)=\sum_{a\le\sqrt x}\epsilon(a)M(x/a^2).
$$
The current proof works even when a new board chooses every switch afresh. The same switches must serve every prefix of that board.

At a putative zero with $\beta>1/2$, apply (4) to each $X/a^2$ and sum. The bounded correction is $O_\rho(\sqrt X)$. Extending the coefficient sum to infinity also costs $O_\rho(\sqrt X)$, since $\sum_{a>\sqrt X}a^{-2\beta}\ll_\beta X^{1/2-\beta}$. Thus
$$
 \int_0^1 K_\rho(v)S_\epsilon(Xv)\,dv
    =-Q(\rho)X^\rho E_\epsilon(2\rho)+O_\rho(\sqrt X),
 \qquad E_\epsilon(z)=\prod_p(1-\epsilon(p)p^{-z})^{-1}.
$$
The Euler product converges absolutely here. Its modulus is at least $\prod_p(1+p^{-2\beta})^{-1}=\zeta(4\beta)/\zeta(2\beta)>0$, **uniformly in every prime switch on the board**. It follows that the mean absolute prefix is $\gg_\rho X^\beta$ on each sufficiently large board.

The choice of side is free as well. Equation (1) gives
$$
 \left|\int_0^1 P(v)S_\epsilon(Xv)\,dv\right|
 =\left|\sum_{a\le\sqrt X}\epsilon(a)q(a^2/X)\right|\le\sqrt X.
$$
Write $A_\pm(X)=X^{-1}\int_0^X(\pm S_\epsilon(t))_+\,dt$. Since $P\ge9/16$ on the first half, the mean absolute value at $X/2$ is at most $(32/9)[2\min(A_+,A_-)+\sqrt X]$. Indeed the weighted total absolute mass equals twice the smaller of the two weighted masses plus the absolute signed mass. Each weighted one-side mass is bounded by its unweighted one. The same switches on the inner half still obey the uniform lower bound. Hence both $A_+$ and $A_-$ are $\gg_\rho X^\beta$ if this off-line zero exists.

At integer head $H$, let $B(H)$ be the least unnormalized one-side area across all legal prime switches and the two board-wide orientations. Only primes up to $\sqrt{H-1}$ occur, and the area is the integer sum over $0\le n<H$. On paper the following is equivalent to ordinary RH:
$$
 \forall r\ge1,\ \forall H_0,\ \exists H\ge\max(2,H_0),
 \qquad B(H)^{2r}\le H^{3r+1}. \tag{5}
$$
If $\beta>1/2$, fix $r$ with $2r(\beta-1/2)>1$ in the lower bound above. Conversely under RH one has $M(x)=O_\eta(x^{1/2+\eta})$, and hence $S_\epsilon(x)=O_\eta(x^{1/2+\eta})$ uniformly by $\sum a^{-1-2\eta}<\infty$. Choosing $\eta<1/(2r)$ gives (5). More generally, if $\Theta$ is the supremum of the real parts of the nontrivial zeros, then
$$
 \Theta=\lim_{H\to\infty}\frac{\log(\sqrt H+B(H)/H)}{\log H}.
$$
For $\Theta<1$ use $M(x)=O_\eta(x^{\Theta+\eta})$, from convergence of the Möbius Dirichlet series to the right of $\Theta$ and partial summation. For $\Theta=1$ use $|S_\epsilon(x)|\le x$ from the single step at each position. The lower bound takes each zero with $\beta>1/2$ in turn, and the explicit square root supplies the endpoint when $\Theta=1/2$. [Balazard–Saias estimate as stated in Báez-Duarte, Lemma 2.1](https://arxiv.org/pdf/math/0202141v2#page=3)

The independent Lean target proves a separate stronger-premise version. At each head one set of switches can be selected to bound all its prefixes by $Cm^b$ for each $b>1/2$, with $C$ independent of the head. The exact inverse uses coefficients $\epsilon(a)\mu(a)$ at the same squares and costs at most $\zeta(2b)$. Thus this prefix envelope suffices for stock RH. The sparse one-sided theorem (5) uses the preceding integral argument on paper. [Exact inverse and formal implication](PALRH/ColoredSquares.lean) · [Fixed challenge](checks/square-switches/SwitchChallenge.lean)

Christopher Daniel Pang’s PAL and GPPR insist on retaining the prime label while carrying its power. His Single-Cut Transport and DARK questions motivated fixing the switch on the whole board and testing what survives changes to its square layers. Hearthline derived the explicit brackets, bounded switch-uniform detector and one-sided transfer from the doubled ruler. The earlier mean-value results and the quantitative prime-number estimates retain the authorship identified above.

## Unresolved

Produce the sparse upper budget (5) on the genuine signed walk at unbounded heads. The shrinking ordinary-area brackets in (3) and their linear-ramp counterparts earn all positive tolerances in that area metric. They leave the square-root growth threshold in (5) open.
