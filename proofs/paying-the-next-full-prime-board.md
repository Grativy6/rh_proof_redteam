# Paying the next full prime board

Christopher Daniel Pang and Hearthline · 26 November 2026

**Every cut of board 22 satisfies the original one-thirteenth test, in both directions.** Its last cut is $16^{22}=2^{88}$. The same calculation funds board 23 through $2^{91}$, exactly half of its observed horizon. Both guarded product comparisons and the placement of the original individual ticks are covered on these ranges. The previous published finite-range transfer stopped at complete board 21. [Original open comparison](one-thirteenth-of-a-returned-layer.md) · [Product and original tick addresses](one-product-one-direction-per-board.md)

This is a finite analytic result on paper. Its input about zeros is Platt and Trudgian’s published result through height $T=3\cdot10^{12}$. The contribution from all higher zeros is explicitly bounded. We evaluated the inequalities, with no direct enumeration of primes through $2^{88}$ and no assumption of global RH. [Finite zero input](https://arxiv.org/abs/2004.09765) · [Rational arithmetic and independent numerical replay](../receipt-archives/check_pal_finite_prime_budget.py)

| Board | All cuts covered through | Prime error, root and rounding cost | Available row quota |
|---:|---:|---:|---:|
| 22 | $2^{88}$ | $<159.583617$ | $>162.768758$ |
| 23 | $2^{91}$ | $<176.180402$ | $>177.230335$ |

The numerical columns use units of $\sqrt{16^j}=4^j$ for their respective board. The quota already sets aside the flag cells needed when individual clocks were rounded. In unscaled integer row units the two margins exceed 56,033,599,773,205 and 73,882,549,477,578 respectively.

## The finite estimate

Write $e(t)=\theta(t)-t$. For $599\le t\le10^{26}$ use Johnston’s Corollary 3.3, which extends the Schoenfeld-shaped bound $|e(t)|\le\sqrt t\log^2t/(8\pi)$ through $1.101\cdot10^{26}$. A possible half-weight convention at a prime costs at most $\log t$, included throughout. Below 599 the elementary Chebyshev bound suffices. The same finite theorem gives the price at the board root $x=4^{j+1}(j+1)^2$. [Johnston, equation (3.4) and Corollary 3.3](https://link.springer.com/article/10.1007/s11139-022-00616-x)

For a slab $L\le t\le U$ above $10^{26}$ choose fixed smoothing parameters
$$
 c=35,\qquad \varepsilon=c/T,\qquad a=1/4,\qquad F=(2\pi c)^{-1/2}.
$$
Set $B_L=0.98F\varepsilon L e^{-\varepsilon}$. We have $\log B_L>31.97$ throughout. Büthe’s smoothed explicit formula in Johnston’s equation (2.2) has an absolute additive error at most 2. Split its zero sum at $aT$ and $T$. The following are upper bounds in the original units:
$$
\begin{aligned}
 E_1&=\frac{\sqrt U}{2\pi}\log^2\!\frac{aT}{2\pi},\\
 E_2&=\frac{1+11c\varepsilon}{\pi c a^2}\log T\,
       \frac{\cosh(c\sqrt{1-a^2})}{\sinh c}\sqrt U,\\
 E_3&=\frac{0.16(U+1)}{\sinh c}e^{0.71\sqrt{c\varepsilon}}\log(3c)\log T,\\
 E_4&=e^{2\varepsilon}(\log U+\varepsilon)
 \left[\frac{2\varepsilon U F}{\log B_L}
       +2.01\varepsilon\sqrt U+\tfrac12\log\log(2U^2)\right].
\end{aligned}
$$

For $E_1$ use the normalized smoothing weight at most one on the line and the reciprocal-height sum of Johnston’s Lemma 2.2. Büthe’s Proposition 3, equations (4.1) and (4.2), pays $E_3$ for unrestricted heights and $E_2$ on the finite critical-line range. Its conditions include $aT\ge10^3$, $c\ge3$ and $\varepsilon\le10^{-3}$. Here $aT=7.5\cdot10^{11}$ and $\varepsilon<10^{-4}$. For $E_4$, Johnston’s Lemma 2.3 bounds the cost of removing the smoothing. Its Bessel factor $I_1(c)/(2\sinh c)$ is between $0.98F$ and $F$ at $c=35$. The positive defining series through index 80 and a geometric bound for the remainder independently put the ratio to $F$ in $[0.989187557660,0.989187557661]$. Replacing all positive numerator arguments by $U$ and the logarithmic denominator by its lower price at $L$ covers every interior point. [Büthe, corrected version, Proposition 3](https://arxiv.org/pdf/1410.7015v4) · [Johnston, §2 and equations (3.13)–(3.14)](https://link.springer.com/article/10.1007/s11139-022-00616-x)

Thus $|\psi(t)-t|\le E_1+E_2+E_3+E_4+2$ with the source’s endpoint convention. From $\theta(v)\le v\log4$, the prime powers add at most
$$
 \log4\,[\sqrt U+\lfloor\log_2 U\rfloor\,\lceil U^{1/3}\rceil]
$$
when passing to $\theta$. The replay uses a somewhat larger power of two for the cube-root bound. A further $\log U$ handles endpoint conventions. At $U=2^{88}$ the four analytic terms divided by $\sqrt U$ are bounded by $103.534841$, $1.375813$, $0.474594$ and $52.802577$. The unrestricted high-zero cost is already inside that sum.

## Paying the actual jobs

For $M=16^j$ and the observed endpoint $U_*$ of that board, our earlier integer tick result gives a row cost at most
$$
 \sup_{x\le t\le U_*}|e(t)|+|e(x)|+3U_*/x
$$
above the ordinary columns. The quota is $\lfloor x/13\rfloor-\lceil M/x\rceil$. The finite estimates in the table put this cost below that quota. Thus the upper product test fits, while the lower product test follows already from the smaller price without the $3U_*/x$ term. The same estimate pays the triangularly weighted one-thirteenth test. [Exact transfer from the prime error to the physical reading](../pal-rh/PALRH/ReturnedReading.lean) · [The two numerical head specializations in Lean](../pal-rh/PALRH/FiniteHorizon.lean)

For board 22 use the single slab $[10^{26},2^{88}]$. For board 23 put $Q=2^{88}$ and use consecutive boundaries $10^{26},Q,2Q,4Q,6Q,8Q$. In each slab the upper endpoint determines the positive costs while the lower endpoint determines $B_L$. The proof is uniform within each slab. The rational implementation encloses elementary functions outward, and a separate 75-digit decimal computation re-evaluates all four analytic terms on each recorded slab. The Lean specializations explicitly take the finite prime-error estimate as their input. The analytic derivation and its published finite zero input supply that estimate on paper.

At the full board-23 endpoint $2^{92}$, this particular estimate on its last quarter gives an upper-envelope coefficient above 306 in the same units, against a quota below 178. That upper envelope fails to pay the full next board. The actual prime reading beyond the covered range remains undetermined here. [All interval components, margins and full-head control](../receipt-archives/2026-11-26-pal-finite-prime-budget.json)

Pang’s PAL and BLA construction supplied the fixed unit and the requirement to price each source of error in the same row. Hearthline selected the smoothing parameters, derived the slab bounds and returned the finite estimates to the actual job counts. Büthe, Johnston, Platt and Trudgian supply the analytic and finite-zero results credited above.
