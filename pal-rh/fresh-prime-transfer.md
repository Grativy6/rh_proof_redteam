# What one fresh prime does to an old fit

Christopher Daniel Pang and Hearthline · 25 November 2026

**An old coefficient can reverse sign, and genuinely distant primes each improve the fit while their improvements cannot be added independently.** This is an unconditional statement about the square-error geometry of the actual remainder functions. The Riemann–Pang Ledger supplies the single-fresh-factor square shell and the question of how much an old/detail split counts twice. DARK supplies the idea of removing the old response first, and CHARTER keeps the scale attached to the reading. The analytic endpoint uses the classical Nyman–Beurling–Báez-Duarte criterion. Historical priority for the asymptotic calculation is unassessed. [Pang’s RPL](https://doi.org/10.5281/zenodo.21894278) · [Corpus routes](CORPUS-ROUTES.md) · [Construction key](CONSTRUCTION-KEY.md)

## Watch the weight on 6

Our physical row is a positive integer $k$. Give it weight $w_k=1/[k(k+1)]$. Write $b_d(k)=\{k/d\}$ and $\langle f,g\rangle=\sum_{k\ge1}w_k f(k)g(k)$. The target is the constant 1. Fit it by real linear combinations of $b_2,b_3,b_6$. Then admit a fresh prime $p$ together with $b_p,b_{2p},b_{3p},b_{6p}$. All coefficients, including the old ones, may change. The squared error includes infinitely many rows in every fit.

| New primes added to the same parent | Coefficient on 6 | Least squared error |
| --- | ---: | ---: |
| none | $[0.60084,0.60086]$ | $[0.07828,0.07830]$ |
| 5 | $[-0.12594,-0.12561]$ | $[0.03718,0.03779]$ |
| 7 | $[-0.10067,-0.10004]$ | $[0.04824,0.04930]$ |
| 11 | $[0.14497,0.14586]$ | $[0.05796,0.05934]$ |
| 5 and 7 jointly | $[-0.41760,-0.41722]$ | $[0.02497,0.02591]$ |

The last line includes the union of the two four-reading groups. Effects containing both new primes, such as $b_{35}$, would be additional measurements. The identical old residue $5\bmod6$ for 5 and 11 cannot determine the sign. Counting the isolated 5 and 7 improvements on the unchanged parent **overestimates their joint improvement by between 0.01618 and 0.01877**. The signed mixed term in [the Lean energy calculation](PALRH/Gain.lean) explains where a simple addition can fail. Refitting in the enlarged space accounts for the whole Gram matrix.

**How the intervals were earned.** All columns in each calculation repeat with common period $L$. After a prefix ending at a multiple $M$ of $L$, the remaining mass is $1/(M+1)$. The largest and smallest of its $L$ residue-class masses differ by at most $w_{M+1}$ because differences across one period are bounded by the difference between corresponding first visits in successive periods, which telescopes. Put the average remaining mass in each class as a midpoint estimate. Rounding each head term down on a $10^{-16}$ grid then bounds the absolute error in each Gram or target entry by $e=Lw_{M+1}+M10^{-16}$. All readings lie in $[0,1]$.

Let $A_0,v_0$ be these rational approximations, $n$ the column count, $J=\|A_0^{-1}\|_\infty$, and $a_0=A_0^{-1}v_0$. Direct rational multiplication checks the inverse. When $Jne<1$, the true coefficients lie within $Je(1+\|a_0\|_1)/(1-Jne)$ of $a_0$ in the maximum norm, by applying the inverse perturbation bound to $v-Aa_0$. The squared-error optimum is $1-v^Ta$. All table intervals round outward. [Executable arithmetic](../receipt-archives/check_pal_prime_refits.py)

## Variable prime, fixed parent

Take any fixed finite independent family of old remainder columns $b_{d_i}$, with Gram matrix $A$, least-squares coefficient vector $\alpha$, and residual $r=1-\sum_i\alpha_i b_{d_i}$. An overbar denotes the **ordinary unweighted periodic mean**. In particular $m_i=\overline{b_{d_i}}=(d_i-1)/(2d_i)$ and $\bar r=1-m^T\alpha$. Choose distinct positive cofactors $a$ from a fixed finite set, and write $t_a=1/a$. Define
$$
H_{ab}=\int_0^\infty \{y/a\}\{y/b\}\,\frac{dy}{y^2},
\qquad \kappa=t^TH^{-1}t.
$$

Let $\alpha_p$ be the old coefficients after adding all $b_{ap}$ and refitting. Let $\Delta_p$ be the reduction in the squared error. As $p\to\infty$,
$$
\frac{p}{(\log p)^2}\Delta_p\longrightarrow \bar r^2\kappa,\qquad
\frac{p}{(\log p)^2}(\alpha_p-\alpha)\longrightarrow
     -\bar r\,\kappa\,A^{-1}m .
$$
If $\bar r=0$, the same argument gives $\Delta_p=O(1/p)$. The proof holds along positive integers, hence along the primes. The parent and cofactors are fixed in these limits.

1. For any bounded periodic $h$, split $\langle h,b_{ap}\rangle$ at $k=ap$. Below the cut the summand is $h(k)/[ap(k+1)]$. The centered sequence $h-\bar h$ has bounded partial sums, so its harmonic sum there is bounded by summation by parts. The remaining absolute contribution is at most $\|h\|_\infty/(ap)$. Thus $\langle h,b_{ap}\rangle=\bar h\,\log(p)/(ap)+O_{a,h}(1/p)$.
2. If $D_p$ is the new-columns Gram matrix, then $pD_p\to H$. Put $y=k/p$ in the entries. On compact subintervals of $(0,\infty)$ this is an ordinary Riemann sum with finitely many jump points. For $y<\epsilon<\min a$ the product of the two readings is $y^2/(ab)$, bounding the contribution by $(\epsilon+1/p)/(ab)$. Beyond $T$ the telescoping weights cost at most $p/(\lfloor pT\rfloor+1)$. These estimates justify both ends. The limiting matrix is positive definite. A zero-norm combination of the piecewise linear fractional parts vanishes on every interval of continuity. At the smallest selected positive cofactor its jump forces that coefficient to vanish. Repeat in increasing order; all earlier multiples already have zero coefficients. Hence $\kappa>0$.
3. Let $B_p$ be the old/new cross matrix. Eliminating the old coefficients gives the new Gram $S_p=D_p-B_p^TA^{-1}B_p$ and right-hand side $z_p=(\langle r,b_{ap}\rangle)_a$. Step 1 gives $p B_p/\log p\to mt^T$ and $pz_p/\log p\to\bar r t$. Therefore $pS_p\to H$ and $S_p^{-1}/p\to H^{-1}$. For all sufficiently large $p$ these inverses exist. The exact formulas $\Delta_p=z_p^TS_p^{-1}z_p$ and $\alpha_p-\alpha=-A^{-1}B_pS_p^{-1}z_p$ give the claims. For zero mean, $z_p=O(1/p)$ directly.

For the parent 2,3,6 the rational enclosures give $0.14168\le\bar r\le0.14170$ and $3.81942\le(A^{-1}m)_6\le3.81945$. Thus every sufficiently distant prime moves the fitted weight of 6 down by a positive but vanishing amount. Its limiting value is the **positive** old coefficient. The opposite signs for small and larger individual primes are compatible with this law. The hard question concerns many primes acting together as the old frame itself grows.

## Why the first shortcut fails and where to turn

For this parent there is a positive constant times $(\log p)^2/p$ of isolated gain for every sufficiently large prime. Summing those separate predictions over primes diverges. Indeed the finite Euler products dominate the partial harmonic sums by unique factorization, and $-\log(1-1/p)\le2/p$, so $\sum_p1/p$ diverges. The joint gain from any finite number of observations is bounded by the original error. Consequently single-prime gains cannot be credited repeatedly against the same parent.

There is a second obstruction using actual primes. Take successive primes $p<q$ along a sequence with $q/p\to1$; such a subsequence exists because an eventual fixed proportional gap would force $\sum_p1/p$ to converge. For each fixed $a$,
$$
p\|b_{ap}-b_{aq}\|^2\longrightarrow0 .
$$
In the Riemann-sum argument of step 2 the rescaled functions are $\{y/a\}$ and $\{y/[a(q/p)]\}$. Off arbitrarily small neighborhoods of the finitely many jumps on a compact interval they converge uniformly to each other. The jump neighborhoods have bounded weight away from zero, and the two tail bounds in step 2 are uniform for $q/p$ near one. Yet $p\|b_{ap}\|^2\to H_{aa}>0$. Thus the smallest eigenvalue of the pooled Gram on the $p$ scale can approach zero. Removing any fixed old projection preserves this obstruction because orthogonal projection onto the old complement is a contraction and the old correction to each scaled norm tends to zero.

The replacement is to carry the **joint** residual and to resolve genuine contrasts. When $q/p\to\lambda$ in a compact positive interval avoiding all ratios $a/b$ of the selected cofactors, the corresponding two-group limiting Gram is positive definite by the same jump argument at the distinct lengths $a,\lambda b$. The convergence argument works along every convergent ratio subsequence, so the normalized two-group conditioning is uniform on such compact intervals at sufficiently large scales for a fixed parent. A well-conditioned measurement can still have arbitrarily small correlation with a changing residual. The remaining task is a lower bound on that correlation, with control of the growing parent, or a different mechanism that supplies the missing all-scale gain.

## Unresolved

Pass from fixed-parent asymptotics to progress on the **actual changing residual**. Density of prime labels, positive finite Gram matrices, and an average-case estimate for an unrelated residual do not establish that step. The [key](CONSTRUCTION-KEY.md) retains the signed-event and aperture alternatives. The [Lean module](PALRH/Gain.lean) proves the exact energy updates and a genuine whole-row gain for every $p>2$ on the initial even-row residual. The matrix asymptotics on this page are a paper derivation with self-review.
