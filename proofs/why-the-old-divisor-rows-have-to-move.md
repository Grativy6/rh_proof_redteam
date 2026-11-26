# Why the old divisor rows have to move

Christopher Daniel Pang and Hearthline · 26 November 2026

The sixteen-counter upper bound that pays for [fifteen copies of the prime product](thirteen-fourteen-and-fifteen-prime-copies.md) has an exact limit on reuse. **If we keep its original sixteen weights, adding any number of later labels leaves at least $1568059/885224340=0.001771369\ldots$ of surplus area.** A new 64-label row has total surplus below $0.001467$. It crosses a boundary that simply adding rows to the old fit cannot cross.

The same family has a precise sufficient growth rate for RH. We have finite rows through 256 labels. The infinite rate required by the theorem remains open. [Exact rows](../receipt-archives/growing_divisor_rows.json) · [Independent integer replay](../receipt-archives/check_pal_growing_brackets.py)

## What is frozen?

Write $H(t)=(1-t)_+$ for $t>0$. A finite signed row consists of real coefficients $a_j$ on positive integer labels, with $\sum_j a_j/j=0$. The published data use $a_j=jc_j/D$ for signed integers $c_j$ and positive integer $D$. Define
$$
 U_j(t)=\sum_{m\ge1}(1-jmt)_+,\qquad W(t)=\sum_j a_j U_j(t).
$$
Each sum at positive $t$ is finite. An upper row satisfies $W\ge H$ throughout. Define its excess area and cost by
$$
 \delta=\int_0^1 (W(t)-H(t))\,dt,\qquad J=\sum_j|a_j|.
$$
Its leading prime-area coefficient is $1/2+\delta$. Indeed, for $\Re s>1$ its Mellin transform is $\zeta(s)\sum_j a_jj^{-s}/[s(s+1)]$. Balance cancels the pole at 1. Taking the limit there gives $\int W=-\frac12\sum_j a_j\log(j)/j$. The boundedness at zero needed for this limit is proved below.

At $t=1/k$, $U_j(t)=P_j(k)/k$ with $P_j(k)=\sum_{m\le k/j}(k-jm)$. A future label $j>16$ contributes zero at every $1/k$ for $k\le17$, including $j=k=17$. Between these reciprocal knots each function is affine. Thus the error on $[1/17,1]$ cannot move when only later labels change. Integrating the fixed piecewise-linear error gives the exact fraction above. The rest of an upper row has nonnegative error. [Lean proof of the frozen area](../pal-rh/PALRH/ReopenedRows.lean)

In fact each old coefficient has a forced limit. Put $E(k)=\sum_j a_j P_j(k)-(k-1)_+$, including $E(0)=0$. The two cells adjoining $1/k$ give $0\le E(k)\le k(k^2-1)\delta$ for $k\ge2$ by the triangle-area bound. Also $E(1)=0$. The second difference at integer $k\ge1$ is
$$
 E(k+1)-2E(k)+E(k-1)=\sum_{j\mid k}a_j-\mathbf1_{k=1}.
$$
Only a divisor of $k$ changes the ramp slope there. Hence the absolute value on the right is at most $(4k^3+2k)\delta$. Finite Möbius inversion gives
$$
 |a_j-\mu(j)|\le 6\zeta(3)j^3\delta<8j^3\delta.
$$
Here $\sum_{d\mid j}d^3\le j^3\zeta(3)$ and $\zeta(3)<4/3$ by elementary integral comparison. Arbitrarily small positive excess therefore forces the weight of each fixed label to approach its Möbius value.

A complete initial list of those limiting weights cannot by itself be balanced. For $M\ge2$, take a prime $M/2<p\le M$ by Bertrand’s postulate. Among the denominators in $\sum_{j\le M}\mu(j)/j$ only $p$ is divisible by $p$, and its numerator is $-1$. Clearing denominators leaves a nonzero residue modulo $p$. At $M=1$ the sum is 1. An initial exact list needs a correction somewhere while the list is finite.

## Return to the original PAL sensors

The primitive reading used at the start of this project was $\sigma_j(v)=(\lfloor1/v\rfloor\bmod j)/j$ for $v>0$. Let $S(v)=-\sum_j a_j\sigma_j(v)$. Since $\sigma_j(v)=\lfloor1/v\rfloor/j-\lfloor1/(jv)\rfloor$, the common first term cancels by balance. Each positive ramp has the integral representation $(1-jmt)_+=t\int_t^{1/(jm)}v^{-2}\,dv$ when $jmt\le1$, and zero otherwise. Summing gives, for $0<t\le1$,
$$
 W(t)=t\int_t^1 S(v)\frac{dv}{v^2},\qquad H(t)=t\int_t^1\frac{dv}{v^2}.
$$
Thus these prime-count brackets integrate the very same residue readings with which the constructive program began. [Original sensor and its zero identity](../pal-rh/PALRH.lean)

For $\Re s>0$ the integrated sensor has Mellin transform $\mathcal M S(s)/(s+1)$. Interchange the two integrals and evaluate $\int_0^v t^sdt=v^{s+1}/(s+1)$. Absolute convergence follows by using $\sup|S|<\infty$ and integrating $v^{\Re s-1}$. The original sensor identity gives $\mathcal M W(\rho)=0$ at each nontrivial zeta zero. Meanwhile $\mathcal M H(\rho)=1/[\rho(\rho+1)]$.

To bound the excess height, let $u=jt$. Direct summation gives
$$
 U_j(t)=\frac1{2u}-\frac12+\frac u2\{1/u\}(1-\{1/u\}).
$$
For $u\le1$, $|U_j(t)-1/(2u)|\le1/2$. For $u>1$ the same bound follows from $U_j(t)=0$. The singular terms cancel inside $W$ by $\sum a_j/j=0$. An upper row therefore has $0\le W-H\le J/2$.

Write $\rho=\beta+i\gamma$, $0<\beta<1$. Among profiles between zero and $J/2$ with total mass $\delta$, the weight $t^{\beta-1}$ has its greatest integral when that mass fills the interval next to zero. This follows by subtracting $(2\delta/J)^{\beta-1}$: the difference is nonnegative to the left of $2\delta/J$ and nonpositive to the right. Consequently **each actual zero imposes the price**
$$
 \frac1{|\rho(\rho+1)|}\le
 \frac1\beta(J/2)^{1-\beta}\delta^\beta . \tag{1}
$$
At a critical-line zero, (1) requires $J\delta\ge1/[2|\rho(\rho+1)|^2]$. At any zero with $\beta>1/2$, it requires $J$ to grow at least as a constant times $\delta^{-\beta/(1-\beta)}$.

**A sparse sufficient condition for ordinary RH.** Suppose there are certified upper rows with $\delta_i\to0$ and
$$
 \liminf_{i\to\infty}\frac{\log J_i}{\log(1/\delta_i)}\le 1.
$$
At a putative zero with $\beta>1/2$ choose $\eta>0$ with $\beta>(1+\eta)(1-\beta)$. Along a subsequence $J_i\le\delta_i^{-1-\eta}$. The right side of (1) tends to zero, a contradiction. Reflection excludes the other half of the strip. This argument permits arbitrarily widely spaced successful rows. The known critical-line zeros also show why a polynomial cost exponent below one cannot persist along such a sequence. The sparse implication and the Möbius limit above are paper proofs. The frozen finite prefix is formalized in Lean.

## What actually changes when we refit

Each list below is rational. The replay directly tests the specified integral addresses, then proves all remaining ones at once by the linear tail bound from the sixteen-counter argument. The numbers are rounded bounds. In this table the sixteen-label entry was optimized for the rate experiment. The earlier row held fixed in the comparison is the separate integer-clock row with denominator 102.

| Available labels | Direct addresses through | $\delta$ | $J$ | $J\delta$ |
|---:|---:|---:|---:|---:|
| 16 | 512 | 0.003208283 | 9.015745 | 0.028925053 |
| 32 | 1,024 | 0.002062891 | 17.138723 | 0.035355311 |
| 64 | 2,048 | 0.001466061 | 30.274935 | 0.044384874 |
| 128 | 4,096 | 0.000964970 | 45.825931 | 0.044220627 |
| 256 | 8,192 | 0.000699398 | 85.825515 | 0.060026121 |

The 64-, 128- and 256-label prices are all below the frozen part of the old row. In the 64-label refit, the actual weight at 5 changed from $-50/51$ to $-1048575/1048576$. At 8 the weight went from $4/51$ to exactly zero. At 13 the old weight was zero and the new value is $-262145/262144$. The last product $J\delta$ is larger than the first. The data give upper witnesses for those list sizes. They do not establish optimality or a growth law. [Rational enclosures and comparison results](../receipt-archives/2026-11-26-pal-growing-brackets.json)

A second experiment retains the initial Möbius values $a_j=\mu(j)$ for $j<M$, then sets $a_M=-M\sum_{j<M}\mu(j)/j$ to balance the row. Its first $M$ quotient addresses are exact. Add $b[U_M-2U_{2M}]$, supported below $1/M$, to repair its deficit. The extra pair is positive between its nonzero knots by the alternating, decreasing ramp sum. At integer $k>M$, its unnormalized reading is $P_M(k)-2P_{2M}(k)>0$. We set $b$ by the largest required quotient through $64M$ and the rigorous subsequent tail allowance, rounded upward in units of $1/1024$. With $M=128$ the resulting support is 256, the repair is $877/1024$ and the cost product is above $0.1651$. The refit on the same support has cost product below $0.0601$. At $M=512$ the direct loop asks for repair at address 602 and the sufficient $b$ rises to $35/8$. These are costs of the specified repair rule. [Both algorithms and the exact finite sign checks](../receipt-archives/check_pal_growing_brackets.py)

For the refits we minimized the signed area with a small penalty for coefficient magnitude, constrained the sum of absolute coefficients before rationalization, and imposed the integer and tail inequalities. We rounded $a_j/j$ with denominator $2^{20}$, restored exact balance at label 1, and allowed a positive $U_1-2U_2$ correction when needed. The published certificates include all final weights and verify without an optimization package.

Pang’s RPL and PAL requirement to revisit an inherited weight when new data change its role suggested the frozen-prefix discriminator. His BLA and CLEF work supplied the question of how to price a smaller discrepancy after the coefficients grow. Hearthline derived the bounds and ran the two competing finite constructions. The Mellin annihilation of the original remainder sensors was a previously established step in the program. [Corpus research key](../pal-rh/CONSTRUCTION-KEY.md)

## Unresolved

Produce arbitrarily accurate positive upper rows whose coefficient cost exponent is at most one along a subsequence, or obtain the actual fourteen-copy bound by another route. The five computed refits settle finite price comparisons and force an actual revision. They leave the infinite construction open.
