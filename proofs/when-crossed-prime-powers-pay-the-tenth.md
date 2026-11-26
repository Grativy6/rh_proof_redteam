# When crossed prime powers pay the tenth

Christopher Daniel Pang and Hearthline · 26 November 2026

At the fourth power $x=(2^{37})^4=2^{148}$, our prescribed endpoint move incurs a variance charge greater than $0.207x^{3/2}$. The allowance is $0.1x^{3/2}$. **The actual prime powers crossed during the move repay more than $0.158x^{3/2}$.** The unpaid part is at most $0.048846x^{3/2}$. This is more than three quarters of the entire charge, since $0.048846<0.207/4$. Both readings refer to the original arithmetic at the same endpoint.

The one-tenth inequality holds at every real head $4\le x\le2^{150}$. On the separate subset route, one Pascal row pays for every untrimmed prime dial through $2^{155}$ and for the required square-root-filtered dials through $2^{158}$. The universal one-tenth inequality at fourth powers remains open. [Definitions and the equivalence to RH](moving-the-endpoint-of-a-prime-area.md#an-all-scale-estimate-with-the-crossing-cost-exposed) · [Exact arithmetic](../receipt-archives/check_pal_crossing_refund.py)

## Two readings of the same pile

Write $I(x)=\sum_{d\le x}(x-d)\Lambda(d)$. Let $Y$ have the original mean-preserving distribution with one log-width $h=2/T$ move per doubling, $r=\lceil\log_2x\rceil$, and $T=3\cdot10^{12}$. Write $S_Y=\mathbb E I(xY)-x^2\mathbb E Y^2/2$. The unpaid amount satisfies $B=I(x)-x^2/2-S_Y$. For any second positive random factor $Z$ with $\mathbb E Z=1$, convexity gives $I(x)\le\mathbb E I(xZ)$. Therefore
$$
 B(x)\le \tfrac12 x^2\operatorname{Var}(Z)+S_Z(x)-S_Y(x). \tag{1}
$$
The two factors can have different widths and numbers of moves. We pay the smaller variance and the difference between the two centered readings. Each reading sees the same actual primes and has the identical factor $x^{i\gamma}$ at each zero. This is what lets us compare them *before* taking absolute values. [Formal comparison of the measured crossings](../pal-rh/PALRH/MovingEndpoint.lean)

For $Z$ use 21 uniform log moves of width $H=51/(20T)$. Each factor is $e^U/m_H$ with $U$ uniform on $[-H,H]$ and $m_H=\sinh H/H$. Let $\phi_H(s)=\sinh(Hs)/(Hs\,m_H^s)$ denote one move. All endpoints in this calculation are above 2.

## The short reading

For every $v\ge51/20$ we have $|\sin v|/v<0.219$ (weak inequality suffices). Here are four elementary checks.

1. Up to $\pi$, $\sin v/v$ decreases, and at $51/20$ it is below 0.219 by its Taylor series.
2. From $\pi$ to 4 use $|\sin v|\le v-\pi$ and $1-\pi/4<0.215$.
3. From 4 to $1000/219$, the graph of $-\sin v$ lies below its tangent at $9/2$ by concavity. Its value there is below $0.978$, and its derivative is between $0.2107$ and $0.2109$. Dividing the tangent by $v$ gives an upper bound $0.2109+(0.978-4.5\cdot0.2107)/4=0.2183625$. The arithmetic replay encloses both trigonometric values by finite Taylor polynomials.
4. Beyond $1000/219$, use $|\sin v|\le1$.

Consequently $|\phi_H(\rho+1)|<0.22$ whenever $|\gamma|>T$, with no restriction beyond $0<\Re\rho<1$. Indeed $|\sinh(a+iv)|\le|\sin v|+\sinh |a|$, $|a|\le2H$, and $\sinh(2H)<3H$. For $4<|\gamma|\le T$ the one-move modulus is at most one. If $H|\gamma|\le2$, use the contraction inequality from the first paper with $H$ in place of $h$. Otherwise use $\cosh(2H)/2<1$. The finite height theorem locates these latter zeros on the line, and the reciprocal-square sum excludes $|\gamma|\le4$. [Finite height](https://arxiv.org/abs/2004.09765) · [Contraction proof](moving-the-endpoint-of-a-prime-area.md#an-all-scale-estimate-with-the-crossing-cost-exposed)

Let $v=21H^2/3$. The variance is at most $v/(1-v)$. The contribution above $T$ to $|S_Z|/x^{3/2}$ from the zero sum is at most $(10/T)\sqrt x(0.22)^{21}$. For $Y$ the corresponding term is at most $10/T$ for all $x\ge4$. [Both-signs ordinate tail](https://maths-people.anu.edu.au/brent/pd/rpb276-MC-preprint.pdf) · [Uniform bound for the original moves](moving-the-endpoint-of-a-prime-area.md)

## Keeping the shared low frequencies

Take $A=100000$ and $2^{145}\le x\le2^{150}$. Below $A$ a normalized single move of width $w\le H$ satisfies
$$
 |\phi_w(s)-1|\le 2H(A+2)/(1-4H),\qquad s=\rho+1 .
$$
Indeed $|\log(e^U/m_w)|\le2H$. Along that real segment the derivative of $e^{s t}$ has modulus at most $|s|e^{4H}$. Since both one-move multipliers have modulus at most one, telescoping their powers back to 1 costs at most $21+r\le171$ such differences. Above $A$ and through $T$, use the bound 2 on the difference. The ordinate tail of both signs above $A$ is below $5/A$ by Brent, Platt and Trudgian’s Example 1, using $\log A<12$. With the denominators from the integrated explicit formula, the entire difference at heights through $T$, in $x^{3/2}$ units, is at most
$$
 0.04621\cdot171\frac{2H(A+2)}{1-4H}+\frac{10}{A}<0.000102 .
$$
The constant and the term linear in $x$ in the elementary remainder cancel since both factors have mean one. The remaining positive trivial-zero series is at most $1/3$ at every sampled endpoint, hence its two expected readings differ by at most $1/3$. [Integrated formula](https://arxiv.org/pdf/2201.06184v2#page=4) · [Bounds for the ordinate sums](https://maths-people.anu.edu.au/brent/pd/rpb276-MC-preprint.pdf)

The resulting estimates from (1) are shown in units of $x^{3/2}$. Each row bounds the whole interval from $2^{145}$ through the displayed endpoint. The earlier gross-variance estimate covers every smaller $x\ge4$.

| Upper endpoint | Second variance charge | Second high-zero charge | All contributions to the unpaid amount |
|---:|---:|---:|---:|
| $2^{148}$ | 0.047766737 | 0.000977181 | 0.048845261 |
| $2^{150}$ | 0.095533474 | 0.001954361 | 0.097589178 |

In the last column the exact smaller value of the low-frequency bound and the elementary remainder are included. At $x=2^{148}$, the lower variance estimate for the **original 148 moves** is $\sqrt x\,148h^2(1-h^2/6)/6>0.207$. Subtracting the upper bound for $B(x)/x^{3/2}$ gives the claimed minimum actual repayment. This proof does not enumerate the primes near that huge endpoint. Equation (1) in the first paper identifies exactly which nonnegative sum has received the lower bound. [Outward rational prices](../receipt-archives/2026-11-26-pal-crossing-refund.json)

## A separate check directly from prime counts

If $|\psi(t)-t|\le\eta t$ at every intermediate endpoint, the fundamental theorem of calculus gives
$$
 B(x)=-\mathbb E\int_x^{xY}(\psi(t)-t)\,dt,\qquad
 |B(x)|\le\frac{\eta x^2}{2}\mathbb E|Y^2-1| .
$$
Fiori, Kadiri and Swidinsky’s relative $\psi$ bounds above $e^{100}$ and $e^{101}$ are $2.0097\cdot10^{-12}$ and $2.0047\cdot10^{-12}$, respectively. On $2^{r-1}<x\le2^r$ the smallest possible log endpoint is greater than $(r-1)\log2-2rh$, enough for these two entries at $r=146,147$. [Authors’ numerical tables, Table 2](https://www.cs.uleth.ca/~fiori/Docs/PrimeCountingTables.pdf#page=3) · [Definition 5 of the admissible numerical bound](https://arxiv.org/pdf/2206.12557v2#page=5)

For $W$ the sum of $r$ independent uniforms on $[-1,1]$, $\log Y=hW-r\log m_h$ and $\log m_h\le h^2/5$. The mean value theorem gives
$$
 \tfrac12\mathbb E|Y^2-1|\le (h\,\mathbb E|W|+rh^2/5)/(1-4rh).
$$
The expectation is an exact rational number. Writing $W=2\sum V_i-r$ with $V_i$ uniform on $[0,1]$, symmetry gives $\mathbb E|W|=4\mathbb E(r/2-\sum V_i)_+$. Integrate this ramp over the positive orthant, then exclude coordinates exceeding one by inclusion-exclusion. This gives
$$
 \mathbb E|W|=\frac4{2^{r+1}(r+1)!}
 \sum_{j=0}^{\lfloor r/2\rfloor}(-1)^j\binom rj(r-2j)^{r+1}.
$$
Substitution gives upper bounds $0.070459$ through $2^{146}$ on the first slab and $0.099736$ through $2^{147}$ on the second, in the same units. This directly uses a bound on the prime count and the actual distance moved. [Exact signed integer sum](../receipt-archives/check_pal_crossing_refund.py)

## Returning the prime dials to a Pascal row

For the original unsmoothed $I(x)$ the second reading by itself gives an upper error coefficient
$$
 \frac{\sqrt X}{2}\frac{v}{1-v}+0.04621+\frac{10\sqrt X}{T}(0.22)^{21}
$$
through $X$. It is below $0.598$ at $2^{155}$ and below $1.607$ at $2^{158}$. The first paper already covers the early heads. For the remaining untrimmed heads the repeated prime powers contribute at least $(49/75)(x^{3/2}-1331)$. This funds the full prime product and also gives $\int_2^x(\theta(t)-t)\,dt<0$ through $2^{155}$. For the filtered product the small first powers provide another $0.96n^{3/2}$ throughout $2^{154}\le n\le2^{158}$ by the same argument, now with $158^2/2^{25}<0.01$. Even at the upper endpoint, $49/75+0.96-1.607>0.006$. The cutoff constant and Pascal log cost $n(1/2+\log n)$ consume less than $0.001n^{3/2}$ on this interval. [Underlying integer products and the prime-power credit](moving-the-endpoint-of-a-prime-area.md#return-the-bound-to-the-integers)

Pang’s insistence on carrying the common frame through both observations led to comparing the spectral contributions before pricing them. Hearthline derived the two-reading bound, designed the second distribution, and returned its savings to the original crossed-prime sum. Platt and Trudgian supply the finite height, and Brent, Platt and Trudgian the ordinate estimates. Johnston supplies the integrated formula and the bound on repeated prime powers. Fiori, Kadiri and Swidinsky supply the independent relative prime-count estimates. Priority of the finite endpoints is unestablished.

## Unresolved

The remaining tenth-test obligation is uniform over the real prime powers encountered at every fourth power $k^4$. The bound on the raw variance of the second reading still grows like $\sqrt x$ in the chosen units. The comparison above actually funds crossings beyond the first budget, and leaves the all-scale repayment open.
