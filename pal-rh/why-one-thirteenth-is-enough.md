# Why one thirteenth of a layer is enough

Christopher Daniel Pang and Hearthline · 26 November 2026

For $j\ge0$, put $u=j+1$, $M=16^j$, $x=4^u u^2$ and $n=x^2$. These are still fourth-power boards since $n=(2^u u)^4$. Write $A_m=nm-m(m+1)/2$ and $P_m=\sum_{d\le m}(n-d)T_d$, where $T_d$ is the ordinary integer tick count when $2\le d$ and $\gcd(d,x!)=1$, and zero otherwise. Define

$$
 Z_m=P_m+xA_{\min(m,x)}-xA_m,\qquad D_j=\max_{0\le m\le M}|Z_m|.
$$

**Theorem.** RH is equivalent to $13D_j\le n^2$ for every $j\ge0$. In particular each individual comparison is a necessary consequence of RH. The direction to RH is proved in Lean from the displayed integer condition. The reverse direction uses a published analytic theorem under RH and the elementary bounds below. The return and both signs are fully visible in the independent statement. [Fixed Lean target](checks/returned-horizon/ReturnedChallenge.lean) · [Conditional proof and missing-strip obstruction](PALRH/ReturnedHorizon.lean)

## From the integer comparison to RH

The return satisfies $0\le xA_{\min(m,x)}\le xnx=n^2$. Thus the condition implies $|P_m-xA_m|\le2n^2$ for all observed cuts. Since $4M\le n$, finite summation by parts gives

$$
 \left|\sum_{d\le m}(T_d-x)\right|\le4n .
$$

Indeed if $F(m)=\sum_{d\le m}(T_d-x)$, exactly $P_m-xA_m=(n-m)F(m)+\sum_{i<m}F(i)$. The induction bounding the absolute value then costs at most $2/n$ times the supremum of the weighted error. The sieved tick estimate gives $|\sum_{d\le m}T_d-x\theta(m)|\le3n$. Consequently $|\theta(m)-m|\le7x=28\cdot4^j(j+1)^2$ for every $m\le16^j$. For any positive $m$ choose the first such $j$ to obtain the usual $O(\sqrt m(1+\log m)^2)$ estimate. Prime powers cost $O(\sqrt m)$, and the Mellin transform of the remainder excludes zeros with real part greater than one half. The functional equation excludes their reflections. [Finite untilting](PALRH/ShapeStrip.lean) · [Mellin proof](PALRH/UncalibratedPrime.lean)

## Reading a prime error back onto the same strip

The two-sided cost before weighting is especially simple. For $i\le x$, both the raw jobs and the corrected discrepancy vanish, because the gcd test excludes all those distances and the correction supplies their entire reference. For $x<i\le M$, put $e(t)=\theta(t)-t$ and write

$$
 F_i=\sum_{d=1}^i(T_d+x\,\mathbf 1_{d\le x}-x)
     =x(e(i)-e(x))+r_i,\qquad 0\le r_i\le3i.
$$

To see the last bound, each kept prime contributes between $x\log p$ and $1+(x+1)\log p$. The count of kept primes is at most $i$ and their total logarithmic weight is at most $\theta(i)\le2i$. Thus the formula includes the integer rounding on every individual clock. Finite summation by parts gives $Z_m=(n-m)F_m+\sum_{i<m}F_i$, with nonnegative coefficients of total weight $n$. In particular for any bound $|e(i)-e(x)|\le b$ at all observed $i>x$,

$$
 D_j\le n(3M+xb).
$$

This is an independent finite implication about the actual board. [Exact tick remainder](PALRH/PrefixReturn.lean) · [Formal transfer from observed prime errors to an integer board](PALRH/ReturnedReading.lean)

## Why the number thirteen works

When $j=0,1,2,3$, $M\le x$ and hence $D_j=0$. For $u\ge5$, $M\ge x\ge25,600$. Under RH, Schoenfeld gives $|e(y)|<\sqrt y\,\log^2y/(8\pi)$ for $y\ge599$. This expression is increasing throughout the relevant range. The previous estimate therefore gives

$$
 \frac{D_j}{n^2}\le
 \frac{\sqrt M\log^2 M}{8\pi x}
 +\frac{\log^2 x}{8\pi\sqrt x}
 +\frac{3M}{x^2}.
$$

Substitution gives $c(1-1/u)^2$ for the first term, with $c=(\log2)^2/(2\pi)$. The other two terms, multiplied by $u$, have sum

$$
 G(u)=\frac{(u\log4+2\log u)^2}{8\pi\,2^u}+\frac{3}{16u^3}.
$$

Write $L(u)=u\log4+2\log u$. For $u\ge5$, $L(u)>10$ and $L(u+1)-L(u)\le\log4+2/5<1.79$. Hence $L(u+1)/L(u)<1.18<\sqrt2$, so $G$ decreases. At $u=5$ one has $G(5)<0.13$. Also $0.13<(9/5)c$ and $c<1/13$. For instance $0.69<\log2<0.6932$, $1.60<\log5<1.61$ and $3.14<\pi<22/7$ give all three strict comparisons by rational arithmetic. Thus

$$
 \frac{D_j}{n^2}
 <c(1-1/u)^2+\frac{0.13}{u}
 <c<\frac1{13},
 \qquad u\ge5,
$$

where $2-1/u\ge9/5$. This covers every initial size as well as the limit. The reciprocal $2\pi/(\log2)^2=13.0776\ldots$ explains choosing thirteen. The rational replay encloses the logarithms using their positive odd-power series and $\pi$ by Machin’s formula with alternating arctangent remainders. [Schoenfeld, equation (6.3)](https://electronicsandbooks.com/edt/manual/Magazine/M/Mathematics%20of%20Computation/1960-2002/pdf/1976_v030_n134/2005976.pdf) · [Exact bounds used in this proof](../receipt-archives/check_pal_returned_horizon.py)

## Either sign alone, and the least initial buffer

Each of the following two conditions separately implies RH on paper. For every $j$ and $m\le M$, require only $13 Z_m\le n^2$. Or require only $-13 Z_m\le n^2$. RH gives both by the preceding argument. The exported Lean RH theorem uses the absolute discrepancy. The positivity step below and the finite placement theorem also have Lean proofs. [Shorter taper, both signs and prefix placement](PALRH/ReturnedTaper.lean)

For $1\le d\le m$ set $v_d=T_d+x\mathbf 1_{d\le x}-x$ and $K_d=(m+1-d)/(n-d)$. The $K_d$ are nonnegative and decreasing since $m+1<n$. Their successive differences and the last value give

$$
 \sum_{i=1}^m F_i
 =\sum_{d=1}^m(m+1-d)v_d
 =\sum_{d=1}^{m-1}(K_d-K_{d+1})Z_d+K_mZ_m .
$$

For a pencil example take $n=8$ and $m=3$. The right-hand side becomes $(2/21)Z_1+(2/15)Z_2+(1/5)Z_3$. The coefficient on $v_1$ is $7(2/21+2/15+1/5)=3$, on $v_2$ it is $6(2/15+1/5)=2$, and on $v_3$ it is $5/5=1$. No sign was lost in undoing the longer taper.

All coefficients on the right have the same sign and sum to $m/(n-1)$. For either fixed sign $\sigma\in\{1,-1\}$, the one-sided hypothesis implies $\sigma\sum_{i\le m}F_i\le mn^2/[13(n-1)]$. For $i>x$, $F_i=x(e(i)-e(x))+r_i$, with $0\le r_i\le3i$, and for $i\le x$ it vanishes. The ordinary bound $|e(i)|\le i$ therefore gives

$$
 \sigma\sum_{i\le m}e(i)\ll mx+m^2/x .
$$

The weighted upper bound divided by $x$ contributes $O(mx)$ since $n=x^2$. Summing the missing $i\le\min(m,x)$ and the term $e(x)$ costs another $O(mx)$. Choose the least $j$ with $m\le16^j$, giving $x\asymp\sqrt m(1+\log m)^2$. Hence the signed sum is at most $O(m^{3/2}(1+\log m)^2)$. The difference between this sum and $\int_1^m(\theta(t)-t)\,dt$ is $O(m)$ because $\theta$ is constant between consecutive integers and $|e(m)|\le m$. The estimate extends to real endpoints, and restoring prime powers changes the integral by $O(m^{3/2})$.

If RH fails, let $\omega=\sup_{\zeta(\rho)=0}\Re\rho>1/2$. Johnston’s Lemma 2.8 with $c=0$ gives excursions of both signs of order $y^{1+\omega-\delta}$ in the integral of $\psi(t)-t$, for any $\delta>0$. Choose $\delta<\omega-1/2$. Each sign then contradicts its own derived upper bound. This establishes both implications separately. [Johnston, Lemma 2.8](https://arxiv.org/pdf/2201.06184)

The upper sign has a physical construction attached. Start with a buffer of $B$ cells available immediately. At distance $d>x$ release another $x(n-d)$ cells. The number of jobs arrived through $m$ is $P_m$. The cumulative number of released cells is $B+x(A_m-A_{\min(m,x)})$. A single placement into cells available by the time each job arrives exists precisely when $B\ge\max_{m\le M}Z_m$. Necessity follows by counting at each cut. For sufficiency, number all jobs in order of arrival and assign job number $r$ to released-cell ordinal $r$, numbering both from zero. Each prefix inequality says its final ordinal has already been released. This constructs a common placement for all cuts. A buffer of $\lfloor n^2/13\rfloor$ on every prescribed board would suffice for RH.

At the first active board, $j=4$, the least initial buffer is 1,783,280,135,488,374 cells. The final job at distance 59,753 exactly fills all space released through that cut. It uses source start 655,300,246 and tick 281,553. Its actual destination has endpoints 655,300,246 and 655,359,999 at layer 25,599, with all coordinates counted from zero. One less cell in the initial pocket fails at precisely that cut. [Actual job and destination](../receipt-archives/2026-11-26-pal-returned-horizon.json)

## The cut that stayed put

On the three directly counted active heads the deepest deficit occurred at the same cut as on the earlier, smaller board with the same observed horizon and the same small-distance correction. A third reading, obtained by summing $\log p$ directly for all primes since 2, puts the minimum of $\theta(m)-m$ at that cut too.

| Last observed cut | Deepest cut in all three readings | Primes on either side | Widest complete prime gap in the observed range |
|---:|---:|---|---|
| 65,536 | 64,996 | 64,969 to 64,997 | 31,397 to 31,469 |
| 1,048,576 | 993,820 | 993,793 to 993,821 | 492,113 to 492,227 |
| 16,777,216 | 16,576,186 | 16,576,141 to 16,576,187 | 4,652,353 to 4,652,507 |

For the third reading, $\theta(m)-m$ decreases by one at each step between successive primes. It suffices to compare the final integer before each prime and the terminal cut. Rational enclosures separate the winner from every other terminal candidate. On the last board the gap at the deepest cut has length 46. Another gap in the same horizon has length 154. The accumulated deficit on arrival matters. Agreement of the three maximizing locations is an observation over the displayed range. [Unpadded board counts](../receipt-archives/2026-11-26-pal-local-distance.json) · [Padded counts and independently enclosed prime weights](../receipt-archives/2026-11-26-pal-returned-horizon.json)

## The range already covered

* **Exact small part on every board.** For $m\le\min(x,M)$, the corrected error is zero. Without the return, the error at $m=x$ is $xA_x$. For $x\ge2$ and $d\le x$, $2(n-d)\ge n$, so $2xA_x\ge n^2$. This exceeds the one-thirteenth allowance. Starting at $j=3$ that cut belongs to every board. Indeed $x\le M$ reduces to $u^2\le4^{u-2}$, true at $u=4$ and preserved by $(u+1)^2\le4u^2$.
* **Exact finite counts.** The runnable calculation takes both endpoints of every constant-job interval through $j=6$, ending at cut $16^6=16,777,216$. At the first active head it also decides the covering powers for the first and last surviving primes by direct integer exponentiation. At later heads rational logarithm enclosures determine the same least covering integer with successively tighter rational intervals available for a close crossing. The receipt gives each worst surplus, deficit, cut and remaining number of units. [Direct replay and ranges](../receipt-archives/2026-11-26-pal-returned-horizon.json)
* **Entire boards through $j=21$.** Johnston’s Corollary 3.3 gives the stated Schoenfeld bound for $\theta$ through $1.101\cdot10^{26}$ unconditionally, drawing on a finite zeta-zero calculation. Here $16^{21}=2^{84}<1.101\cdot10^{26}<2^{88}=16^{22}$. The proof above only uses the estimate for $x\le i\le M$. It consequently pays every cut on each of the first 22 boards. This extension uses the published finite-range theorem. Our direct job counts have the smaller range just specified. [Johnston, Corollary 3.3 and equation (3.4)](https://link.springer.com/article/10.1007/s11139-022-00616-x)
* **Further cuts on every sufficiently large board.** For $V(n)=(\log n)^{3/5}/(\log\log n)^{1/5}$, the unconditional prime error estimate gives $\sup_{x\le i\le x\exp(0.10V(n))}|e(i)|=o(x)$. Indeed $\log x=(\log n)/2$ and the negative exponential in the estimate outweighs this window’s growth. In the same range $3i=o(n)$. The returned reading is therefore $o(n^2)$ uniformly throughout these cuts, so it fits the fixed one-thirteenth budget eventually. The required upper cut is $M=n/(16u^4)$, beyond that guaranteed inner range for large $j$. [Proof with the explicit constants](how-prime-trips-change-distance.md#what-is-already-paid-on-every-sufficiently-large-board) · [Johnston and Yang, Theorem 1.4](https://arxiv.org/pdf/2204.01980)

The remaining problem has a definite failure condition. Produce one board and one cut with $13|Z_m|>n^2$, or give an independent argument paying the budget across every remaining cut. An isolated success at a larger board extends the direct range. It cannot supply the quantified statement. The finite transfer, choice of return and distortion budget were developed by Hearthline in Christopher Daniel Pang’s PAL, RPL and BLA program. [Corpus provenance](../proofs/PROVENANCE.md)
