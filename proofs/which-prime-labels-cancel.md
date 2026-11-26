# Which prime labels cancel?

**At a side of one trillion we can identify a group of actual integers whose signed contribution to the PAL measurement is exactly zero.** It includes every prime in the interval, every product of one prime between 5 and 347 and one prime above 347, and specified fractions of products of three primes. It accounts for between **10.59% and 10.62%** of the entire absolute first-pass cost in that interval. The fractions keep working when the measuring head moves within its cell.

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). Pang asked what has to travel with a prime through a change of frame and why a central reflection could ever force a location. His PAL, APCI and BLA questions led us to keep the actual integer labels and change the measurement after choosing the weights. The [mirror experiment](what-the-central-mirror-earns.md) changes the rule at 5. Here the ordinary primes and their Möbius signs are fixed throughout.

## Six integers you can do by hand

| Label $d$ | Factorization | Signed amount, in units of $1/1190$ |
| ---: | --- | ---: |
| 83 | prime | −83 |
| 95 | $5\cdot19$ | +475 |
| 107 | prime | −1070 |
| 119 | $7\cdot17$ | +1190 |
| 131 | prime | −655 |
| 143 | $11\cdot13$ | +143 |

Each amount spends at most one available mark. Both columns of signs have total magnitude $1808/1190$. Now divide each signed numerator by its **own label**. What remains, in order, is
$$
 -1,\quad 5,\quad -10,\quad 10,\quad -5,\quad 1.
$$
Those six integers take the fifth difference. The labels are twelve apart. The fifth difference of a polynomial of degree at most four vanishes because each difference lowers its degree by one. It follows that the signed marks in the table cancel against **every price of the form**
$$
 g(d)=a/d+b+cd+ed^2+fd^3. \tag{1}
$$
Multiply the price by $d$ and you can see the quartic yourself. The six labels stay where they are. All five coefficients in the price may change afterward.

This is the price the PAL construction actually uses. Write $T$ for the measuring head, $k=\lfloor T/d\rfloor$, $r=T-kd$, $u=r(d-r)$. Its point reading and window potential on an active cell $d\le T$ are
$$
 G(T,d)=\frac{T u(d-2r)-u^2}{2dT^3},\qquad E(T,d)=\frac{u^2}{4dT^2}.
$$
At fixed $T,k$, both numerators are polynomials in $d$ of degree at most four. For the six labels, every real $T$ between 143 and 165 gives $k=1$ for all six. The same payment works at each such head for both readings. [Definitions and derivation of the readings](../pal-rh/what-a-reflected-remainder-carries.md) · [Five differences and both actual prices in Lean](../pal-rh/PALRH/PrimeTransport.lean)

## The sector at one trillion

Take $X=10^{12}$, $T=2X$, $A=1{,}600{,}000{,}000{,}000$, $B=1{,}666{,}666{,}666{,}666$. Use $A<d\le B$. Every label has $k=1$ at $T$ and is inactive at $T/2$. The signed cost per unit is
$$
 G(T,d)=\frac{T}{2d}-\frac32+\frac{3d^2}{T^2}-\frac{2d^3}{T^3}.
$$
This price is positive and increasing on the sector. With $z=d/T$, its second derivative in $z$ is $z^{-3}+6-12z$, which is decreasing and negative at $4/5$. The first derivative at the right endpoint $5/6$ is $17/150>0$. The [preceding sector calculation](../pal-rh/what-a-reflected-remainder-carries.md) bounded the entire signed first-pass reading here between −45,627 and −45,417.

Let $q>347$ be prime and let $r,s$ be distinct primes from 5 through 347 with $r<s$ when used together. Unique factorization gives three disjoint sets of physical labels.

| Set | Sign | Actual labels | Amount spent |
| --- | :---: | ---: | --- |
| $q$ | − | 2,370,643,751 | All |
| $rq$ | + | 3,223,386,005 | All across the two steps |
| $rsq$ | − | 2,104,921,452 | Between 28.66% and 52.36% of each, according to its bin |

Split the sector into five equal intervals in $t=(d-A)/(B-A)$. For each bin sum the five functions
$$
 f_i(d)=\frac A d {4\choose i}t^i(1-t)^{4-i},\qquad 0\le i\le4 .
$$
They form a basis of (1). Write $b$ for the column of five sums over all primes, $M$ for the matrix whose columns sum over the five $rq$ bins, and $N$ for the corresponding $rsq$ matrix. Both systems below use the actual integer locations.

1. Solve $Mw=b$. Each of the five rational fractions is strictly between $0.6785$ and $0.7924$. Spending $w_j$ of each positive mark in bin $j$ covers all prime marks.
2. The positive marks left over have total column $M\mathbf1-b$. Solve $Nv=M\mathbf1-b$. All five fractions lie strictly between $0.2866$ and $0.5236$. Spending $v_j$ of each available negative three-prime mark now covers every remaining positive mark from the first step.

These fractions prove the existence of a particular accounting. Individual primes can be accounted for collectively in more than one way. The two equations hold for the entire space (1). For every $B\le T'\le2A$, the same accounting therefore cancels both $G(T',d)$ and $E(T',d)$ exactly. Crossing a quotient boundary changes the price formula. The [all-scale argument](../pal-rh/how-much-can-travel-with-a-prime.md) prices those crossings.

## How much of the arithmetic does this explain?

| Measurement at $T=2X$ | Outward bounds |
| --- | ---: |
| Magnitude of all prime labels covered | 56,048,901 to 56,054,741 |
| Additional positive cost covered at the second step | 20,155,202 to 20,168,981 |
| Total magnitude removed, counting both signs | 152,419,886 to 152,435,766 |
| Total magnitude of the entire first-pass sector | 1,435,922,440 to 1,438,917,024 |
| Share of the sector cost removed | 10.59% to 10.62% |
| Share within the unsmoothed rough labels alone | 31.77% to 31.85% |

The combined magnitude removed is twice the original whole positive $rq$ column, since both steps cancel exactly and that column is spent once. The signed reading of the complement consequently still lies between −45,627 and −45,417. We have isolated a part of the large cancellation and measured how much arithmetic is still outside it.

## How to reproduce the bounds

The public count table gives the three exact populations on each of 2,000 subintervals. A segmented sieve counts the primes $q$ after dividing each endpoint by its specified small-factor product. Every complete factor row also agrees with the difference of two endpoint prime-counting values. An elementary sieve and direct small-factor stripping independently reproduce all three populations on each of 100 calibration intervals near 1.6 million. [Integer counts](../receipt-archives/prime-transport-trillion-counts.csv) · [Counting program](../receipt-archives/prime_transport_counts.cpp) · [primesieve](https://github.com/kimwalisch/primesieve) · [primecount](https://github.com/kimwalisch/primecount)

On each subinterval the Bernstein polynomial has its minimum at an endpoint and its maximum either at an endpoint or at $t=i/4$. Enclose $A/d$ using its two endpoint values, multiply by the count, and round outward. For either system call the matrix midpoint $H$, its entrywise radius $D$, the right-hand midpoint $b_0$, and its radius $e$. Compute $R=H^{-1}$ exactly and $x_0=Rb_0$. Put $\nu=\|\,|R|D\,\|_\infty$. Both values of $\nu$ are below $0.038$. For the true system $(H+\Delta)x=b_0+\delta$, the inverse of $I+R\Delta$ has norm at most $1/(1-\nu)$ by the geometric series. Thus
$$
 \|x-x_0\|_\infty\le
 \frac{\|\,|R|(e+D|x_0|)\,\|_\infty}{1-\nu}.
$$
This encloses the solution for the actual prime locations between mesh endpoints. Gaussian elimination, bin bounds and the final strict capacity inequalities all use rational arithmetic. No floating approximation enters the bounds. [Standard-library replay](../receipt-archives/check_pal_prime_transport.py) · [Complete results](../receipt-archives/2026-11-25-pal-prime-transport.json)

For the full denominator of the percentage, write $a(v^2d)=v\mu(d)$ for $v=2^i3^j$, $(d,6)=1$, and zero elsewhere. Let $g(y)=y-\lfloor y/2\rfloor-\lfloor y/3\rfloor+\lfloor y/6\rfloor$ for integer $y$. Expanding the squarefree indicator as $\sum_{\ell^2\mid d}\mu(\ell)$ gives
$$
 \sum_{n\le x}|a(n)|=\sum_{m\le\sqrt x}h(m)\,g(\lfloor x/m^2\rfloor),
 \qquad h(v\ell)=v\mu(\ell),\quad(\ell,6)=1 .
$$
For the rough-only total keep $v=1$. Taking differences counts exactly **60,792,389,809 weighted marks** in the full sector and **20,264,236,980** in the rough-only sector. The replay bounds the increasing price by its endpoints on 100 subintervals and checks the square-divisor formula against direct factorization at small integers.

## What remains

The finite calculation completely funds the specified one- and two-prime groups in this interval. The all-scale result extends that operation to a prime carrying a growing cofactor and identifies a signed remainder with a fixed parity in its small prime factors. The sign across the other cofactors and labels with several large factors remains the outstanding RH estimate. [Proof for moving heads](../pal-rh/how-much-can-travel-with-a-prime.md)
