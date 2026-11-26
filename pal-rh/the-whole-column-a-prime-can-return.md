# The whole column a prime can return

Christopher Daniel Pang and Hearthline · 26 November 2026

Let $x\ge1$ be a whole column’s height, and $t_d\ge0$ the number of ticks per starting site at distance $d$. A distance has $n-d$ forward starts. On the prime boards the only nonzero $t_d$ are at retained primes, with their actual clock lengths. The following allocation works for any nonnegative integer tick stream.

Set $S_m=\sum_{d\le m}t_d$, $C_m=\lceil S_m/x\rceil$, and $c_d=C_d-C_{d-1}$. Open $c_d$ whole columns at each start still present at distance $d$. All earlier eligible columns remain available in that row. Since $\lceil(a+b)/x\rceil\le\lceil a/x\rceil+\lceil b/x\rceil$, each $c_d$ is either the same as the independently rounded-up charge or one column smaller.

## An address that survives the next prime

At start $i<n-d$, give tick $t<t_d$ the row ordinal $S_{d-1}+t$. Division by $x$ gives its column number and lane. The ordinal is below $xC_d$, so the column already exists. If its issuing distance was $q\le d$, then $i<n-q$, so this very row was live when that column opened. To decode, recover the ordinal from its column and lane and find the first cumulative tick count strictly exceeding it. That distance and the difference from its preceding count give the original tick. A proposed record beyond the row’s last admissible distance is an empty lane. The running count modulo $x$ and its quotient update the allocation. The source sequence supplies the inverse through its cumulative endpoints. [Integer division and weighted capacity proof](PALRH/SharedColumns.lean) · [Physical codec](../receipt-archives/pal_tick_columns.py)

Through any $m\le n$, a rule covering each row on arrival must have opened at least $C_m$ cumulative columns on a still-live row. The difference $r_m=xC_m-S_m$ is in $\{0,\ldots,x-1\}$. Finite summation by parts gives the exact cost
$$
 x\sum_{d\le m}(n-d)c_d-\sum_{d\le m}(n-d)t_d
 =(n-m)r_m+\sum_{k=0}^{m-1}r_k\ \le\ n(x-1).
$$

The first term is held by the $n-m$ live starts. Each summand in the second term is the residual in one retired starting row. Equivalently, sum $r_{\min(m,n-1-i)}$ for $0\le i<n$. The weights in this expression are nonnegative. Opening the least possible number of columns at each prefix therefore also minimizes their weighted cost among the rowwise rules that cover that common tick stream.

At $n=16$, $x=4$, the four positive distances have clock lengths $8,9,11,12$. Their cumulative ticks are $8,17,28,40$, giving cumulative columns $2,5,7,10$. Distance 11 opens two columns and uses a lane left at distance 7. For example its first tick at row 1 goes to row 1, local column 2 of owner 7, lane 1, all numbered from zero. The 260 original records occupy 272 allocated lanes, compared with 292 under independent per-prime rounding. Starts 5, 6, 7 and 8 each end with three unused lanes. The replay sends every one of the 260 individual records through both directions of the decoder. [Integer witnesses, including all retired rows](../receipt-archives/2026-11-26-pal-carry-storage.json)

## How many actual primes relinquish a column?

On the prescribed boards $M=16^j$, $x=4^{j+1}(j+1)^2$ and $n=x^2$. Let $N=\pi(M)-\pi(x)$ for the active heads. Let $W_j$ be the number of primes $p\in(x,M]$ for which $c_p<\lceil t_p/x\rceil$. The following asymptotic is unconditional, with natural logarithms:
$$
 \frac{W_j}{N}=H(\{\log M\})+o(1),\qquad
 H(v)=2-v-\frac{e^{-v}}{1-e^{-1}}\quad(0\le v\le1).
$$
The endpoints agree. The weighted number of physical lanes released by sharing equals $nxN(H(\{\log M\})+o(1))$, because each such prime releases $x(n-p)$ lanes and $M/n\to0$.

Indeed $t_p/x=\log p+O((1+\log M)/x)$ uniformly. Telescoping the shared counts gives
$$
 W_j=\sum_{x<p\le M}(\lceil t_p/x\rceil-t_p/x)+O(1).
$$
By the ordinary prime number theorem, $p/M$ under uniform counting of these primes tends in distribution to uniform length on $[0,1]$, since $x=o(M/\log M)$. Take a subsequence along which $\{\log M\}\to v$ on the circle. First restrict $p/M$ to $[\eta,1]$. The sawtooth $\lceil t\rceil-t$ is bounded and continuous there after removing neighborhoods of finitely many points where $v+\log(p/M)$ is integral. The neighborhoods have arbitrarily small limiting mass. The price perturbation tending to zero may therefore be removed, and finally $\eta$ sent to zero. This gives
$$
 H(v)=\int_0^1(\lceil v+\log u\rceil-v-\log u)\,du .
$$
If $Y=-\log u$, then $\Pr(Y\ge y)=e^{-y}$ for $y\ge0$. The mean of $\lceil v-Y\rceil$ is $1-\sum_{k\ge0}e^{-v-k}$, and the mean of $Y$ is 1. This yields the displayed formula, including its endpoint values by continuity. The argument on every convergent subsequence gives the asserted $o(1)$ along the whole family.

The minimum is $2-1/(1-e^{-1})=0.41802\ldots$, and the maximum is $1+\log(1-e^{-1})=0.54132\ldots$. Both are limiting values along the actual boards. To see why the phase visits the whole circle, $\log16$ is irrational. If $\log16=A/B$ for positive integers $A,B$ then $e^A$ would be the integer $16^B$. For $f(t)=t^k(A-t)^k/k!$ all derivatives at 0 and $A$ are integers. Repeated integration by parts would make $\int_0^A e^t f(t)\,dt$ a strictly positive integer. Its upper bound $Ae^A(A^2/4)^k/k!$ tends to zero. The orbit $j\log16\bmod1$ is consequently dense by the irrational rotation theorem.

Independent rounding in these units creates an excess much larger than the entire $n^2/13$ pocket on all sufficiently late boards, even at the terminal cut. In fact the original signed terminal error is $o(nxN)$ by the unconditional prime error bound and the returned-prefix calculation. The extra $nxN H$ has a strictly positive limiting lower coefficient and $nxN/n^2=N/x\to\infty$. Sharing the partial column reduces this particular overhead on every prefix to at most $n(x-1)$. Its fraction of one layer tends to zero. This discharges the rounding cost. The cumulative deviation of the prime weights from the ordinary release schedule still needs control. [Original signed-error estimate](why-expiring-gap-credit-fails.md#the-obstruction) · [Physical crossing costs](how-much-credit-crosses-a-prime-cut.md)
