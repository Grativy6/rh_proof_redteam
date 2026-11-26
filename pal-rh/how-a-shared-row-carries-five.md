# How a shared row carries five

Christopher Daniel Pang and Hearthline · 26 November 2026

Let $P_m=\prod_{a=0}^m\binom ma$, the number of choices of one arbitrary subset of each size from $m$ labels. Multiplying consecutive binomial identities gives $P_{m+1}(m+1)!=(m+1)^{m+1}P_m$. Cancel the same factorial in two adjacent steps to obtain the integer identity
$$
 (m-1)^{m-1}P_mP_{m-2}=m^{m-1}P_{m-1}^2 \qquad(m\ge2).
$$
In particular a consecutive change of radix $m/(m-1)$ is the $(m-1)$st root of a ratio of three real packet sizes. Multiplying these ratios for $m=2,3,4,5$ and clearing denominators gives
$$
 P_2^4 P_3 P_5^3=P_4^2\,5^{12}=2{,}250{,}000{,}000{,}000 .
$$
The exact values are $P_2=2$, $P_3=9$, $P_4=96$ and $P_5=2500$. Four size-2 packets supply four binary places. The size-3 packet supplies two ternary places. Each size-5 packet supplies two binary places and four five-way places. The combined ten binary and two ternary places encode the two size-4 packets, which have $96^2$ possible combined states. For *each* of these common states, $5^{12}$ independent settings remain. The replay carries the actual subsets and tests every common state with three different payloads. [Integer conservation and uniform division](PALRH/SharedPascal.lean) · [Decoder](../receipt-archives/check_pal_tick_layers.py)

## Finite signed rows can have an actual uniform quotient

For a possible factor $d$ in row $m$, set $B_m(d)=\lfloor m/d\rfloor(d-1-(m\bmod d))$. For any prime $p$, $v_p(P_m)=\sum_{a\ge1}B_m(p^a)$ by summing the usual factorial floors over all subset sizes. Also $B_m(d)=\sum_{r\le m/d}(2rd-m-1)$. Fix $n$ and a desired integer profile $f(d)$ on $2\le d\le n$. Define
$$
 h(k)=\sum_{r\le n/k}\mu(r)f(rk),\qquad
 U_k=\frac{k h(k)+\sum_{j=k+1}^n h(j)}{k(k-1)},\qquad
 c_k=U_k-U_{k+1}
$$
for $k\ge2$, with $U_{n+1}=0$. Then $\sum_{m=2}^n c_m B_m(d)=f(d)$ at **every original integer label**. Indeed $\sum_{m\ge k}(2k-m-1)c_m$ has the same last value and consecutive differences as $h(k)$, since $(k-1)U_k-(k+1)U_{k+1}=h(k)-h(k+1)$. Substituting into $B_m(d)$ and summing $h(rd)$ recovers $f(d)$ by Möbius inversion. The diagonal entries $B_m(m)=m-1$ give uniqueness. The excluded label 1 has $B_m(1)=0$ for every $m$.

For $f(d)=n-d$, the first negative coefficient in the integer scan is $c_{11}=-1/330$ at $n=61$. At the fourth power 81 the two negative entries are $c_{14}=-29/1365$ and $c_{15}=-29/1680$. This is the stronger requirement of matching every possible label, including composites. Let $D=\operatorname{lcm}(1,\ldots,n)$. The consecutive factors $k$ and $k-1$ are coprime, so $D$ clears all the denominators in $U_k$ and $c_k$. Prime valuations show that the positive-row product divided by the negative-row product is exactly $\prod_{p^a\le n}p^{D f(p^a)}$. For nonnegative $f$ this is an integer. Split the prime-digit registers of the positive packets into the ones needed by the negative packets and those that remain. This yields a uniform projection and specifies its remaining factors separately at each prime. Such sharing explains a negative row as a finite joint construction. Its existence alone supplies no upper estimate on the fiber’s size. [Exact profiles and divisibility checks](../receipt-archives/2026-11-26-pal-tick-layers.json)

## The competing shapes in one set of steps

Set $\ell_j=\log(j/(j-1))>0$. With $n=k^4$, let $H_j=\sum_{p\ge j,\,\sqrt n<p\le n}(n-p)$ and $T_j=(j-1)(n+1-j)$ for $2\le j\le n$. The one-direction prime count $R_n$ and Pascal count have the exact readings
$$
 \log R_n=\sum_{j=2}^n H_j\ell_j,\qquad
 \log P_n=\sum_{j=2}^n T_j\ell_j .
$$
The first formula writes $\log p$ as the sum of the steps through $p$. The second sums the adjacent-row identity twice from $P_0=P_1=1$. The unresolved comparison is the signed difference between a decreasing staircase and a parabola, measured with these same positive step sizes.

The indices where $H_j>T_j$ form one initial interval. In fact this holds for **any subset of distance labels**. The demand decreases in $j$ and is bounded by $(n-j)(n-j+1)/2$. Thus $T_j$ pays outright once $3j\ge n+2$. Up to this range the parabola increases. For instance at $n=16$ there are 28 required forward trips at the first height and only 15 matching binary steps. At the next height the available and needed counts both equal 28. All subsequent heights have nonnegative capacity margins. The comparison at all sizes still has to pay the early, more expensive steps from what remains. [Formal single-crossing proof](PALRH/SharedPascal.lean) · [Per-head counts](../receipt-archives/check_pal_tick_layers.py)
