# How much can travel with a prime?

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). Pang’s question about an integer carrying its own frame suggests keeping its small factors attached while the measuring head moves. This proof uses the two ordinary signs of the Möbius function, the five prices from the [six-label calculation](../proofs/which-prime-labels-cancel.md), and a prime number theorem in short intervals. The arithmetic input and the remaining sign condition are stated below.

## A fixed allocation at every sufficiently large scale

Write the physical first-pass coefficient as $a(v^2d)=v\mu(d)$ for $v=2^i3^j$, $(d,6)=1$, and set it to zero elsewhere. Partition the positive axis into blocks $(Y,Y+L]=(m^4,(m+1)^4]$. Thus $L\asymp Y^{3/4}$. Fix any $0\le\gamma<11/26$ and the set $\mathcal R$ of 67 primes from 5 through 347. For each subset $S\subseteq\mathcal R$ put $r_S=\prod_{r\in S}r$, including $r_\varnothing=1$.

**Theorem.** In every sufficiently large block one can allocate fractions of actual signed marks at
$$
 n=c\,r_S q,\qquad c=v^2u\le Y^\gamma,\qquad
 u\text{ squarefree},\quad (u,6\textstyle\prod_{r\in\mathcal R}r)=1,\quad q>347\text{ prime}.
$$
The selected fractions lie in $[0,1]$. They use every label with $S=\varnothing$ and every label with odd $|S|$. Within each fixed cofactor $c$ the remaining labels in this family have even $|S|\ge2$ and the single sign $-\mu(u)$. On every block the allocated signed marks $w(n)$ annihilate $1/n,1,n,n^2,n^3$ exactly. Once chosen, $w$ is fixed at every head. For the ordinary PAL point price,
$$
 \sum_{n\ge1} w(n)G(T,n)=o(\sqrt T)\qquad(T\to\infty).
 \tag{1}
$$
The sum is finite for each real $T$. The first-pass difference with $G(T,2n)$ has the same bound.

### Why the same integer cannot be spent twice

Unique factorization recovers $v$ from the valuations at 2 and 3 and recovers $S$ from divisibility by the 67 chosen primes. Since $\mathcal R$ is fixed, $q\gg_{\mathcal R}Y^{1-\gamma}$ while $u\le Y^\gamma$. For sufficiently large $Y$ the largest prime factor is $q$ and exceeds every factor of $u$. Dividing recovers $u$. The sign of $a(n)$ is $(-1)^{|S|+1}\mu(u)$, with magnitude $v$. Distinct cofactors, tags and blocks consequently spend disjoint physical capacity.

### Why enough actual primes occur in each bin

For a fixed fractional interval of the block and a fixed tag, count primes $q$ around $x=Y/(cr_S)$ in an interval of length comparable to $L/(cr_S)$. The ratio of log length to log position is at least
$$
 \frac{3/4-\gamma}{1-\gamma}+o(1)>\frac{17}{30}
$$
uniformly over eligible $c$ and all tags. The interval length also lies below $x^{0.99}$ eventually. Corollary 1.3 of Guth and Maynard gives the prime count asymptotic in this every-interval range. The strict exponent margin absorbs fixed tag products and each fixed fractional subdivision. The older $7/12$ theorem of Huxley, in Heath-Brown’s proof, already covers every $\gamma<2/5$. In that version prime powers with exponent at least two have total von Mangoldt weight $O(\sqrt x\log^2x)$ and can be removed. Fixed-power intervals tile longer intervals with an end piece of negligible relative length when there is power slack. [Guth and Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552) · [Heath-Brown, opening theorem](https://doi.org/10.4153/CJM-1982-095-9)

Divide each tag count by $L/(c\log(Y/c))$. On the normalized coordinate $t=(n-Y)/L$, its counting measure tends to $dt/r_S$. Convergence for fixed interval endpoints is uniform in $c$, since $x$ tends uniformly to infinity and $\log(Y/(cr_S))/\log(Y/c)\to1$ uniformly. A fixed fine subdivision and positivity give convergence for continuous weights and for their restrictions to the five bins. They also give uniform convergence of cumulative counts on $0\le t\le1$ by squeezing between adjacent subdivision endpoints. The factor $Y/n$ tends uniformly to 1.

Work in the five functions $f_i(n)=(Y/n){4\choose i}t^i(1-t)^{4-i}$ for $0\le i\le4$. Let $H_{ij}$ be the integral of the $i$th Bernstein polynomial over the $j$th fifth of the unit interval. The matrix $H$ is invertible. A left null vector would give a polynomial of degree at most four with integral zero on all five intervals. A nonzero such polynomial must change sign in the interior of each interval and would have at least five distinct roots. The Bernstein polynomials are a basis, so the null vector is zero.

### Cover the marks and retain the surplus

All matrix columns below are sums of the five actual functions. Allocate the same fraction to each member of a named bin. The cofactor’s common sign and magnitude can be restored after solving.

1. Cover every empty tag using the singleton tags. After division by the count scale the offered matrix tends to $sH$, where $s=\sum_{r\in\mathcal R}1/r>1.2012$. The target tends to $H\mathbf1$. The unique five fractions thus tend uniformly to $1/s$, strictly inside $(0,1)$.
2. Cover all unused odd tags using the even tags of size at least two. Write $O=\sum_{|S|\ \mathrm{odd}}1/r_S$ and $F=\sum_{|S|\ \mathrm{even}}1/r_S$. The target equals the full odd column less the entire empty-tag column, by step 1. The new matrix tends to $(F-1)H$ and this target tends to $(O-1)H\mathbf1$. Since $O\ge s>1$ and
   $$
   F-O=\prod_{r\in\mathcal R}(1-1/r)>0,
   $$
   the limiting fraction $(O-1)/(F-1)$ also lies strictly inside $(0,1)$.

Continuity of the inverse and the strict margins give admissible rational fractions for every eligible cofactor in every sufficiently large block. Taking the finite sum of marks assigned in the two steps gives five exact zero moments there. Set $w=0$ in the finitely many earlier blocks. The unspent signed mass in the orientation of the even tags, divided by $vL/(c\log(Y/c))$, tends to $F-O$. For this set of primes the product lies between $0.28609190$ and $0.28609191$. It gives a specific residue that this allocation has to carry. The finite trillion-scale experiment spends only tags of size at most two and uses its own explicitly given interval. [Finite populations and palette arithmetic](../receipt-archives/2026-11-25-pal-prime-transport.json)

### What happens when the head cuts a block

For real $T>0$, extend the remainder by $r=T-n\lfloor T/n\rfloor$. It satisfies
$$
 G(T,n)=\frac{(T-n)_+}{2n}-\sum_{k\ge1}h(kn/T),\qquad
 h(t)=(1-t)_+^2(1+2t).
$$
The same finite polynomial identity as for integer $T$ proves this formula. On each side of a cutoff $n=T/k$, the summand is a polynomial in $n$ of degree at most three. The linear ramp divided by $n$ also lies in the five-dimensional space on either side of $n=T$. A whole block on one side contributes exactly zero to that term. [Remainder identity](what-a-reflected-remainder-carries.md)

For any block near $Y$ its total available absolute weight is bounded by
$$
 \sum_{v=2^i3^j\le\sqrt{Y+L}}v(L/v^2+1)
 \ll L+\sqrt Y\log(2Y)\ll L.
$$
Here $\sum 1/v=3$, and summing the powers of 3 for each of $O(\log Y)$ powers of 2 gives the second term. On the initial segment $\sum_{n\le D}|a(n)|\le3D$ by the same divisor count without a rounding term.

Choose the block boundary $D=\lfloor T^{1/5}\rfloor^4\asymp T^{4/5}$. For $n\le D$ use $|G(T,n)|\le(n/T)^2$ from the remainder formula. The total cost is $O(D^3/T^2)=O(T^{2/5})$. For $n>D$ only the terms whose cutoff is inside a block can contribute. In a block crossing $y=T/k$ one has $h(n/y)\ll(L/y)^2$, since it vanishes to order two at the cutoff. The charge per cutoff is $O(L^3/y^2)=O(y^{1/4})$. Summing gives
$$
 \sum_{k\le T/D}O((T/k)^{1/4})=O(T/D^{3/4})=O(T^{2/5}).
$$
A boundary at a block endpoint incurs zero additional charge. The single ramp crossing at $y=T$ costs $O(L^2/T)=O(\sqrt T)$. This already places the entire allocation within the fourth-power allowance.

For the strict little-$o$ in (1), the normalized signed cumulative sums of the funded marks in each cofactor group tend uniformly to zero. Indeed each tag’s cumulative measure has the uniform limit just proved, the five fractions in each step tend to a common constant, and the limiting signed density of each funded step is zero. The error per cofactor in a partial block is therefore $o(vL/(c\log(Y/c)))$, uniformly in the cofactor and the partial endpoint. Summation preserves $o(L)$ because
$$
 \sum_{c=v^2u\le Y^\gamma}\frac{v}{c\log(Y/c)}
 \ \ll_\gamma\ \frac{1}{\log Y}
 \sum_{v=2^i3^j}\frac1v\sum_{u\le Y^\gamma}\frac1u=O_\gamma(1).
$$
Partial summation at the ramp crossing multiplies this $o(L)$ by its $O(L/T)$ total variation and endpoint size. This improves the crossing cost to $o(\sqrt T)$ and proves (1). Homogeneity gives $G(T,2n)=G(T/2,n)$, which handles the second head with the identical stream of weights.

## The sign still needed for RH

Let $w$ be the allocation just proved. The exact first-pass identity at side $X$ is
$$
 \tfrac X2 S(X)=P_h(X)+\sum_n a(n)[G(2X,n)-G(X,n)] .
$$
At $X=j^4$, removing $w$ introduces an $o(j^2)$ error. It now suffices to show that at every sufficiently late fourth power
$$
 P_h(X)+\sum_n(a(n)-w(n))[G(2X,n)-G(X,n)]\ge0 .
$$
The existing fourth-power argument allows a fixed multiple of $j^2$ of negative error in the original identity. The Lean module proves the transfer from an affordable stream and this remaining sign test to stock Mathlib RH. The moving-head allocation and short-interval argument above are paper results. The sign across the surviving cofactors and the integers outside the displayed factorization is open in this construction. [Source of the actual charge](PALRH/ReflectedCarry.lean) · [Transfer to the fixed RH statement](PALRH/PrimeTransport.lean)
