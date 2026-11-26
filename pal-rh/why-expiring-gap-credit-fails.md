# Why expiring gap credit exceeds the budget

Christopher Daniel Pang and Hearthline · 26 November 2026

Use the returned boards $M=16^j$, $x=4^{j+1}(j+1)^2$ and $n=x^2$. The goal of the upper-only construction is to file all forward prime-trip jobs using the distance columns already released and an initial pocket of $\lfloor n^2/13\rfloor$ cells. The present obstruction concerns assigning those columns exclusively to groups that eventually discard their unused cells. [Upper-only reduction and indexing](why-one-thirteenth-is-enough.md#either-sign-alone-and-the-least-initial-buffer)

## The exact model

List the primes $x<p_1<\cdots<p_N\le M$ and set $p_0=x$. Prime $p$ releases a group of $(n-p)t_p$ jobs with $t_p=\lceil\log p/\log(1+1/x)\rceil$. Each distance $d>x$ contributes $x(n-d)$ ordinary positions. Partition the consecutive primes into blocks, with at most $r$ primes in each. If a block follows the prime at position $q$ and ends at prime $p$, it owns the distance columns $q<d\le p$. The last block may also use all columns through $M$. Positive shortages draw on the initial pocket, using distinct cells. At each boundary unused ordinary positions expire.

In the most permissive version a block may use its entire allocation immediately and may rearrange its jobs at will. Write $\Delta_G$ for its integer demand less its integer allocation. Its least pocket draw is $(\Delta_G)_+=\max(0,\Delta_G)$, so the total draw is $B(\mathcal P)=\sum_G(\Delta_G)_+$. Requiring arrival-time placement inside each block can only increase this amount.

Let $A_m=\sum_{d\le m}(n-d)$, $P_m=\sum_{x<p\le m}(n-p)t_p$ and $Z_m=P_m+xA_{\min(m,x)}-xA_m$. For every partition the signed sum of its discrepancies is exactly $Z_M$. The shared-pool minimum under the original arrival rule is $\max_{m\le M}Z_m$. These are three different accounts of the same jobs. [Finite credit identity and separated-group bound](PALRH/ExpiringCredit.lean)

## The obstruction

Write $V(M)=(\log M)^{3/5}/(\log\log M)^{1/5}$ for large $M$. Uniformly over integers $1\le r\le\exp(0.04V(M))$ and over all the indicated partitions, on all sufficiently large boards,

$$
 B(\mathcal P)\gg \frac{nxM}{r^4\log M}.
$$

The implied constant is independent of $r$, the partition and $j$. Consequently $B(\mathcal P)/n^2\to\infty$ uniformly over this range. Indeed $x=4\sqrt M(j+1)^2$ and $\exp(0.04V(M))=M^{o(1)}$. In particular an architecture with this kind of reset cannot meet the one-thirteenth budget with any fixed power of $\log M$ as its maximum group size.

**A range of prices with no integral fit.** Put $a=\lfloor\log M\rfloor-1$, $h=1/(r+1)$, and $w=1/[4r(r+1)]$. Take primes with $\log p\in[a+h-w,a+h+w]$. If $1\le s\le r$, $s h$ lies in $[h,1-h]$ and $s w\le h/4$. Thus

$$
 \operatorname{dist}(s\log p,\mathbb Z)\ge 3/[4(r+1)]
$$

simultaneously for every possible block length. The interval in $p$ lies between fixed positive multiples of $M$ and has length $\gg M/r^2$, by the mean value theorem. The unconditional estimate $|\theta(y)-y|\ll y\exp(-0.18V(y))$ gives a uniform endpoint error $O(M\exp(-0.18V(M)))$ here. One way to see uniformity is to use the increasing envelope $y\exp(-0.18V(y))$ all the way to $M$. Since $r^2\exp(-0.18V(M))\to0$, the interval contains $\gg M/(r^2\log M)$ primes. Discard the at most two blocks crossing its ends and, if necessary, the final block with its extended allocation. They contain at most $3r$ primes. The remaining good blocks number $\gg M/(r^3\log M)$. [Formal simultaneous separation](PALRH/ExpiringCredit.lean) · [Primary prime estimate, Theorem 1.4](https://arxiv.org/pdf/2204.01980)

**The cost of a good block.** Let it contain $s$ primes, let its last prime be $p$, and let $g=p-q$ be its integer width since the preceding boundary. Divide both demand and capacity by $x(n-p)$. The capacity becomes $g+g(g-1)/[2(n-p)]$. Every tick clock has $t_\ell/x=\log\ell+O((1+\log\ell)/x)$. If $g>4r\log M$, the normalized demand is at most $2r\log M$ on sufficiently large boards, since $n/(n-p)=1+o(1)$. The discrepancy already has absolute value greater than one.

If $g\le4r\log M$, the primes of the good block lie within $g$ of $p\asymp M$. Replacing their logarithms by $\log p$ costs $O(rg/M)$. Replacing their individual factors $(n-\ell)/(n-p)$ by one costs $O(rg\log M/n)$. The clock correction costs $O(r\log M/x)$. Finally $g(g-1)/[2(n-p)]=O(g^2/n)$. All four errors are $o(1/r)$ uniformly because $r=M^{o(1)}$ and $x\ge\sqrt M$. The normalized discrepancy is therefore $s\log p-g+o(1/r)$. Its absolute value is $\gg1/r$ by the separation just proved. Since $n-p\sim n$, summing actual absolute discrepancies over the good blocks gives

$$
 \sum_G|\Delta_G|\gg nxM/(r^4\log M).
$$

**Why a positive part must be paid.** The net discrepancy $\sum_G\Delta_G=Z_M$ is much smaller. The unweighted returned prefix vanishes through $x$. Thereafter it is $x(e(i)-e(x))+r_i$ with $e(y)=\theta(y)-y$ and $0\le r_i\le3i$. The positive taper of total weight $n$ gives

$$
 |Z_M|\ll n[xM\exp(-0.18V(M))+M].
$$

The ratio of this upper bound to $nxM/(r^4\log M)$ tends to zero, since $4\cdot0.04<0.18$ and $r^4\log M/x\to0$. Thus $2B(\mathcal P)=\sum_G|\Delta_G|+Z_M$ gives the claimed lower bound, including its sign. The argument uses unconditional estimates throughout. It leaves open the budget when spare cells remain available across arbitrary boundaries.

## Choosing the best finite partition

Write $z_i=Z_{p_i}$, $z_0=0$. For a nonterminal permissive block after arrival $a$ through arrival $b$, the cost is $(z_b-z_a)_+$. For the terminal block replace $z_b$ with $Z_M$. For a causal block, which can only use cells released by the current arrival, the cost is $\max(0,\max_{a<i\le b}(z_i-z_a))$. A surplus of jobs can attain its maximum only immediately after an arrival. The last-block extension supplies no earlier cells in this model.

For either cost $c(a,b)$, the optimum through arrival $b$ is the minimum of $D(a)+c(a,b)$ for $\max(0,b-r)\le a<b$, starting with $D(0)=0$. For a fixed full board use the extended endpoint only at $b=N$. Removing the last block of a partition proves necessity of the recurrence, and appending that block to an optimum at $a$ attains it. Increasing $r$ only adds allowable partitions. Bisection therefore finds the smallest working cap, and following the recorded minimizing boundaries reconstructs an actual attaining partition. The replay independently enumerates every partition in 1,296 small signed test cases and recalculates all charges of its displayed optimizing partitions. [Executable replay](../receipt-archives/check_pal_expiring_gap_credit.py)

| Index and rule | Pocket available | Best cost one prime below transition | Best cost at transition | First working cap |
|---|---:|---:|---:|---:|
| 4, all block cells available immediately | 33,038,209,969,230,769 | 36,239,477,724,788,563 | 32,349,708,793,138,512 | 8 |
| 4, causal arrivals | 33,038,209,969,230,769 | 33,323,222,525,576,988 | 32,446,162,866,430,334 | 21 |
| 5, all block cells available immediately | 36,366,913,421,757,322,161 | 36,382,895,093,012,340,418 | 35,885,281,995,698,977,799 | 64 |
| 5, causal arrivals | 36,366,913,421,757,322,161 | 36,511,595,570,564,990,650 | 36,336,052,223,307,187,143 | 246 |

For a separate address control, insist that a non-pocket destination has positive distance divisible by its prime and was available at the prime’s own arrival. Only distance $p$ itself qualifies. It has $x(n-p)$ ordinary positions. The pocket must then absorb at least $\sum (n-p)(t_p-x)_+$ over the arrivals. At $j=4$ this exceeds the entire allowed pocket by prime 27,791, the 215th retained arrival. This is another real failure of a proposed placement on a board that the shared-pool construction actually funds. [All source counts and fixed cases](../receipt-archives/2026-11-26-pal-expiring-gaps.json)

Pang’s question about carrying a distinction into the next frame suggested the expiring allocations. BLA supplied the common units for comparing two accounts and RPL supplied the requirement to track what is discarded at each boundary. Hearthline derived the simultaneous phase separation, the price of resets and the finite optimizers in Pang’s independent program. [Corpus roles](../proofs/PROVENANCE.md)
