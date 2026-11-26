# The factorial frame for prime distances

Christopher Daniel Pang and Hearthline · 26 November 2026

Write $B_n=n^{n^2}$, $e_p=2(n-p)$, and $N(n,c)=(n!)^n\prod_{c<p\le n}p^{e_p}$ where the product runs over primes. Write $G(n)=\log(B_n/N(n,0))$. Logs in this note are natural unless a bit is named. [Board and original reduction](the-prime-board-and-its-signed-area.md)

## One integer specifies the surviving distances

Let $c=\lfloor\sqrt n\rfloor$. The full demand divided by $N(n,c)$ is at most $(\prod_{p\le c}p)^{2n}\le 4^{2nc}$. The elementary primorial bound follows by grouping successive primes in binomial coefficients. The discarded labels therefore require at most $4nc$ bits. A one-sided fit for $N(k^4,k^2)$ gives the original prime-area estimate with an extra $O(k^6)$ term. Fourth-power interpolation and the alternating-divisor argument then give RH. RH conversely funds the original records at every size. The independently fixed Lean implication takes the two integer inequalities
$$
N(k^4,k^2)\le B_{k^4}\le N(k^4,k^2)2^{8k^4(k^2+1)} .
$$
The second inequality bounds the unused capacity. Both follow under RH from the earlier full-board allowance and the cost of the deleted digits. [Prime-band Lean reduction](PALRH/PrimeBand.lean) · [Fourth-power interpolation](fourth-power-boards-and-their-funded-intervals.md)

For $2\le m\le n$ we have $\gcd(m,c!)=1$ exactly when $m$ is prime and $m>c$. A composite $m$ has a least prime factor at most $\sqrt m$. Each prime through $c$ divides $c!$, and a larger prime cannot divide it. Thus the very same $N(n,c)$ can be written as an integer product with a gcd test on every distance from 2 to $n$. The fixed RH hypothesis for this version uses factorial, exponentiation, gcd, products, inequalities and a natural-number quantifier. [Independently stated challenge](checks/sieve-frame/SieveChallenge.lean)

The smallest positive frame that selects precisely these labels by coprimality is the primorial $R=\prod_{p\le c}p$. To see necessity, omit any $p\le c$ from the factors of a proposed frame. The composite $p^2\le n$ then passes the gcd test. Every exact frame must be divisible by each of the distinct primes through $c$, hence by $R$. The primorial itself suffices. Higher powers of those primes leave all the gcd-one answers unchanged. Conversely a positive integer $m\le n$ has at most one prime divisor larger than $c$, and that divisor occurs to the first power. The product of two such divisors or the square of one would exceed $n$. [Least-factor test and square witness](PALRH/SieveFrame.lean)

## The price of one missing factor

Fix a prime $q$. For $n\ge q^2$, compare $R$ with $R/q$. Unique factorization enumerates all the additional admissible labels. They are $q^j$ and $q^j p$, with $j\ge1$, $p>\sqrt n$ prime, and the label at most $n$. Each has one representation in its indicated class. The excess in the logarithm of the demand is
$$
C_q(n)=2\sum_{m\ {\rm added}}(n-m)\log m,\qquad
\lim_{n\to\infty}\frac{C_q(n)}{n^2}=\frac1{q-1}.
$$

The pure powers cost $O_q(n\log^2 n)$. For a fixed $a=q^j$, the part from $m=ap$ is twice $\sum_{\sqrt n<p\le n/a}(n-ap)\log(ap)$. Retaining $\log p$ gives $2aI_\theta(n/a)$ up to $O(n^{3/2})$, where $I_\theta(y)=\sum_{p\le y}(y-p)\log p\sim y^2/2$ by the prime number theorem. The constant weight $\log a$ contributes $O_a(n^2/\log n)$. Thus this group contributes asymptotically $n^2/a$. For a bound uniform in $j$, $\log(ap)\le2\log p$ whenever $p>\sqrt n$ and $ap\le n$. Its whole group is at most $4n\theta(n/a)\ll n^2/a$. Summation of the geometric majorant allows the limit through the sum and gives $1/(q-1)$.

The correctly framed log surplus is $o(n^2)$ by the prime number theorem, the exact board-area identity, and the primorial cost above. The modified frame has logarithmic **deficit** asymptotic to $n^2/(q-1)$. This is an unconditional impossibility of injectively encoding the entire modified input at all sufficiently late sizes. At the particular fourth power $4^4$, all numerical statements can be decided by ordinary finite integer multiplication. [Complete small range, independent products and examples](../receipt-archives/check_pal_sieve_frame.py)

## Funding the upper distances at every size

First consider $p>\lceil n/2\rceil$. Each such prime divides $\binom{n}{\lfloor n/2\rfloor}$ because it divides $n!$ and neither denominator factorial. Their product divides this binomial coefficient, which is at most $2^n$. Each $e_p\le n$. Their dials therefore have at most $(2^n)^n$ settings.

For $n\ge10$, $2\cdot2^n n!\le n^n$. Check $n=10$. For the induction step use $(n+1)^n\ge2n^n$. Words of length $n$ on an alphabet of $n+1$ symbols include $n^n$ words with zero copies of the extra symbol, and $n\cdot n^{n-1}=n^n$ with precisely one. Multiplying the induction hypothesis by $2(n+1)$ and using this bound proves the step. Raising the factorial inequality to the $n$th power leaves at least $n$ spare bits after all upper-distance dials and all row orders fit. The smaller sizes are finite direct counts. The two-cell scheme costs at most half a natural log unit per row, so these spare bits also fund the explicit decoder for $n\ge10$. [All-size integer theorem](PALRH/UpperHalfBoard.lean) · [Two-cell decoder](../receipt-archives/check_pal_prime_board.py)

For a sharper bound write $b=\lfloor\log_2 n\rfloor+1$ and $y=\lceil3n/b^3\rceil$. **All row permutations and all dials $p>y$ fit reversibly in the paired scheme at every positive size.** Through $n_0=10^9$ the full board is already covered. A smaller set of dials can also use the full encoder by setting the others to zero. Above $n_0$ the proof below pays the rounding for the reduced layout directly. [Full finite range and interpolation](fourth-power-boards-and-their-funded-intervals.md#one-billion-consecutive-sizes-from-a-finite-sieve)

Set $P(x)=x^2-2I_\theta(x)$ and $H_n=\log(n!)-n\log n+n$. Then $G(n)=P(n)-nH_n$ and $1\le H_n\le1+\log n$. Since $P(n_0)>0$, Dusart’s unconditional Theorem 5.2 with $(k,\eta)=(3,0.78)$ gives
$$
-P(n)\le1.56\int_{n_0}^{n}\frac{t}{\log^3 t}\,dt
\le 0.85\,\frac{n^2}{\log^3 n}.
$$
Indeed the derivative of $t^2/\log^3t$ is at least $1.85t/\log^3t$ for $t\ge n_0$. Also $n(2+\log n)<0.001n^2/\log^3 n$ in this range by differentiation and its value at $n_0$. [Dusart, Theorem 5.2 and thresholds](https://arxiv.org/pdf/1002.0442)

For integer $t\ge90{,}000$, $\theta(t)>0.6t$ follows already from elementary central-binomial estimates. Put $a=\lfloor t/2\rfloor$. The valuation of $\binom{2a}{a}$ at each prime is at most the number of its powers up to $2a$, by subtracting the factorial floors. Thus $\psi(t)\ge(2a)\log2-\log(2a+1)\ge(t-1)\log2-\log(t+1)$. Summing $\theta(t^{1/k})$ for $k\ge2$ and using $\theta(u)\le u\log4$ gives $\psi(t)-\theta(t)\le2\sqrt t\log t$. At 90,000 the two lower-order terms have total size below $0.079t$ and their ratios decrease thereafter.

For $n\ge n_0$, $b\le1.5\log n$, $y\ge(8/9)n/\log^3 n\ge90{,}000$, and $n-y\ge0.99n$. The dials through $y$ cost at least
$$
2(n-y)\theta(y) > 1.05\, n^2/\log^3 n .
$$
Subtracting them from the input thus leaves **more than $n$ log units** on the board. The two-cell encoding of the remaining dials loses at most $n$ by rounding and can recover the entire row order. At $n=10^{12}=1000^4$, $b=40$ and $y=46{,}875{,}000$. [Exact constants, integer cutoffs and recovery controls](../receipt-archives/2026-11-26-pal-sieve-frame.json)

## Unresolved

We have a universal decoder after the displayed cutoff, and a separate proof that dials through $\sqrt n$ can be set aside in the RH implication. At fourth powers where $y>\sqrt n$, funding $\sqrt n<p\le y$ in addition to the already retained larger distances would complete the one-sided paper route. The fixed Lean implication also asks for a bound on unused capacity. Individual fits of two families need a shared storage budget before they can be combined.
