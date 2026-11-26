# What a Pascal row pays for

Christopher Daniel Pang and Hearthline · 26 November 2026

Let $P_n=\prod_{a=0}^n\binom na$ and $A_n=n^n/n!$. One complete Pascal packet chooses one subset of each size. The subsets need not be nested. Let $R_n=\prod_{\sqrt n<p\le n}p^{n-p}$ count one direction of large-prime trips. The board has $B_n=n^{n^2}$ states. [Work through two and sixteen](../proofs/two-pascal-rows-fit-on-every-board.md)

## A board can always carry two packets

For every positive $n$,
$$
 (n!)^n P_n^2\le B_n .
$$
Indeed $P_{n+1}(n+1)!=(n+1)^{n+1}P_n$ follows by multiplying $(a+1)\binom{n+1}{a+1}=(n+1)\binom na$ over $a=0,\ldots,n$. Hence $P_n=\prod_{j=1}^n A_j$. Put $b_j=(1+1/j)^j$, so that $A_1=1$ and $A_{j+1}/A_j=b_j$. The sequence $b_j$ increases. With $u=j+1$, Bernoulli’s inequality gives the explicit comparison
$$
 \frac{b_{j+1}}{b_j}=(1-u^{-2})^j(1+u^{-1})
 \ge (1-ju^{-2})(1+u^{-1})=1+u^{-3}.
$$
Pair $A_j=\prod_{i<j}b_i$ with the other end of the row. The ratio $A_n/A_{n+1-j}$ comprises $j-1$ consecutive factors ending at $b_{n-1}$. Its $i$th index is $n-j+i\ge i$. Thus $A_j A_{n+1-j}\le A_n$. Multiply over $j$ to obtain $P_n^2\le A_n^n$. The finite code ranks subsets by the combinatorial number system, combines them with Lehmer-ranked permutations, and writes the result in base $n$. [Formal inequality](PALRH/PascalBoard.lean) · [Reversible implementation](../receipt-archives/check_pal_pascal_board.py)

## What is earned at one prime?

For $p>\sqrt n$, write $n=qp+r$ with $0\le r<p$. There are exactly
$$
 v_p(P_n)=q(p-1-r)
$$
available radix-$p$ places in one Pascal packet. Legendre’s floor formula stops after the first power on every factorial up to $n$. A subset size $a$ contributes one $p$ exactly when $a\bmod p>r$. Each of the $q$ full blocks of residues contributes $p-1-r$ and the final partial block contributes zero.

For a direct view of this condition, arrange the $n$ labels in $q$ cycles of length $p$ and $r$ fixed positions. Rotate the cycles together. An invariant subset contains whole cycles plus some fixed positions. Its size has residue at most $r$. For any other size all subset orbits have exactly $p$ members, providing a genuine free $p$-way choice. The factorial calculation supplies the exact multiplicity, including the sizes where fixed subsets exist. [Lean valuation proof](PALRH/PascalCarry.lean) · [Lagarias and Mehta on Pascal-row valuations](https://arxiv.org/pdf/1409.4145)

Let $g=\gcd(R_n,P_n)$, $M=R_n/g$ and $U=P_n/g$. Prime by prime $g$ admits $\min(n-p,v_p(P_n))$ genuine digits in each direction. Because $g\mid P_n$, the two resulting packets and all the permutations fit at every size. The remaining integers $M,U$ are coprime. If $M\le U$, put a rank from $0$ to $M-1$ in the unused $U$-state register. Combining with the $g$-state register gives $R_n\le P_n$ and hence $(n!)^nR_n^2\le B_n$. At $n=16$, $M=175$. This is a multiplicative count for that one head. [Exact controls](../receipt-archives/2026-11-26-pal-pascal-board.json)

## How much the same-prime matches pay

The requirement per prime is $n-p$. The deficit in registered places before exchanging between primes is
$$
 (n-p)-v_p(P_n)=q+(q+1)r-p .
$$
Put $t=p/n$. In each fixed cell $1/(q+1)<t\le1/q$, the normalized difference tends to $d_q(t)=(q+1)-(q^2+q+1)t$. Its positive and negative triangular areas are, respectively,
$$
 \frac{q^2}{2(q+1)^2(q^2+q+1)},\qquad
 \frac{1}{2q^2(q^2+q+1)}.
$$
The zero lies at $(q+1)/(q^2+q+1)$. The prime number theorem turns these weighted cell sums into the displayed areas as $n\to\infty$. Restrict first to $t\ge\delta$ with finitely many jumps. On $p<\delta n$, both the demand and this one-carry capacity are at most $n$ per large prime, and their weighted total is $O(\delta n^2)$ since $\theta(y)=O(y)$. Small primes occur only in the unused side and have total Pascal valuation cost $O(n^{3/2})$, by the bound of one carry per prime-power digit per subset size and the elementary prime-count estimate.

Subtracting the second cell area from the first gives
$$
 \frac12\left(\frac1q-\frac1{q+1}-\frac1{q^2}+\frac1{(q+1)^2}\right).
$$
It sums to zero. Write $\alpha=\sum_{q\ge1}1/[2q^2(q^2+q+1)]=0.1917856601\ldots$. The tail after $Q$ is at most $1/(6Q^3)$. Thus both the unpaid and the unused log counts, before the global exchange, are $\sim\alpha n^2$. Meanwhile $\log R_n\sim n^2/2$. Consequently $\log g/\log R_n\to1-2\alpha=0.6164286796\ldots$. For $n=10^7$ the actual matched contribution is between 0.30802222 and 0.30802223 times $n^2$, and the unpaid contribution is between 0.19144534 and 0.19144535 times $n^2$. [Directed prices and exact first cells](../receipt-archives/check_pal_pascal_board.py)

There is a useful sign to the exchange. For each fixed $Q\ge1$, the Pascal factors with $p>n/(Q+1)$ have a net surplus over the requested digits in that same set of primes asymptotic to $Qn^2/[2(Q+1)^2]$. This follows by telescoping the first $Q$ cell differences, with the sign reversed for surplus. In particular each fixed upper collection can fund itself eventually, even if it cannot pay each prime in the original radix. This is consistent with Du and Lagarias’s scaling function for partial factorizations at reciprocal integers. Their Theorem 1.7 has the explicit additional hypothesis $\log x/\log n\to1$. A fixed power $x=n^a$ with $a<1$ lies outside that theorem’s range. [Du and Lagarias, Theorems 1.1 and 1.7](https://arxiv.org/pdf/2006.15439)

## Why changing the sizes of positive rows cannot pay every prime in its own radix

Allow any nonnegative mixture of subrows whose top sizes are at most $n$. For one direction, the entire asymptotic budget has log size $n^2/2$. Even a choice of weights depending on $n$ cannot meet every large prime's demand using those primes’ own factors at this budget. The obstruction can be seen at the first five Möbius entries.

In the scale $t=p/n$, a row of top size $\lambda n$ has leading registered credit per $n$
$$
 K_\lambda(t)=q\bigl((q+1)t-\lambda\bigr)
             =\sum_{d\le\lambda/t}(2dt-\lambda),\qquad q=\lfloor\lambda/t\rfloor .
$$
Set $K_\lambda(t)=0$ for $t>\lambda$. Each kernel is nonnegative. For a nonnegative inventory $\nu$ on scales $0<\lambda\le1$ write $F(t)=\int K_\lambda(t)d\nu(\lambda)$. The desired one-direction profile is $F_0(t)=(1-t)_+$. Integrating on each cofactor cell gives $\int_0^1 K_1(t)\,dt=\sum_{q\ge1}1/[2q(q+1)]=1/2$, hence $\int K_\lambda=\lambda^2/2$ by scaling.

To read the underlying row inventory, put $H(y)=\int_{[y,1]}(2y-\lambda)\,d\nu(\lambda)$. The kernel identity gives $F(t)=\sum_{d\le1/t}H(dt)$. Finite Möbius inversion recovers $H(y)=\sum_{k\le1/y}\mu(k)F(ky)$. The total mass of rows **at least** $y$ is recovered by the second elementary identity
$$
 U(y)=\nu([y,1])=\frac{H(y)}{y}+\frac1{y^2}\int_y^1 H(t)\,dt.
$$
For a single row at $\lambda\ge y$, the two numerator contributions are $y(2y-\lambda)$ and $y\lambda-y^2$; their sum is $y^2$. A row below $y$ contributes zero. Linearity proves the formula including an atom at the boundary.

For the target $F_0$, the same operations require
$$
 U_0(y)=\frac1{2y^2}\sum_{k\le1/y}\frac{\mu(k)}{k}
             -\frac12\sum_{k\le1/y}k\mu(k).
$$
On $1/6<y<1/5$ the first sum is $1-1/2-1/3-1/5=-1/30$ and the second is $-9$. Thus $U_0(y)=9/2-1/(60y^2)$ there. It extends continuously to both endpoints, since an entering term at $k=1/y$ contributes zero. Raising the threshold from $1/6$ to $1/5$ would increase the required mass from $39/10$ to $49/12$. This asks for **$11/60$ more rows above the higher threshold**. Every actual positive row inventory decreases weakly as the threshold rises. [Exact endpoint readings and monotonicity in Lean](PALRH/PascalInventory.lean)

### This failure has a positive cost even on the actual primes

Let $\phi$ be the tent of height one on $[a,b]=[1/6,1/5]$ with midpoint $v=11/60$. For a positive inventory $\int\phi\,d\nu\ge0$. On the target, integration by parts against $U_0$ gives
$$
 L(F_0)=\int\phi'(y)U_0(y)\,dy
  =-\frac1{30}\int_a^b\frac{\phi(y)}{y^3}\,dy=-\frac1{11}.
$$
The integral of the tent divided by $y^3$ is $(b-a)/(2abv)=30/11$. The same functional on $F$ is $L(F)=\int\phi'(y)U(y)dy=\int\phi\,d\nu$. Substituting the two finite recovery formulas expresses $L(F)=\int_a^1 F(t)\Psi(t)dt$. Indeed the coefficient of $H(t)$ is
$$
 w(t)=\phi'(t)/t+\int_a^t\phi'(y)y^{-2}dy,\qquad
 \Psi(t)=\sum_{k\le t/a}\frac{\mu(k)}k w(t/k).
$$
The slopes of $\phi$ have magnitude 60 and $\int|\phi'|=2$. Thus $\|w\|_\infty\le60/a+2/a^2=432$, and $\|\Psi\|_\infty\le432(11/5)<1000$. It follows that every positive row profile satisfies $\int_a^1|F-F_0|\ge1/11000$.

For the discrete implication take nonnegative multiplicities $w_{m,n}$ of Pascal rows of tops $m\le n$. Assume their registered digit counts cover $n-p$ at each actual prime $p>\sqrt n$. Then
$$
 \liminf_{n\to\infty}\frac2{n^2}\sum_{m\le n}w_{m,n}\log P_m\ \ge\ 1+\frac1{5500}.
$$
The same bound holds along any unbounded sequence of successful heads. To prove it, restrict to a subsequence with bounded normalized cost; unbounded cost requires no estimate. At each fixed $e>0$, $\log P_m\sim m^2/2$ uniformly for $en\le m\le n$, so the total multiplicity at these scales is bounded in terms of $e$. On $[e,1]$ each $K_{m/n}$ has uniformly bounded variation, with at most $1/e$ jumps and piecewise slopes bounded in terms of $e$. Therefore the combined profile $F_n(t)=\sum_m w_{m,n}K_{m/n}(t)$ and $(F_0-F_n)_+$ have uniformly bounded variation there. For $p>\sqrt n$, the *exact* row valuation divided by $n$ is $K_{m/n}(p/n)-\lfloor m/p\rfloor/n$, so $F_n\ge F_0$ at each actual prime in the interval for sufficiently large $n$. Partial summation against $\theta(nt)/n=t+o(1)$ now gives $\int_e^1(F_0-F_n)_+=o(1)$. The endpoint convention at a kernel jump gives the left-limit value there; the error in sampling either choice is bounded by the same uniform cumulative error times the variation.

For $e<1/6$, the dual bound therefore implies $\int_e^1 F_n\ge\int_e^1 F_0+1/11000-o(1)$. Only rows with $m/n\ge e$ contribute on that interval, and their normalized cost is at least $(2-o(1))\int_e^1F_n$ by the kernel integral and Pascal asymptotic. Let $e$ decrease to zero. This proves the stated extra cost. The argument concerns **positive separate row resources priced prime by prime**. The universal packing and the global coprime exchange above explicitly permit conversion between different radices. [Rational calculations and positive-inventory controls](../receipt-archives/check_pal_pascal_board.py)

A signed row in a formula would need a construction if it is to save physical space. For example, two finite packets projecting uniformly onto the same $g$ states have $|A||B|/g$ compatible pairs. One must exhibit those projections and recover the required independent inputs from the compatible pairs. The negative mass calculated here identifies a place to test such sharing.

## The remaining two-integer test

A universal eventual comparison $M\le U$ at $n=k^4$ is equivalent to RH. The forward implication follows from the universally funded Pascal packets and the one-sided large-prime fit. Conversely $\log P_n=n^2/2+O(n\log n)$ follows by summing $\log(j!)=j\log j-j+O(\log(2j))$. From the prime-square and cutoff identities,
$$
 \log P_n-\log R_n=(5/3+o(1))n^{3/2}-(I_\psi(n)-n^2/2).
$$
Under RH the last absolute term is at most $(0.08+o(1))n^{3/2}$, so $P_n>R_n$ at every sufficiently large $n$. This proves the equivalence and leaves the unconditional inequality at unbounded fourth powers to establish. The finite input comparison naturally retains the surplus and deficit separately. The leading $n^2$ asymptotics alone cannot compare their difference on the smaller scale of interest. [Small-prime removal and one-sided consequence](the-factorial-frame-for-prime-distances.md) · [Johnston, Lemma 2.6](https://arxiv.org/pdf/2201.06184)
