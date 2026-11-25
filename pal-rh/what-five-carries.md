# What 5 carries through doubling and tripling

Christopher Daniel Pang and Hearthline · 25 November 2026

Pang asked what a prime has to carry from its own frame into the next one. In this particular construction the answer for 5 is **a signed amount of $-1/15$**. After the first four contributions, every layer of doublings and triplings has to pass that amount on when the constant target is fitted exactly. The same prime carries $-1/30$ for the first-tick target. Two different paths around an interior square give precisely the same physical reading at **every integer**. Where the amount exits a finite frame can change the whole error.

Here is the constant-target calculation before the general notation. From 5 the relevant source terms are
$$
-\frac15+\frac1{10}+\frac1{15}-\frac1{30}=-\frac1{15}.
$$
Later multiples $5\cdot2^i3^j$ contribute zero new source because they contain a repeated prime. Add the accounts for every vertex through one layer. The amount sent from one included vertex to the next cancels once as outgoing and once as incoming. Only the amount crossing the outer layer remains. That is where the $-1/15$ has to be. A different prime factorization can reverse its sign. The core 35 carries $+1/105$.

## The two clocks are actual residue measurements

Let $b_d(k)=(k\bmod d)/d$, $T_m(k)=k\bmod m$, and $D_mf(k)=f(\lfloor k/m\rfloor)$. Use two independently adjustable, normalized parents $2b_2$ and $3b_3$. Give their copies at $m$ coefficients $A_m,B_m$ and let $x_m=A_m/m,\ y_m=B_m/m$. These quantities are signed. The two contributions are exactly
$$
x_m(T_{2m}-T_m),\qquad y_m(T_{3m}-T_m).
$$
For example, going $m\to2m\to6m$ with a unit amount gives $T_{6m}-T_m$. Going $m\to3m\to6m$ gives the same function of $k$. This identity holds before taking a norm, a limit or an average. [Actual row identity, square and finite graph formula](PALRH/CarriedPrime.lean)

Every positive integer belongs to exactly one grid $n=r2^i3^j$, with $\gcd(r,6)=1$. The excess sent out of vertex $n$ is
$$
d_n=x_n+y_n-[2\mid n]\,x_{n/2}-[3\mid n]\,y_{n/3}.
$$
For a finite collection of edges the physical fit is $F=-\sum_n d_n T_n$. The origin coefficient multiplies $T_1=0$, while the first physical row gives $F(1)=A_1+B_1=d_1$.

## Why the amounts are forced

For $n\ge2$ take the finite reading $D_n(h)=\sum_{t\mid n}\mu(n/t)(h(t-1)+h(1)-h(t))$, with $h(0)=0$. A single residue wraps precisely at a multiple of its modulus, so $D_n(b_a)=[a=n]$ for $a\ge2$ by Möbius inversion. This is the classical divisor-coordinate reading also used in our [initial construction](README.md#precisely-which-moduli-matter). Consequently $D_n(F)=-n d_n$.

For the occupied target $\chi(k)=[k\ge1]$, the expression inside the sum is $1$ for $t>1$ and $0$ at $t=1$. For the first tick $e(k)=[k=1]$ there is one additional unit at $t=2$. Exact agreement through $K$ therefore forces, for $1\le n\le K$,
$$
q_n^{\chi}=\frac{\mu(n)}n,\qquad
q_n^{e}=\frac{\mu(n)-[2\mid n]\mu(n/2)}n,\qquad d_n=q_n.
$$
At $n=1$ both formulas agree with the first physical reading. For either target, at every fresh prime $p>3$ the exact constraint is $A_p+B_p=-1$. At a squarefree product of two such primes the sum is $+1$. The total is forced even when the two individual coefficients remain free.

For squarefree $r>1$ coprime to 6, summing $q^\chi$ over $i+j\le t$ gives $\mu(r)/(3r)$ for every $t\ge2$. All four possible squarefree sources are then included. In the first-tick case the extra contribution is a shifted copy with coefficient $-1/2$, giving $\mu(r)/(6r)$ for every $t\ge3$. Summing $d_n$ cancels the interior and leaves $\sum_{i+j=t}(x_{r2^i3^j}+y_{r2^i3^j})$. This proves the assertion about 5.

## How much has to travel in an approximate fit

Write $E=\sum_{k\ge1}(T(k)-F(k))^2/[k(k+1)]$ for either target $T$. The error at row $k$ has magnitude at most $(k+1)\sqrt E$. Since $\sum_{t\mid n}\mu(n/t)=0$ for $n\ge2$, the common row-one contribution in $D_n$ cancels. Bounding the two neighboring rows gives
$$
|D_n(T-F)|\le 3\sqrt E\sum_{t\mid n}t\le 3n^2\sqrt E .
$$
Over a triangle with $r3^t\le K$ and $r>1$ the divergence error is less than $14K\sqrt E$, because $\sum_{i+j=h}2^i3^j=3^{h+1}-2^{h+1}$. If $\sqrt E\le1/(168K^2)$, the outgoing magnitude is at least $1/(4r)$ for the constant and $1/(12r)$ for the first tick, on the same layers as above.

There is a joint price across the grids. Take $K=3^{2M}$, $M\ge3$. Use all squarefree $1<r\le3^M$ coprime to 6 and all layers $3,\ldots,M$. Their edges are disjoint. Under the displayed error condition,
$$
\sum_m\frac{|A_m|+|B_m|}{m}
\ \ge\ c(M-2)\left(\frac{H_{3^M}}6-1\right),
\quad c=\frac14\text{ for }\chi,\quad c=\frac1{12}\text{ for }e.
$$
Indeed every positive integer has a unique expression $2^a3^b u^2 r$ with $\gcd(ur,6)=1$ and $r$ squarefree. The harmonic sum through $X$ is at most the sum of $1/r$ over those $r\le X$ multiplied by $\sum2^{-a}3^{-b}=3$ and $\sum u^{-2}<2$. Subtract the $r=1$ term. The bound grows quadratically in $M$. With $M$ chosen as the largest allowed by the error condition this gives order at least $(\log(1/E))^2$ in the required absolute coefficient budget as $E$ tends to zero.

Even in the one core $r=5$, Cauchy–Schwarz on the $2(t+1)$ outgoing edges gives $\sum_{i+j=t}(x_n^2+y_n^2)\ge c^2/[2r^2(t+1)]$ on these layers. Thus the squared normalized coefficient budget required in this single core is unbounded along any sequence approaching either target. Coefficient energy and physical squared error are separate quantities.

A source $R$ at the origin of a grid admits the explicit split
$$
x_{ij}=\frac{R(i+1)}{(t+1)(t+2)},\qquad
y_{ij}=\frac{R(j+1)}{(t+1)(t+2)},\qquad t=i+j .
$$
Every node of layer $t$ sends $R/(t+1)$. Its two incoming contributions add to that amount for $t>0$. The sum of squared coefficients on the layer is $R^2(2t+3)/[3(t+1)(t+2)]$. This attains the order of the shell lower bound for carrying one source. The actual fit still has to be evaluated on physical rows. [Lean conservation and split](PALRH/CarriedPrime.lean)

## Removing all the interior paths

Fix a maximum copy scale $K$ and require the first $K$ physical rows to be exact. In each grid keep the vertices $m\le K$ and the exit vertices $v>K$ of the edges $m\to2m,3m$. Identify exit edges that land on the same integer. A signed exit mass $\beta_v$ has just one constraint per core,
$$
\sum_{v\ {\rm exiting\ core}\ r}\beta_v
=\sum_{\substack{n\le K\\ n=r2^i3^j}}q_n .
$$
These conditions are **both necessary and sufficient**. Each finite grid is connected to its least vertex $r$ by division by 2 or 3. Choose one allowed predecessor at every other vertex, including each exit. Starting at the leaves of this tree, set the incoming edge equal to the known outgoing total minus the prescribed divergence. At the root the one displayed balance closes the account. Rational exit choices give rational legal coefficients.

Every interior route that realizes the same exits gives exactly the same fit,
$$
F(k)=-\sum_{n\le K}q_n(k\bmod n)+\sum_v\beta_v(k\bmod v)
     =\sum_{n\le K}nq_n\lfloor k/n\rfloor-\sum_v v\beta_v\lfloor k/v\rfloor .
$$
For $1\le k\le K$ the exit floors vanish. The first sum is $1$ for the occupied target because $\sum_{d\mid j}\mu(d)=[j=1]$. For the first tick one subtracts the same answer at $\lfloor k/2\rfloor$. This proves the converse on physical rows and removes every interior path from the optimization problem.

## Exactly the same first 256 rows

We tried two choices of exit distribution at $K=256$. The first divides each node’s available signed amount in proportions $(i+1):(j+1)$ and stops at the hard integer cutoff. It gets every one of the first 256 rows right for each target. For the constant the error already exceeds one by row 4,857. For the first tick it exceeds one by row 5,761. Every later contribution to squared error is nonnegative. [Integer check of the failed cutoff](../receipt-archives/check_pal_two_clock_flow.py)

At the same cutoff the grid has 256 distinct exits in 85 cores, hence 171 free coordinates. We refitted just those coordinates on physical rows through 32,768 with numerical least squares, rounded them to rational values and restored each core balance exactly. A separate integer calculation reconstructs legal clock coefficients on a tree and bounds the entire infinite error.

| Squared error with the first 256 rows exact | Fixed proportional split | Refitted exits, whole infinite interval |
| --- | --- | --- |
| Constant | $>1$ | $0.19490\le E\le0.21951$ |
| First tick | $>1$ | $0.08441\le E\le0.09399$ |

For the upper bounds, the checker sums two million physical rows. For the remainder, write the eventual error as $t-\sum_d c_db_d$. The period mean of $b_d$ is $(d-1)/(2d)$. The covariance of $b_d,b_j$ is $(\gcd(d,j)^2-1)/(12dj)$, since conditioning on the common residue leaves independent uniform digits by the Chinese remainder theorem. Let $V$ be the resulting mean squared error. The discrepancy of partial sums of each centered product is bounded by its period $\mathrm{lcm}(d,j)$. Summation by parts therefore bounds the remaining error after $H$ by
$$
\frac{V}{H+1}+
\frac{2|t|\sum_d|c_d|d+\sum_{d,j}|c_dc_j|\mathrm{lcm}(d,j)}
     {(H+1)(H+2)} .
$$
This calculation applies to the stored rational witnesses. It does not assume the chosen exits are the optimal full-tail exits. [Rational exits](../receipt-archives/2026-11-25-pal-two-clock-exits.json) · [Independent standard-library checker](../receipt-archives/check_pal_exits.py)

## One larger frame beats every smaller-frame fit

We can test every one of the 171 free coordinates at once. In each core choose its largest exit $a$ as the balancing anchor. Moving mass to another exit $v$ changes the fit by $X_v(k)=T_v(k)-T_a(k)$. This column vanishes before row $v$ and reads $-v$ at row $v$. Thus the free columns have distinct pivots.

Take a finite row measurement $\ell$ on rows 257 through 32,768. Start with the rounded, weighted residual of the trial. Enforce $\sum_k\ell_k X_v(k)=0$ at every exit by adjusting only the pivot rows in descending order of $v$. A smaller pivot cannot disturb a column already settled. Every operation is rational. Once these sums are zero, $\sum\ell_k(T(k)-F(k))$ has the same value $a_0$ for *every* exact-prefix fit of width 256. Its complete squared error is at least $a_0^2/\sum_k\ell_k^2/w_k$ by weighted Cauchy–Schwarz. This gives the first numeric column below. [Finite dual bound](PALRH/CarriedPrime.lean) · [Exact null measurements](../receipt-archives/check_pal_exits.py)

We then opened copies at scales 257 through 512. Every one is zero on the first 256 rows. We fitted these two sets of coefficients together with the original free exits, rounded to exact rational values, and used the same whole-tail argument, with ten million direct rows. The smaller-frame lower bound applies to **all real choices** in that frame. The larger-frame upper bound comes from **one legal rational choice**.

| Target, first 256 rows exact throughout | All fits with copy scales through 256 | Exhibited fit with copy scales through 512 |
| --- | --- | --- |
| Constant | $E\ge0.16939$ | $0.14106\le E\le0.15431$ |
| First tick | $E\ge0.07740$ | $0.06114\le E\le0.06529$ |

This establishes a strict gain over the entire old frame on both targets. A least-squares routine selected the candidates. The inequalities follow from their stored rational values, the exact dual identities and bounds on the infinite tails. [Reproduce the search](../receipt-archives/select_pal_exits.py) · [Widened witnesses](../receipt-archives/2026-11-25-pal-two-clock-exits.json)

For any fixed finite exact head and any finite feasible copy width, some larger width has a strict gain over the old best on the occupied target. The statement also holds for the first tick when the first row is protected. To see this, minimize over the original finite-dimensional real affine space. The minimizer is a bounded periodic fit. The [strict-successor argument](every-fit-has-a-successor.md) works over real coefficients and supplies a remote binary carry with positive gain, leaving the head alone. The finite exact-head equations have rational coefficients and rational right sides. Rational solutions are dense in their real solution space by Gaussian elimination. A close rational approximation to the improved solution still beats the old minimum. This argument supplies neither a fixed enlargement factor nor a uniform amount of gain. The table proves both strict separations for the specific doubling from 256 to 512.

## What it costs to protect a finite head

The number of rows to protect and the number of scales to allow can now be kept independent. For either target, demanding *any fixed finite head exactly* preserves the arbitrary-tolerance question once larger scales are allowed. This holds in the full legal space and even in any legal rational subspace containing every binary copy.

Here is the actual repair. Put $C_m(k)=\lfloor k/m\rfloor\bmod2$ and $u_m=C_m-C_{m+1}$. Its values lie in $\{-1,0,1\}$. It vanishes at $k<m$ and has value one at $m$. If a current fit $F$ has row error $a=T(m)-F(m)$, replace it by $F+a u_m$. Earlier rows are unchanged, and row $m$ is now exact. The squared cost of the added function is at most $a^2$, while the old error already pays $w_ma^2$. Squaring the triangle inequality in the physical norm gives
$$
E(F+a u_m)\le(2+2m(m+1))\,E(F).
$$
Repair $m=1,\ldots,H$ in that order. The product of these finite factors is enough to transfer arbitrarily good unconstrained fits to arbitrarily good fits exact on a specified $H$. The coefficients stay rational and the added copy scales reach at most $H+1$. The reverse implication simply forgets the head requirement. The factors grow rapidly with $H$, so this lemma gives no simultaneous rate when $H$ grows with the requested accuracy. [Quantitative repair and both directions in Lean](PALRH/Protected.lean)

Pang’s PAL v2.4 supplied the question about an independently carried frame. RPL supplies the arithmetic shell, and Boundary-Ledger Accounting asks what crosses it after internal routes cancel. The classical Möbius coordinate detector is credited in the [prime-phase derivation](README.md#precisely-which-moduli-matter). The two-clock accounting, physical endpoint reduction and signed numerical comparisons were derived here. The upstream proof supplied no mathematical input to this calculation. Literature priority for the application is unassessed. [Corpus sources](CORPUS-ROUTES.md)

## Unresolved

An all-tolerance construction needs exit distributions whose **whole physical errors** tend to zero. The result above identifies every free exit for the exact-prefix policy at each cutoff and puts lower bounds on how much must travel. It leaves the choice of exits across increasing cutoffs open. The exact finite prefix has an unconditional repair when the copy width can grow independently. An estimate uniform enough to reach all tolerances remains open.
