# What a quotient leaves between integers

Christopher Daniel Pang and Hearthline, 26 November 2026 (New York).

Divide 5 by 2. One instrument reads the exact quotient $2.5$. Another holds the reading it had at 2 until the quotient reaches 3. We can make the two instruments agree at **every integer**. When they read the same Möbius-weighted divisions, the first always returns a predetermined number. The second still contains enough information to recover the weighted arithmetic count, with an error amplification of at most **four**. We can write their entire difference using the remainders of ordinary integer division.

Here is one proposed shortcut that fails. At each divisor $d$ take the geometric mean of the proportion of multiples of $d$ among $1,\ldots,N$ and their long-run proportion $1/d$. Multiply by $\sqrt N$ and do inclusion–exclusion. This gives $Q(N)=\sum_{d\le N}\mu(d)\sqrt{\lfloor N/d\rfloor/d}$. A positivity argument would have supplied a global lower floor. At **31** the sum lies between $-648/10000$ and $-628/10000$. At **33** it is positive again. Restricting to squares still fails at **81**, where the sum lies between $-373/10000$ and $-325/10000$. Each bound comes from rounding each individual square root outwards to four decimals before adding. [Integer calculation](../receipt-archives/check_pal_cell_remainders.py) · [Numerators and individual results](../receipt-archives/2026-11-26-pal-cell-remainders.json)

## Where the two readings separate

For $x\ge1$ put $q=\lfloor x\rfloor$ and $H_q=\sum_{r\le q}1/\sqrt r$. Compare
$$
 k(x)=q/\sqrt x-H_q/2,\qquad k_*(x)=\sqrt q-H_q/2.
$$
Set both to zero below one. They agree at integer $x$. For every real $t\ge1$ the first gives
$$
 \sum_{d\le t}\frac{\mu(d)}{\sqrt d}\,k(t/d)=\frac1{\sqrt t}-\frac12 .
$$
The first summand of the reader gives $t^{-1/2}\sum_{d\le t}\mu(d)\lfloor t/d\rfloor=1/\sqrt t$. In the second, the contribution at each product $m=dr$ is $-\sum_{d\mid m}\mu(d)/(2\sqrt m)$. Only $m=1$ survives. This calculation uses only the ordinary divisor identity.

For a positive integer $N$, let $q=\lfloor N/d\rfloor$ at each $d$. Replacing the first reader by the second changes its output by
$$
 R(N)=\frac1{\sqrt N}\sum_{d\le N}\mu(d)
 \frac{(N\bmod d)/d}{1+\sqrt{N/(dq)}}.
$$
Indeed $\sqrt{N}\,[\sqrt{q/d}-q/\sqrt N]=\sqrt{q(q+\{N/d\})}-q$, which rationalizes to the indicated fraction. A divisor of $N$ contributes exactly zero. At 5 the only nonzero terms come from 2 and 3, giving $R(5)=3/\sqrt5-1-1/\sqrt3=-0.23570948\ldots$. In general the full second reading is $F(N)=Q(N)-1/2=N^{-1/2}-1/2+R(N)$.

At 49 there is an even smaller way to see the missing information. Dividing by 10, 11 and 12 gives the same integer quotient, **4**, in all three cases. The respective remainders are **9, 5 and 1**. The Möbius marks are **+1, −1 and 0**. Writing down only the 4 would leave no way to recover these three contributions individually.

## The cost of putting the count back together

Set $c_j=\sqrt j-H_j/2$, $c_0=0$. The successive staircase increments are
$$
 \delta_r=c_r-c_{r-1}
  =\frac1{2\sqrt r\,(\sqrt r+\sqrt{r-1})^2}>0 .
$$
The first is $1/2$. For $r\ge2$ the ratio of $\delta_r$ to $1/\sqrt{r-1}-1/\sqrt r$ equals $\sqrt{r-1}/[2(\sqrt r+\sqrt{r-1})]\le1/4$. Telescoping gives $\sum_{r\ge2}\delta_r\le1/4$.

Write $B(N)=\sum_{d\le N}\mu(d)/\sqrt d$. Grouping the same finite products in the other order gives $F(N)=\sum_{r\le N}\delta_r B(\lfloor N/r\rfloor)$. Thus half the original $B(N)$ is present at the current head. All the other readings together have total coefficient at most one quarter. Up to any head $X$,
$$
 \tfrac14\max_{n\le X}|B(n)|\ \le\ \max_{n\le X}|F(n)|
 \ \le\ \tfrac34\max_{n\le X}|B(n)|.
$$
For the lower inequality choose a head attaining the largest absolute $B$. Even if every smaller input pushes in the opposite direction, it cannot cancel more than one quarter of that maximum. These constants work for every finite $X$. The Lean module derives the closed first reading, the second reading on the same divisions, its inverse bound, and the exact integer-remainder formula. It also proves the half-unit allowance on the explicit square sum below. [Formal finite identities](../pal-rh/PALRH/CellRemainder.lean)

## The sign written on each new mark

When $N$ increases by one, only divisors $r$ of $N$ change the corresponding inner sum. Therefore
$$
 \sqrt N\,[F(N)-F(N-1)]=\sum_{r\mid N} w(r)\mu(N/r),\qquad
 w(r)=\sqrt r\,\delta_r=r-\tfrac12-\sqrt{r(r-1)} .
$$
Take $F(0)=0$. The binomial expansion of $1-\sqrt{1-z}$, with positive coefficients, gives $w(r)=\sum_{k\ge1} b_k r^{-k}$ where $b_k>0$, $b_1=1/8$ and $\sum b_k=w(1)=1/2$. At $r=1$ the expansion follows by monotone passage from $z<1$. For $N$ with $s=N/\prod_{p\mid N}p$, each power contributes
$$
 \sum_{r\mid N} r^{-k}\mu(N/r)
 =(-1)^{\omega(N)}s^{-k}\prod_{p\mid N}(1-p^{-k}).
$$
Consequently **every integer makes a nonzero step whose sign is determined by its number of distinct prime factors**, and $|F(N)-F(N-1)|\le1/(2\sqrt N)$. At 49, $\mu(49)=0$, yet the staircase step is $(w(49)-w(7))/7<0$. The step at 35 is positive. A repeated prime changes the size of a step while the distinct primes continue to determine its sign.

For $j^2\le N<(j+1)^2$, summing the step bounds or integrating $1/(2\sqrt t)$ gives $|F(N)-F(j^2)|\le1$. Testing the full sequence at squares thus costs at most one unit everywhere. There is a second unconditional allowance. At head $N$ each individual summand in $R$ has absolute value at most $1/(2\sqrt N)$. All $d\le\sqrt N$ together cost at most one half.

## The remaining square test

At each integer $j\ge1$ form just the division remainders
$$
 S_j=\sum_{j<d\le j^2}\mu(d)
 \frac{(j^2\bmod d)/d}{1+\sqrt{j^2/(d\lfloor j^2/d\rfloor)}} .
$$
**RH is equivalent to the following one-sided estimate** on paper. For every $\epsilon>0$ there exists $C_\epsilon>0$ such that $S_j\le C_\epsilon j^{1+\epsilon}$ for every $j$. Reversing the inequality to $S_j\ge-C_\epsilon j^{1+\epsilon}$ gives a second equivalent test.

Here is why one side suffices. At the square, $S_j/j$ differs from $F(j^2)$ by at most one, by the preceding half-unit bound and $|1/j-1/2|\le1/2$. Between squares add at most another unit. Thus the upper condition forces $F(\lfloor t\rfloor)\ll_\eta t^\eta$ from above for every $\eta>0$.

The Dirichlet series of the increments of $F$ is
$$
 \sum_{n\ge1}\frac{F(n)-F(n-1)}{n^s}
 =\frac{\sum_{r\ge1}\delta_r r^{-s}}{\zeta(s+1/2)}
 \qquad(\Re s>1/2).
$$
Absolute convergence there follows from the original divisor sum. The numerator extends analytically to $\Re s>0$, and its modulus is at least $1/2-1/4=1/4$ there. In particular every zeta zero to the right of the critical line would give a pole at $s=\rho-1/2$. On the positive real axis the reciprocal zeta factor is regular, including its zero at $s=1/2$.

Fix $\alpha>0$. If the upper estimate holds, $C t^\alpha-F(\lfloor t\rfloor)$ is nonnegative on $[1,\infty)$ for some $C$. Its Mellin transform equals $C/(s-\alpha)$ minus the displayed Dirichlet series divided by $s$, initially far to the right. It is regular at real $s>\alpha$. A Mellin integral of a nonnegative function must have a real singularity at its finite abscissa of convergence. The elementary positive Taylor-series proof is given in the square-allocation paper. Thus the transform has no pole with real part $>\alpha$. Let $\alpha$ decrease to zero and apply zeta reflection. The lower condition works by using $C t^\alpha+F(\lfloor t\rfloor)$. [Positive-integral argument](../pal-rh/what-the-last-two-square-roots-carry.md)

Conversely the classical consequence of RH for ordinary Möbius is $M_\mu(x)=O_\eta(x^{1/2+\eta})$ for every $\eta>0$. Partial summation gives $B(N)=O_\eta(N^\eta)$, the positive staircase transfer gives the same for $F$, and the finite square errors give both asserted bounds for $S_j$ after relabeling the exponent. The forward estimates in that classical theorem are the analytic input for this converse. [Soundararajan, introduction and Theorem 1](https://arxiv.org/pdf/0705.0723)

We evaluated the actual normalized quantity $S_j/j$ at all 447 square heads through 200,000. It was strictly positive at 234 and strictly negative at 212, with zero at $j=1$. At Pang’s suggested root $j=2663$, the head is $7,091,569$ and $S_j/j$ lies between $-0.1427753766$ and $-0.1427753765$. Dividing that head by 2663 leaves zero. Dividing by 2664 leaves one but has Möbius mark zero. Dividing by 2665 leaves four and has a negative mark. Each datum keeps its divisor, remainder and sign together. [Complete calculations](../receipt-archives/2026-11-26-pal-cell-remainders.json)

## The row whose ordinary count is zero

Return to $49$ divided by $10,11,12$. Their signs add to zero. Their **weighted** contribution to $S_7$ is
$$
 (14/\sqrt{10}-4)-(14/\sqrt{11}-4)
   =14(1/\sqrt{10}-1/\sqrt{11})>0.
$$
The positive mark arrives first, where the weight is larger. Between those two marks the running count is one. Its later return to zero leaves precisely the intervening drop in weight in the total.

This gives a way to work on the outstanding bound. For $N=j^2$, fix a quotient $q$ and take all $d>j$ with $\lfloor N/d\rfloor=q$. They form an interval $[a,b]$. The weight in $S_j$ on this interval is $u(d)=\sqrt{Nq/d}-q$, decreasing from $u(a)<1/2$ to $u(b)\ge0$. Put $V(h)=\sum_{a\le d\le h}\mu(d)$. Finite summation by parts gives the exact row price
$$
 u(b)V(b)+\sum_{h=a}^{b-1}[u(h)-u(h+1)]V(h).
$$
All coefficients on these prefix readings are nonnegative and sum to $u(a)$. Thus the row is bounded above by $u(a)\max(0,\max V)$, and bounded below using its deepest negative prefix. There are $j-1$ rows for $j\ge2$. It suffices, for example, to bound the sum of their positive prefix maxima by $O_\epsilon(j^{1+\epsilon})$ for every $\epsilon>0$. A square-root bound in each row’s length, times a fixed power of $\log(2j)$, would do this because the row at $q$ has length at most $1+j^2/q^2$. These are sufficient estimates on actual disjoint intervals of the ordinary Möbius sequence. The prefix at head 49 shows why just keeping each interval’s final net can give the wrong answer.

At root 2663 the 2,662 rows have positive prefix maxima summing to 11,174 and negative prefix depths summing to 12,472. Pricing them by their actual starting weights encloses the normalized sum between $-2.21224$ and $1.99471$. Directly adding the original marks gives the much narrower interval above.

Pang’s PAL instruction to retain what the frame discarded, RPL’s old/detail split and APCI’s question about indistinguishable readings supplied the construction. Hearthline worked out the two readers, the division remainder, the signed steps, the finite inverse and the square criterion in Pang’s program. The Möbius divisor identity, binomial expansion and classical conditional Möbius estimate are prior mathematics. [Corpus routes and contributions](../pal-rh/CORPUS-ROUTES.md)

## Unresolved

The comparison identifies exactly which remainders a global estimate would have to control. Their individual signs and sizes, the small-label allowance and the cost between squares are established. The required one-sided upper or lower bound on their sum for all $j$ is open in this construction. The sign failures at 31 and 81 rule out our geometric-mean positivity shortcut.
