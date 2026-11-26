# Can prime phases approximate one?

[Active construction key](CONSTRUCTION-KEY.md) · [Current results](MAP.md) · [Sharp odd-row displacement](half-tick-reflection.md) · [Fresh-prime law](fresh-prime-transfer.md) · [Every finite fit can improve](every-fit-has-a-successor.md)

Christopher Daniel Pang and Hearthline, 25 November 2026. Pang’s PAL atlas asks what a measurement retains when it passes from one representation to another. Here the inputs are integer residues, the geometry is a circle, and the measurement is a weighted squared distance. The Alpöge–Claude release supplies the comparison target and toolchain pin. The mathematical derivation on this branch uses stock Mathlib and the sources identified below. [PAL Mathematical Realization Atlas](../corpus/PAL_v2.4-M_Mathematical_Realization_Atlas.docx) · [APCI](../corpus/APCI_Declared_Interface_v1.0.0.docx)

[Averaging, the whole-square estimate and exact backward differences](averaging-the-square.md) · [Read the current square calculation](the-signed-matrix-inside-a-square.md) · [Absolute prime-depth allowance](where-prime-depth-can-stop.md) · [First new cofactor](what-the-fifth-boundary-needs.md)

[What the signed rows leave at zero](../proofs/what-the-signed-factorial-rows-leave-at-zero.md) · [Endpoint calculation](the-boundary-of-the-signed-factorial-rows.md) · [Four signed factorial phases](counting-the-four-quarters-of-a-factorial.md) · [Finite reconstruction](PALRH/FactorialReturn.lean)

[How the prime board stores its records](../proofs/how-much-room-the-prime-board-needs.md) · [Board area and one-sided implication](the-prime-board-and-its-signed-area.md) · [Two-sided natural-number reduction](PALRH/PrimeBoard.lean)

[A pair of observers and the primes within one doubling](../proofs/what-one-doubling-hears-in-the-primes.md) · [The exact diagonal and prime-only inequality](the-dyson-response-and-prime-squares.md) · [Analytic stock-target reduction](PALRH/DysonOctave.lean)

[The possible local jumps](../proofs/what-can-move-inside-a-square-root-window.md) · [Density and location of the remaining marks](the-background-around-one-large-mark.md) · [Finite square-contact implications](PALRH/SquareExposure.lean)

[How far a square mark must reach](../proofs/how-far-a-square-mark-must-reach.md) · [Why the signed allowance scales with the recovery price](which-window-pays-for-the-return.md) · [Formal adaptive test](PALRH/TrailingRows.lean)

[The same integer readings, two different arithmetic outcomes](../proofs/what-a-quotient-leaves-between-integers.md) · [Finite divisor collapse and stable recovery](PALRH/CellRemainder.lean)

[What the newest half can gain](../proofs/how-much-can-the-newest-half-gain.md) · [Finite rectangle and recovery of stock RH from an upper bound](PALRH/TerminalWindows.lean)

[Why exactly two rough roots may remain](../proofs/why-the-last-two-square-roots-remain.md) · [How much each signed portion carries](what-the-last-two-square-roots-carry.md) · [Square pass and inverse](PALRH/DenseSquares.lean)

[The running integer at 44](../proofs/the-integer-that-turns-at-forty-four.md) · [Why a rare direction suffices](how-many-rising-steps-would-a-zero-force.md) · [The negative physical contribution](where-the-negative-running-mass-comes-from.md)

[One physical primitive per fourth power](../proofs/one-quantity-at-each-fourth-power.md) · [Predicting the next head](what-two-neighboring-blocks-predict.md) · [Fixed Mathlib challenge](checks/one-head/OneHeadChallenge.lean)

[Which signed references can pay](../proofs/what-a-positive-reference-must-lose.md) · [Finite inverse and RH transfer](PALRH/ReferencePrice.lean)

[The full stream on two prime supports](../proofs/two-prime-families-carry-the-full-price.md) · [Why one large prime leaves nine](../proofs/why-one-large-prime-leaves-nine.md) · [The integer sign rule](../proofs/where-an-integer-label-can-go-quiet.md)

[The 2663 cofactor experiment](what-2663-carries-between-frames.md) · [Five moments on actual marks](../proofs/which-prime-labels-cancel.md) · [A prime with a growing cofactor](how-much-can-travel-with-a-prime.md)

[Reflected remainder cells](what-a-reflected-remainder-carries.md) · [What both clocks must do together](how-far-a-negative-run-must-travel.md) · [One pass at the fourth powers](what-the-first-omitted-label-sees.md#one-rational-sign-at-each-fourth-power-suffices) · [How many square passes the sign needs](how-many-square-passes-the-sign-needs.md) · [What the ordinary primes still owe](what-the-ordinary-primes-still-owe.md) · [What the two signs cost together](what-the-two-signs-cost-together.md) · [What the last two rows carry](what-the-last-two-rows-carry.md) · [One list builds the next square](the-balanced-newton-handoff.md) · [Why infinitely many finite error drops would imply RH](when-a-drop-would-count.md)

[Signed window costs and the growth exponent](what-the-next-octave-costs.md) · [What 5 carries through 2 and 3](what-five-carries.md) · [Keeping a finite head when wider scales are available](PALRH/Protected.lean)

[What a single finite frame always misses](what-one-parent-misses.md) · [The price of changing an early row](changing-the-first-wrong-row.md)

## Where the sixth turn went

Draw the point $e^{2\pi i k/d}$ on a circle. Its counterclockwise turn from 1, measured in turns in $[0,1)$, is $b_d(k)=(k\bmod d)/d$. Each full revolution is represented exactly by one turn. For $d=2,3$ one has $1/2-1/3=1/6$, hence

$$
b_6(k)=b_2(k)-b_3(k)+\mathbf1_{\{b_2(k)<b_3(k)\}}.
$$

The last term records the crossing of zero on the circle. At $k=5$, the half-turn minus the two-thirds turn is $-1/6$. It lands at $5/6$. The carry is one. More generally, if $m,n$ are coprime and $un+vm=1$, taking fractional parts gives $b_{mn}(k)=\{u b_m(k)+v b_n(k)\}$. Applying this successively constructs the turn at every squarefree modulus from its prime phases. This is ordinary Bézout arithmetic.

A linear combination of prime readings has a limitation that joint phase measurements escape. Write
$$
D(f)=-2f(1)+f(3)+f(5)-f(6).
$$
Substitution for $d=2,3,4,5,6$ and the equality $k\bmod d=k$ for $d>6$ give $D(b_d)=[d=6]$. Meanwhile $D(1)=-1$. Thus every linear combination omitting modulus 6 has $D=0$, even if it uses every other modulus in the limit. Adding the wrap term above is enough to supply the missing reading.

Give row $k\ge1$ the weight $w_k=1/[k(k+1)]$. These weights sum to one. For $F=\sum a_db_d$ put $E(F)=\sum_{k\ge1}w_k|1-F(k)|^2$. If $a_6=0$, weighted Cauchy–Schwarz gives
$$
1=|D(1-F)|^2
 \le \big(4\cdot2+12+30+42\big)E(F)=92E(F).
$$
The same calculation gives $|a_6+1|^2\le92E(F)$ for all finite sums. It explains exactly what the coefficient of the missing joint reading must approach.

**An explicit construction crosses that barrier.** With 61 squarefree moduli through 101 and coefficients in hundredths, integer arithmetic gives
$$
E(F)\le
\frac{193763581491313249}{18446744073709551616}+
\frac{1656369}{10000002500}<\frac1{92}.
$$
The first fraction bounds the first four million rows, with rounding directed upward. The second bounds every remaining row. The coefficients, a second direct check of the first 202 rows, and the replay command are in the [arithmetic receipt](../receipt-archives/check_pal_residue_distance.py).

## The single obligation

Can finite rational combinations drive $E$ arbitrarily close to zero? For an entirely finite statement, require that for every integer $K\ge1$ there exist a finite family $a_d\in\mathbb Q$ at moduli $d\ge2$ and an integer $M\ge1$ with
$$
\sum_{k=1}^{M}\frac{|1-\sum_d a_db_d(k)|^2}{k(k+1)}
+\frac{(1+\sum_d|a_d|)^2}{M+1}<\frac1K. \tag{1}
$$
Every entry in (1) is rational. The second term bounds the tail because $0\le b_d(k)<1$ and $\sum_{k>M}w_k=1/(M+1)$. Conversely, if finite combinations approximate 1 in the weighted norm, take their real parts, approximate their finitely many coefficients by rationals, then increase $M$ with those coefficients held fixed. The bound $\|b_d\|_2\le1$ controls rational rounding. This proves the equivalence of (1) with the Hilbert-space approximation condition stated in the Lean source. The displayed numerical witness settles $K=92$. In Lean, `rh_of_finite_certificates` accepts this all-rational statement directly, with the positive tolerance indexed by $K+1$ for natural $K$. The existence of witnesses for all $K$ is open in this construction.

## What exact agreement on a finite prefix leaves behind

There is an unconditional way to fit every row before $N$, for any $N\ge2$. Set $a_d=-\mu(d)$ for $2\le d<N$ and set $a_N=N\sum_{d<N}\mu(d)/d$, where the last sum starts at $d=1$. These choices give $\sum a_d/d=1$. Expanding $b_d(k)=k/d-\lfloor k/d\rfloor$ and using $\sum_{d\le k}\mu(d)\lfloor k/d\rfloor=1$ gives the exact residual
$$
1-F(k)=a_N\lfloor k/N\rfloor+\sum_{N\le d\le k}\mu(d)\lfloor k/d\rfloor .
$$
The divisor identity follows by summing $\sum_{d\mid m}\mu(d)=[m=1]$ for $1\le m\le k$. Thus the residual vanishes for $k<N$. On the entire next block $N\le k<2N$ it is exactly $a_N+\sum_{d=N}^k\mu(d)$. For example, at $N=6$ the first five rows agree perfectly and the sixth has error $4/5$. This calculation identifies the signed arithmetic fluctuations any bound for this particular construction has to handle. It supplies no estimate on later blocks.

## Why the obligation reaches RH

Identify row $k$ with the interval $(1/(k+1),1/k]$, of length $w_k$. On it, writing $\rho_d(x)=\{1/(dx)\}$, one has $b_d=\rho_d-\rho_1/d$. For $x>1$ this difference vanishes. The Mellin transform on the positive real half-line therefore gives
$$
s\int_0^1 b_d(x)x^{s-1}\,dx=(d^{-1}-d^{-s})\zeta(s)
 \qquad(\Re s>0,\ s\ne1).
$$
For $\Re s>1$, use $b_d(x)=\lfloor1/x\rfloor/d-\lfloor1/(dx)\rfloor$. Integrating $\lfloor1/x\rfloor=\sum_{m\ge1}\mathbf1_{(0,1/m]}$ term by term gives $\zeta(s)/s$. Scaling $x$ gives the second term. The balanced function is bounded and supported on $(0,1]$ when restricted to positive $x$, so its Mellin integral is holomorphic for $\Re s>0$ by domination on compact subsets. Multiplication by $s-1$ removes the pole on the right, giving the identity by analytic continuation.

Suppose $\zeta(s)=0$, $\sigma=\Re s>1/2$, $s\ne1$. Every finite combination then has Mellin reading zero, while the target's reading is $1/s$. Cauchy–Schwarz yields
$$
\frac1{|s|^2}\le E(F)\int_0^1 x^{2\sigma-2}dx
=\frac{E(F)}{2\sigma-1}.
$$
A sequence with $E(F)\to0$ excludes that zero. The completed-zeta functional equation reflects any nontrivial zero on the other side of the line into this region. This proves the conditional implication to Mathlib’s actual statement. The [cell calculation](PALRH/Cells.lean) proves the cutoff estimate in (1). The [Lean source](PALRH.lean) constructs the continuous Mellin functional and uses the kernel of that functional to express the same obstruction. The published reverse implication is due to the Nyman–Beurling and Báez-Duarte criteria. [Báez-Duarte, Theorem 1.1 and its proof](https://arxiv.org/pdf/math/0202141)

## Precisely which moduli matter

Given a set $S$ of permitted moduli at least two, the distance to the constant can tend to zero using $S$ **if and only if RH holds and $S$ contains every squarefree integer at least two**.

For necessity, set $f(0)=0$ and $J_h(f)=f(h-1)+f(1)-f(h)$. Then $J_1=0$. A wrap at a multiple gives $J_h(b_j)=[j\mid h]$ for $j\ge2$. With the Möbius function $\mu$, define the finite reading
$$
D_d(f)=\sum_{h\mid d}\mu(d/h)J_h(f).
$$
For $d\ge2$, Möbius inversion gives $D_d(b_j)=[d=j]$ and $D_d(1)=-\mu(d)$. Any fixed finite coordinate reading is continuous in this norm. Thus every approximation forces its coefficient $a_d$ to tend to $-\mu(d)$. Omitting a squarefree $d$ costs a positive distance. The four-row test above is $D_6$. The general coefficient detector is Vasyunin’s biorthogonal system in these coordinates. [Vasyunin, 1995](https://www.mathnet.ru/eng/aa557) · [Balazard, §2 and equations (7)–(9)](https://arxiv.org/pdf/1812.04309)

For sufficiency, under RH Báez-Duarte’s proof approximates $\chi=\mathbf1_{(0,1]}$ in $L^2(0,\infty)$ by finite weighted sums $g=\sum c_d\rho_d$ supported on squarefree $d$, including 1, since $c_d$ is a scalar multiple of $\mu(d)$. On $x>1$, $g(x)=A/x$ with $A=\sum c_d/d$, so $|A|=\|g\|_{L^2(1,\infty)}\le\|g-\chi\|_2$. Subtract $A\rho_1$. The result is $\sum_{d\ge2}c_db_d$, and its distance to $\chi$ is at most $(1+\|\rho_1\|_2)\|g-\chi\|_2$. Here $\rho_1$ is bounded on $(0,1]$ and equals $1/x$ beyond 1. The corrected approximants still converge. This sufficiency proof uses RH at its stated entrance. It gives a choice of moduli for the unconditional search. [Báez-Duarte, equations (2.3)–(2.9)](https://arxiv.org/pdf/math/0202141)

## One exact appearance of π in the residual

If $L$ is a common multiple of a finite family's moduli, every reading vanishes at $L,2L,3L,\ldots$. Those rows alone contribute
$$
E(F)\ \ge\ \sum_{j\ge1}\frac1{jL(jL+1)}
\ \ge\ \frac{\pi^2}{6L(L+1)}.
$$
Indeed $jL+1\le j(L+1)$ and $\sum_{j\ge1}j^{-2}=\pi^2/6$. The bound decreases as $L$ grows. It locates a residual for **each** finite family. Whether one can make the **total** residual arbitrarily small is the outstanding question.

## What doubling misses

Pang asked what to do with the carry. With $b_1=0$, the binary carry at scale $d\ge1$ is
$$
C_d(k)=2b_{2d}(k)-b_d(k)=\lfloor k/d\rfloor\bmod 2 .
$$
Across blocks of $d$ rows starting at zero, $C_d-C_{2d}$ repeats $0,1,-1,0$. Its squared size is one on rows $(4j+1)d$ through $(4j+3)d-1$. Summing their lengths gives
$$
\|C_d-C_{2d}\|_2^2
=\frac1d\sum_{j\ge0}\left(\frac1{4j+1}-\frac1{4j+3}\right)=\frac{\pi}{4d}.
$$
The series is the integral of $1/(1+x^2)$ from 0 to 1. The remainder after integrating the first $2n$ terms of its geometric expansion has absolute value at most $1/(4n+1)$.

**Every linear combination of binary carries, at arbitrary scales, has squared error at least $1/(1+(2\pi/\log 2)^2)>1/92$.** To see what they all miss, set $s=1+2\pi i/\log2$. The wave $x^{s-1}$ makes one complete turn when $x$ doubles. Its absolute value is one, so its integral against a function on $(0,1]$ is a continuous measurement of norm one. The constant target has reading $1/s$.

Use the reciprocal cells defined above. Since $C_1$ is one at the odd rows, multiplying its reading by $s$ gives the paired alternating sum of $n^{-s}$. At this $s$, $2^{1-s}=1$. For each $N$ its first $2N$ terms sum to $\sum_{n=N+1}^{2N}n^{-s}$. The integral of $x^{-s}$ from $N$ to $2N$ is zero. The sum differs from that integral by at most $\int_N^{2N}|s|x^{-2}dx$, which tends to zero. Thus $C_1$ has reading zero. Scaling $x$ by $d$ multiplies the reading by $d^{-s}$, so every $C_d$ has reading zero as well. Cauchy–Schwarz gives the stated floor $|1/s|^2$. For the strict comparison use $\pi<22/7$ and $\log 2>2/3$, the latter from the midpoint bound for the integral of $1/x$ on $[1,2]$. This argument also shows the cancellation at the exceptional frequency in the classical alternating zeta formula. [DLMF, equation 25.2.3](https://dlmf.nist.gov/25.2.E3)

**Tripling registers this particular wave.** The rational witness above has squared error below $1/92$, so at least one of its $b_d$ has nonzero reading. The Mellin identity above then gives $\zeta(s)\ne0$ at this one frequency. The reading of $3b_3-b_1$ is $(1-3^{1-s})\zeta(s)/s$, which is nonzero because $1<\log3/\log2<2$. This settles the comparison for one wave. Uniform control of the full error after combining scales remains open.

## Unresolved

Give an unconditional construction satisfying (1) for arbitrary $K$, or establish an obstruction valid for every permitted family that survives as its moduli grow. A finite interval of exact readings, or any finite list of certificates, leaves this quantifier open.
