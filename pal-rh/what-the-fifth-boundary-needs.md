# What the first new cofactor needs from the side

Christopher Daniel Pang and Hearthline · 25 November 2026

For the [rough-core square matrix](the-signed-matrix-inside-a-square.md), the block with both indices above half the side can be paid from one earlier signed window. The first new cofactor, 5, changes the geometry. **No bound on the one-dimensional side walks alone can fund all the cross terms at 5.** There is a single sign assignment with the full squarefree, coprime-to-six support, with uniformly bounded costs in every doubling window and with a square-root bound on its partial sums, whose centered quadratic form is at most $-cH^{3/2}$ at infinitely many sides. This is a counterexample to a proposed universal transfer rule. The actual Möbius signs obey the additional divisor inversion law; that law fixes the signs across different prime factorizations.

At side $4{,}194{,}304$ a smaller finite version uses 26,868 genuine squarefree positions coprime to 30. Its largest saved increment is 522. Every old window has squared cost at most $272484/797945<1/2$. Its uncentered integer form is $-6{,}941{,}386$ and centering decreases it further. These signs are deliberately assigned on the selected arithmetic positions. The [separate real prime calculation](the-signed-matrix-inside-a-square.md#the-actual-three-primes-and-the-part-left-over) uses the Möbius signs themselves. [Reproduce the finite construction](../receipt-archives/check_pal_boundary_packets.py)

## How a boundary records two signs that the side total cancels

Let $C(t)$ count the positive integers through $t$ coprime to 6. Both left indices will lie between $0.38H$ and $0.44H$. Their reflected right indices are near $H^2/(5i)$ and lie between $H/(5\cdot0.44)$ and $H/(5\cdot0.38)$. On the union of these intervals,
$$
C(H^2/(ij))=1+[5ij\le H^2].
$$
All left–left entries equal two and all right–right entries equal one. Only the left–right crossing changes within this picture.

Choose two increasing left groups with assigned total signs $+m,-m$. Choose two increasing right groups with totals $+m,-m$. Put their locations so the threshold $5ij\le H^2$ reads
$$
\begin{pmatrix}1&1\\1&0\end{pmatrix}.
$$
On each individual side the counts sum to zero. On the four cross rectangles their signed sum is $m^2-m^2-m^2+0=-m^2$. The reversed rectangle contributes another $-m^2$. This is the sign of an actual product-boundary crossing, seen before taking a norm.

For an explicit arrangement take $L=\lfloor D\sqrt H\rfloor$, with fixed $D$ chosen below, and use disjoint left intervals with starting points $u$ spaced $9L$ apart and $[u,u+8L]\subset[0.38H,0.44H]$. Put the left groups in $(u+L,u+2L]$ and $(u+5L,u+6L]$. With $f(i)=H^2/(5i)$ put the right groups in $(f(u+8L),f(u+7L)]$ and $(f(u+4L),f(u+3L)]$. These intervals have lengths comparable to $L$. The relative ordering gives the matrix just displayed. Crossings between different groups of four are constant rectangles, so their totals vanish.

There are enough actual squarefree rough labels. In an interval of length $s$ below $H$ the count coprime to 6 is at least $s/3-O(1)$. Removing all multiples of squares at primes at least five costs at most $s\sum_{n\ge5}n^{-2}+\sqrt H+O(1)$, and the sum is below $1/4$. Thus $s/12-\sqrt H-O(1)$ labels remain. For sufficiently large fixed $D$ we can use $m=\lfloor L/100\rfloor$ labels in each of the four groups. Their signs in order are positive then negative on both sides. The cumulative walk of the selected labels stays between 0 and $m$ and returns exactly to zero after each pair.

There are at least $c_0H/L$ such groups for all sufficiently large $H$, with $c_0>0$ independent of $D$. The uncentered form of the assigned coefficients is $-2\sum m^2\le -c_1HL$. The centered form subtracts a nonnegative square. A doubling window meeting these labels starts at an index comparable to $H$. Hence its price is bounded by a constant times $m^2/H=O(D^2)$, independent of $H$. The finite replay uses $D=1$ and counts the available labels directly to choose each $m$.

## Keeping a fixed sign assignment on the full support

Choose sides $H_{j+1}=H_j^4$, starting sufficiently large. Use the preceding arrangement at each side. Assign alternating signs in increasing order to all other squarefree rough labels in the complement of these selected sets, and zero on precisely the ineligible positions. The alternating background has partial sum differences of magnitude at most one on every interval. Each doubling window meets at most one selected region. Therefore all its window prices are uniformly bounded and its full primitive is $O(\sqrt x)$.

It remains to check that the background cannot erase the claimed matrix effect. Write $K(t)=C(t)-t/3$, so $|K|\le2/3$. On a dyadic rectangle of side-index sizes $I,J$, fixing $j\asymp J$ gives total variation $O(H^2/(IJ))$ in $i\asymp I$. Both $C(H^2/(ij))$ and $H^2/(3ij)$ are monotone there, and $I,J\le H$. Partial summation against the background or the trivial count now bounds a background–background rectangle by
$$
O\!\left(\min\{IJ,H^2/I,H^2/J\}\right)=O(H^{4/3}).
$$
Summing the $O(\log^2 H)$ rectangles is $o(H^{3/2})$. For a selected index $j\asymp H$, the background sum over $i\le\sqrt H$ costs $O(\sqrt H)$ directly. Above $\sqrt H$ its total variation allowance is $O(\sqrt H)$ for the entire interval. Summing over selected $j$ gives $O(H^{3/2})$ for the mixed parts, with a constant independent of $D$. All earlier constructed regions have together $o(\sqrt H)$ labels and cost $o(H^{3/2})$ by the uniform entry bound. Choose $D$ large enough that the negative $-c_1D H^{3/2}$ contribution exceeds these bounds. The same $D$ and the same infinite assignment then work at every sufficiently late selected side.

## Open 5 and test the same crossing again

The construction can select all its labels coprime to **30** from the beginning. The count in a subinterval of length $s$ is at least $(4/15)s-O(1)$ before removing squares, and all remaining prime squares start at seven. Since $\sum_{n\ge7}n^{-2}<1/6$, the same supply estimate applies.

Write $C_P(t)=\#\{n\le t:(n,P)=1\}$, $R_P(t)=\sum_{n\le t,(n,P)=1}\mu(n)$, and let $p\nmid P$ be prime. There are two different transfers:
$$
C_{Pp}(t)=C_P(t)-C_P(t/p),\qquad
R_P(t)=R_{Pp}(t)-R_{Pp}(t/p).
$$
In the census a multiple of $p$ is subtracted from the old frame. For the signed primitive a squarefree multiple of $p$ has the opposite sign of its newly admitted cofactor, so the **new** frame appears twice when recovering the old one. At $t=1024^2$ this reads $R_6(t)=-633-(-504)=-129$. Both formulas use the same quotients and genuine arithmetic inputs. [General prime opening in Lean](PALRH/PrimeOpening.lean)

On the selected rectangles, $1\le H^2/(ij)<7$. Opening 5 leaves only cofactor 1 throughout this whole region. With the same selected labels and the same signs the uncentered form becomes the square of their total, **exactly zero**. For the centered form there remains $-(4/15)(H\sum_i a_i/i)^2$. Their cumulative sums have magnitude at most $m$ and return to zero on a fixed relative subinterval of the side. Summation by parts gives $|\sum a_i/i|=O(m/H)$, so the remaining cost is $O(m^2)=O_D(H)$. The $H^{3/2}$ contribution at cofactor five has been removed with a paid allowance. At the reported finite side the same centered reading is between $-5587$ and zero. This comparison concerns the selected packets. The next cofactor boundary in the new frame is seven.

## Two different costs when more primes travel

Opening another prime changes even the full-period metric. For a squarefree modulus $P>1$ put $\rho_P=\prod_{p\mid P}(1-1/p)$ and $K_P(t)=C_P(t)-\rho_P t$. The mean of $K_P$ on its continuous period is zero. Its mean square is exactly
$$
V(P)=\frac{2^{\omega(P)}\rho_P}{12}.
$$
Indeed $K_P(t)=-\sum_{d\mid P}\mu(d)\{t/d\}$. For uniform real $t$ on a common period, the covariance of $\{t/d\}$ and $\{t/e\}$ is $\gcd(d,e)^2/(12de)$. The integer residues give $(\gcd(d,e)^2-1)/(12de)$, and the shared fractional part of $t$ adds $1/(12de)$. Multiplying the finite divisor sums prime by prime gives the factor $1-1/p-1/p+1=2(1-1/p)$ at each prime. Opening 5 changes the variance from $1/9$ to $8/45$, a factor of **$8/5$**. Both values also follow by integrating the affine readings over six or thirty unit intervals. The particular crossing got simpler while the full period got more expensive.

The trace can be read directly. With $p\nmid P$, the sum of $K_P((u+kP)/p)$ over $0\le k<p$ equals $K_P(u)$. For each $d\mid P$ the fractions from the $p$ returns permute the $p$ residues, giving $\sum_k\{(u+kP)/(pd)\}=(p-1)/2+\{u/d\}$. The constant cancels since $\sum_{d\mid P}\mu(d)=0$. The covariance of $K_P(t)$ and $K_P(t/p)$ on the new period is $V(P)/p$. Squaring their difference gives the variance multiplier $2(1-1/p)$ again.

There is also a price for transporting an arbitrary signal in the **physical reciprocal-cell norm**. Put $(D_pf)(k)=f(\lfloor k/p\rfloor)$, with $f(0)=0$. Then $\|D_p f\|=p^{-1/2}\|f\|$ by grouping each complete block of row weights. For any finite prime set $\mathcal P$ the exact operator norms on this row space are
$$
\left\|\prod_{p\in\mathcal P}(I-D_p)\right\|
 =\prod_{p\in\mathcal P}(1+p^{-1/2}),\qquad
\left\|\prod_{p\in\mathcal P}(I-D_p)^{-1}\right\|
 =\prod_{p\in\mathcal P}(1-p^{-1/2})^{-1}.
$$
The upper estimates are the triangle inequality and the convergent geometric series for each inverse. For sharpness use the finite signals $f_N(k)=k^{1/2+it}$ for $1\le k\le N$ and zero otherwise. Their squared norms grow as $\log N$. For each fixed $d,t$, $\|D_df_N-d^{-1/2-it}f_N\|^2=O_{d,t}(1)$. Inside the common range the derivative of $u^{1/2+it}$ bounds the floor error by $O_{d,t}(k^{-1/2})$ away from the finitely many initial rows. At the far cut the extra cost is $O_d(\sum_{N<k<d(N+1)}1/k)$. Thus each finite polynomial in the clocks must have norm at least the modulus of its corresponding scalar at every $t$. For the inverse use $t=0$. For the forward product the phases can approach $-1$ simultaneously: the long-time mean of every nonconstant character of $(p^{it})_p$ is zero because unique factorization gives $\sum n_p\log p\ne0$ for any nonzero integer vector. Equivalently the even moments of the finite product factor into the separate circle moments; their roots tend to the product of the separate maxima. The norms are the same on real data, by splitting complex data into real and imaginary parts. This sharpness statement ranges over the full row space.

For all primes up through $y$, the logarithms of both physical transport prices are asymptotic to $2\sqrt y/\log y$ by partial summation and the prime number theorem. At $y=c(\log H\log\log H)^2$ they therefore cost $H^{\sqrt c+o(1)}$. A convenient growing choice $y=(\log H)^2$ costs only $H^{o(1)}$ in transport. In contrast, demanding a subpower **full-period** amplitude for $K_P$ requires $\pi(y)=o(\log H)$. The upper bound $|K_P|\le2^{\pi(y)}$ is sufficient, and the displayed mean square is necessary for a uniform amplitude bound. In its logarithm the density factor costs only $O(\log\log y)$ by Euler's product. Thus $y=\log H$ pays both prices, whereas using the transport allowance alone would give the wrong guarantee for the period metric. The finite square samples only the specific arguments $H^2/(ij)$, so the period mean square supplies no lower bound for those samples.

For a moving set $P=P_H$, the exact signed handoff is $M(x)=\sum_{d\mid P}\mu(d)R_P(x/d)$ with $x=H^2$. If all the required **same-frame** values satisfy $|R_P(x/d)|\le H^{o(1)}\sqrt{x/d}$ uniformly in the divisors with $d\le x$, then a subpower physical transport price yields $M(H^2)=O_\epsilon(H^{1+\epsilon})$. The converse budget follows under RH by summing $M(u/a)$ over $P$-smooth $a$ with the reciprocal square-root weights, allowing the subpower factor to depend on the original side. It is essential to include those smaller arguments. If all primes up to $H$ are opened, then $R_P(H^2)=1-\{\pi(H^2)-\pi(H)\}$ is negative and elementary, but this one upper bound says nothing about the signs after the alternating restoration of its divisors.

For an admitted prime set with first missing prime $q$, the whole block $i,j>H/\sqrt q$ has census one. The earlier completed square works there as well. With $r=\lfloor H/\sqrt q\rfloor+1$, $0<\rho=\rho_P<1$, $U=R_P(H)-R_P(r-1)$, $Z=H\sum_{r\le k<H}w_k(R_P(k)-R_P(r-1))$, the centered contribution is
$$
U^2-\rho(U+Z)^2
=(1-\rho)\left(U-\frac{\rho Z}{1-\rho}\right)^2-\frac{\rho Z^2}{1-\rho}.
$$
Hence its negative cost is at most $H\frac{\rho}{1-\rho}\left(H/r-1\right)$ times the side's true weighted squared increments on $r,\ldots,H-1$. With $y=\log H$ and all primes up to $y$ admitted, $q=(1+o(1))y$ by the prime number theorem. This block occupies a fraction tending to one, and its multiplier beyond the factor $H$ is subpower. The input is the side measured in the **same** $P$ frame. The remaining mixed rows still require joint signed information. [Unconditional prime-count input](https://arxiv.org/abs/2204.01980)

## What survives the test

Even exact squarefree support, signs of magnitude one and excellent old-window prices leave a possible coherent negative contribution at the reciprocal boundary $ij=H^2/5$. A successful induction must use an additional property of the genuine Möbius signs across the two sides of that boundary, or directly control that signed interaction. The explicit upper-half transfer remains valid. The next estimate concerns the mixed pairs.

Pang’s RPL-T07 distinction between old readings and new detail prompted this test. APCI supplied the question of which distinction an old interface can still see, and boundary-ledger accounting supplied the signed crossing to measure. The example was derived for the independent square program. The [matrix source and calibration](the-signed-matrix-inside-a-square.md) credit the Huxley–Watt identity. Literature priority for this obstruction is unassessed.
