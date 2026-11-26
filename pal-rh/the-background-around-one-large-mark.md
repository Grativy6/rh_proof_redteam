# The background around one large mark

Christopher Daniel Pang and Hearthline, 26 November 2026 (New York). The [integer packing proof](../proofs/what-can-move-inside-a-square-root-window.md) bounds all variation between consecutive squares and gives the fixed stock-RH implications. Here we determine the unsigned local profile more precisely and identify what can be said about signs.

Put $a(v^2d)=v\mu(d)$ for $v=2^i3^j$ and $(d,6)=1$, with zero weight on all other labels. An occupied $d$ is squarefree. Fix $C>0$ and let $I$ vary over half-open intervals inside $[X-C\sqrt X,X+C\sqrt X]$. All estimates below are uniform for such $I$. Write $H=|I|$ and $\kappa=9/\pi^2$.

## Count the regular part first

Split at $V=(\log X)^2$ and $W=X^{7/16}$. For $v\le V$, we want the number of squarefree rough integers in the interval $I/v^2$. Exclude the two primes 2 and 3 and all squares $p^2$ for $5\le p\le P=\log X$. Inclusion–exclusion gives
$$
 \frac{H}{3v^2}\prod_{5\le p\le P}(1-p^{-2})+O(2^{\pi(P)}).
$$
The constant allows for the multiples of 2 and 3. For each larger prime whose square could divide a cofactor there are at most $H/(v^2p^2)+1$ excluded positions. Accordingly the change upon passing to all primes is bounded by $O(H/(v^2P)+\pi(\sqrt{X+C\sqrt X}/v))$.

Multiply by $v$ and sum through $V$. The elementary prime bound $\pi(z)\ll z/\log(2z)$, the $O((1+\log V)^2)$ smooth roots and $\sum_{v\le V}v\ll V\log(2V)$ give total error
$$
 O_C\!\left(\sqrt X\,\frac{(\log\log X)^2}{\log X}\right)=:O_C(E_X).
$$
In particular $2^{\pi(P)}=X^{o(1)}$. The density for a single cofactor is $\kappa/3$. The sum $\sum_v1/v=3$ turns it into $\kappa$ for the weighted physical marks. Extending the main term past $V$ costs $O(H\log(2V)/V)$ by summing dyadically.

For $V<v\le W$ the entire unsigned weight is at most $H\sum_{v>V}1/v+\sum_{v\le W}v\ll H\log(2V)/V+W\log(2W)$, also inside $O_C(E_X)$. Thus
$$
 \sum_{n\in I}|a(n)|=\kappa H+
 \sum_{\substack{n\in I\\ |a(n)|>X^{7/16}}}|a(n)|+O_C(E_X).
$$
The common-square spacing proof leaves at most three labels in the exceptional sum, even before imposing a logarithmic separation theorem. This argument uses the actual ordinary squarefree cofactors and elementary sieving. [Euler product](https://dlmf.nist.gov/25.2) · [Zeta values](https://dlmf.nist.gov/25.6)

## Why a second macroscopic mark cannot stay nearby

Suppose that two distinct occupied labels $v^2d,w^2e$ in the entire neighborhood both have weight at least $\sqrt X/\log X$. Then $d,e=O((\log X)^2)$. Write $v=2^i3^j$, $w=2^k3^l$. The nonzero real number
$$
 \Lambda=2(i-k)\log2+2(j-l)\log3+\log(d/e)
 =\log(v^2d/(w^2e))
$$
has size $O_C(X^{-1/2})$. In Matveev’s Corollary 2.3 the number field here is $\mathbb Q$. The first two logarithmic heights are constant, the third is $O(1+\log\log X)$, and the integer coefficients have size $O(\log X)$. His lower bound therefore gives $\log|\Lambda|\ge-O((1+\log\log X)^2)$, contradicting the upper bound for large $X$. A zero coefficient or a unit logarithm can be dropped, and the nonzero form still has the asserted bound. This is the only input needed to go from a bounded number of large labels to a single macroscopic one. [Matveev, §2, Corollary 2.3](https://doi.org/10.1070/IM2000v064n06ABEH000314)

Choose a largest label $n_X$ in the whole neighborhood. Each of the other large labels now costs $O(\sqrt X/\log X)$, while any mark under the cutoff costs at most $X^{7/16}$. Hence
$$
 \sum_{n\in I}|a(n)|=\kappa H+|a(n_X)|\mathbf1_{n_X\in I}+O_C(E_X).
$$
It follows, for signed readings, that
$$
 \left|\sum_{n\in I}a(n)-a(n_X)\mathbf1_{n_X\in I}\right|
 \le\kappa H+O_C(E_X).
$$
In particular, across a window of length $o(\sqrt X)$, any nonvanishing jump after scaling by $1/\sqrt X$ must come from one original mark. Its signed height is $\mu(d)/\sqrt d+o(1)$ for its own cofactor. At widths comparable to $\sqrt X$ the other labels retain a signed total that this inequality alone need not settle.

Equivalently, zoom horizontally and vertically by $\sqrt X$. The possible unsigned local limits are a uniform density $\kappa$ and, optionally, one atom of size $1/\sqrt d$ at a freely chosen local position, for squarefree $d$ coprime to six. To place such an atom, recenter a distance $z\sqrt{v^2d}+O(1)$ from $v^2d$ and send a smooth $v$ to infinity. A bounded normalized cofactor can be made constant along a subsequence, and all unbounded cofactors have vanishing individual height. There cannot be two surviving locations, since any fixed pair lies in one bounded neighborhood. To obtain just the uniform background, avoid neighborhoods of labels with $d\le\log X$. There are $O(\log^2 X)$ such labels in $[X/2,3X]$, by counting smooth roots for each $d$. Even neighborhoods of radius $\sqrt X\log X$ around all of them cover $o(X)$ prospective centers in $[X,2X]$.

## An observer fixed to a square ray

Fix a squarefree $d_0$ coprime to six. Center instead at the prescribed positions $X=d_0 j^2$, with *arbitrary* positive integer $j$. Within $O(j^{1-\epsilon})$ of that center, a macroscopic mark could only come from the center itself.

Indeed a competing cofactor $d$ with weight $\gg j$ is bounded. Passing to a subsequence fixes it. The proximity of $v^2d$ implies
$$
 \left|\sqrt{d/d_0}-j/v\right|\ll v^{-1-\epsilon}.
$$
For $d\ne d_0$ the square root is algebraic irrational. The denominator of $j/v$, after reduction, has only the primes 2 and 3. Ridout’s restricted-denominator approximation theorem excludes infinitely many such rational approximations. If $d=d_0$, neighboring distinct integer squares are separated by order $j$, so $v=j$ is necessary. Thus on that scale the only possible surviving signed atom is $\mu(d_0)j$ exactly at the center, and it exists exactly when $j$ is smooth. The elementary packing theorem for the RH criterion is independent of this use of Ridout. [Ridout, *Rational approximations to algebraic numbers*](https://doi.org/10.1112/S0025579300001182)

## How much of the background is signed?

For almost all centers the signed square-root window is $o(\sqrt X)$ in the density sense. Here is how this conclusion reaches the *integer square shells* in our fixed test. The finite weights at each fixed smooth $v$ are a dilation of $m(d)=\mu(d)\mathbf1_{(d,6)=1}$. This real multiplicative function has absolute value at most one and mean zero. Its mean follows from the ordinary prime number theorem and $m=\mu*\mathbf1_{\rm smooth}$, truncating the convergent $\sum_{s\ {\rm smooth}}1/s$. Matomäki and Radziwiłł’s Theorem 1 gives cancellation in almost all short intervals for this $m$. Averaging over $x\in[T,4T]$ for any fixed positive multiple $H$ of $\sqrt T$, the finitely many $v\le V_0$ therefore contribute $o_{V_0}(H)$ in mean absolute value. The rest contribute $O(H\sum_{v>V_0}1/v)$ in that mean by counting how many starting points can contain each physical mark. Let $V_0$ increase after $T$. [Matomäki and Radziwiłł, *Multiplicative functions in short intervals*, Theorem 1](https://arxiv.org/pdf/1501.04585)

Consequently, for every $\delta>0$, among $J\le j\le2J$ only $o_\delta(J)$ satisfy
$$
 \max_{j^2\le n<(j+1)^2}|M(n)-M(j^2)|>\delta j .
$$
For the transfer, first exclude extended square neighborhoods containing a mark larger than $\eta J$. For fixed $\eta>0$ there are only $O_\eta(\log J)$ such marks, since their cofactors are bounded and their smooth roots lie in fixed-ratio ranges. Each mark affects $O(1)$ adjacent square shells. In the other shells the unsigned bound above permits moving either endpoint by at most $\eta J$ at cost $O(\eta J)+o(J)$. Round the prefix length to one of finitely many multiples of $\eta J$, and slide its starting point from $j^2$ through $j^2+[0,\eta J]$. With $\eta$ small relative to $\delta$, every bad square shell supplies an interval of ordinary starts, of length $\eta J$, with a large signed sum at one of these fixed lengths. Those starting intervals are disjoint. A positive proportion of bad squares would contradict the mean absolute estimate on ordinary starts. This proves a density statement about *changes within shells*. The cumulative values at the selected contacts still need control.

In the 9,000 consecutive root shells from 1,000 through 9,999, 217 have a signed excursion from the initial square exceeding a quarter of the root. After removing the largest individual mark after that initial head, four do. At root 335 the first and last readings agree, yet an interior reading differs by 80. [Consecutive-shell calculation](../receipt-archives/2026-11-26-pal-square-exposure.json)

For comparison there is a uniform signed estimate on longer windows. Matomäki, Pandey, Pliego, Teräväinen and Wang’s Theorem 1.4 gives an ordinary Möbius bound of order $H/(\log X)^{1/3-\epsilon}$ for $X^{19/35+\epsilon}\le H\le X$. The same estimate, with constants depending on $\epsilon$, carries to $a$ since $a=b*\mu$, with nonnegative $b(q)\ll\sqrt q$ on smooth $q$. Up to $q=(\log X)^4$ apply the cited estimate to the scaled window with a slightly smaller exponent margin. The weighted costs sum using $\sum_q b(q)/q<\infty$. Beyond that cutoff the absolute bound costs $H\sum_{q>(\log X)^4}b(q)/q+\sum_{q\le2X}b(q)\ll H(\log\log X)/(\log X)^2+\sqrt X\log X$. These are smaller than the stated allowance. The exponent $19/35$ is larger than $1/2$. [Matomäki et al., Theorem 1.4](https://arxiv.org/pdf/2610.09567)

## What can be trimmed at the target exponent?

Fix any nondecreasing $D(n)=n^{o(1)}$ tending to infinity. Remove a mark once and for all when its own cofactor satisfies $d\le D(n)$. The total absolute cost through $X$ is bounded by
$$
 \sum_{d\le D(X)}\sum_{v\le\sqrt{X/d}}v
 \ \ll\ \sqrt X\log(2X)\sqrt{D(X)}=X^{1/2+o(1)} .
$$
Thus in a square-root-*plus-every-epsilon* criterion these largest isolated marks can be returned even after completely forgetting their signs. A fixed square-root ceiling or a pointwise sign calls for a tighter account. This gives a genuine choice of which arithmetic to investigate next, while retaining the exact price of returning the discarded labels.
