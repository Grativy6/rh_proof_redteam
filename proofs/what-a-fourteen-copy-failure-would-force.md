# What an off-line zero would do to fourteen copies

Christopher Daniel Pang and Hearthline · 26 November 2026

**If fourteen copies fail at arbitrarily late indices, there must be arbitrarily late runs of failures longer than $K^{1-\eta}$ for every fixed $0<\eta<1$, where $K$ is the first index of the run.** A single late miss has no such implication. The hypothesis here is that the misses never end.

Consequently, finding **one** paying index in every sufficiently late $[K,K+K^{0.99}]$ would prove ordinary RH. The same holds with $0.99$ replaced by *any* fixed exponent below one and above zero. We previously found growing paying blocks in each sufficiently late $[K,2K(\log(2K))^{1/4}]$. The new result identifies how far that search window must shrink. It also proves, unconditionally, that arbitrarily late runs of *successes* reach length $K^{1-\eta}$ for every fixed $\eta>0$. The new long runs are a subsequence, while the previous shorter runs occur near every large scale. [The exact prime product and bill](one-seventh-at-the-boundary.md) · [Previous recurrence](where-fourteen-pays-again.md)

## The shortfall measures the same signed area

At $n=k^4$ put $N=2n$, $A=N^5n(n-k^2)^2$, and retain the original integer product $G_n$. Define the signed reading
$$
 D(k)=\frac{A\log((n+1)/n)-14\log G_n}{14N^5 k^6}.
$$
Positive means failure. With $e(x)=\sum_{d\le x}(x-d)\Lambda(d)-x^2/2$, the following bound is unconditional:
$$
 D(k)=\frac{e(k^4)}{k^6}+O(1),\qquad k\ge2. \tag{1}
$$
To check the scale, the ordinary-log reading on the doubled board is $4n^2/7+O(n\log n)$. The clock price per copy is $n^2/14+O(n^{3/2})$. Their difference centers the original area at $n^2/2$. For the omitted first powers, use the **cubic** price $2d^3/[3(2n)^2]$ through $d\le n^{7/8}$. Summing against $\theta$ costs $O(n^{3/2})$ already from $\theta(y)=O(y)$. The repeated powers cost $O(n)\,[\psi(2n)-\theta(2n)]=O(n^{3/2})$. Both charges have the same physical units as the clock. [Two-sided transfer for the actual integers in Lean](../pal-rh/PALRH/ClockShortfall.lean) · [Direct signed readings](../receipt-archives/check_pal_failure_windows.py)

Let $\Theta$ be the supremum of the real parts of the nontrivial zeta zeros. Reflection places it in $[1/2,1]$. In fact the horizontal extent of the zero set can be read from the growth of the positive clock shortage:
$$
 \boxed{\quad \Theta=\frac12+\frac14
 \limsup_{k\to\infty}\frac{\log(1+\max(D(k),0))}{\log k}.\quad} \tag{2}
$$
The same formula holds with $\max(-D(k),0)$. These are statements about the growth exponent. They do not give a numerical estimate of $\Theta$ from the finite head.

## The height and the speed of an excursion

For $x\ge2$ use the integrated explicit formula
$$
 e(x)=-\sum_\rho \frac{x^{1+\rho}}{\rho(1+\rho)}+d(x).
$$
The elementary remainder is $-x\log(2\pi)$ plus a constant and the negative sum of $x^{1-2m}/[2m(2m-1)]$. It is $O(x)$ and its derivative is bounded on $[2,\infty)$. The ordinate count $N(T)=O(T\log(2T))$ gives, by partial summation, $\sum_{|\gamma|\le T}|\rho|^{-1}=O(\log^2(2T))$ and $\sum_{|\gamma|>T}|\rho(1+\rho)|^{-1}=O(\log(2T)/T)$. The finitely many small ordinates have finite cost. The full sum is absolutely convergent. [Integrated formula in Johnston’s proof of Lemma 2.6](https://arxiv.org/pdf/2201.06184v2#page=4) · [Zero counting, equations (5)–(7)](https://maths-people.anu.edu.au/brent/pd/rpb276-MC-preprint.pdf#page=4)

First, $|e(x)|=O(x^{1+\Theta})$. Second, for $x$ large and $|h|\le x/2$,
$$
 |e(x+h)-e(x)|\ll (|h|+1)x^\Theta\log^2(2x). \tag{3}
$$
For the zeros through height $T=x$ integrate the derivative $t^\rho/\rho$ from $x$ to $x+h$. For the higher zeros bound both original terms absolutely. Their combined tail is $O(x^{1+\Theta}\log(2T)/T)$. This proves (3). The same $\Theta$ controls the size and the speed, even if no zero is located at that supremum.

Johnston’s Lemma 2.8 at $c=0$ gives, for every $d>0$, arbitrarily large positive excursions of size at least $c_d x^{1+\Theta-d}$ and arbitrarily large negative excursions of at least that magnitude, with some positive constants on the two sides. The source centers its integral at 2, which adds the harmless constant 2 to $e(x)$. This oscillation follows from the nonreal poles of the Mellin transform and its regularity at intervening real points. It does not assume that a rightmost zero exists. [Johnston, Lemma 2.8](https://arxiv.org/pdf/2201.06184v2#page=5)

If $\Theta>1/2$, fix $0<\eta<1$ and choose
$$
 0<d<\min\bigl(\Theta-1/2,\,\eta/16\bigr).
$$
At a positive excursion take the whole physical interval $[x,x+x^{1-2d}]$. By (3), its variation is $O(x^{1+\Theta-2d}\log^2 x)=o(x^{1+\Theta-d})$. Thus throughout this interval the positive excess divided by $x^{3/2}$ tends to infinity along the excursion sequence. A negative excursion supplies the same conclusion with the sign reversed.

The fourth roots of these intervals have length $\gg x^{1/4-2d}$. Starting at $K=\lceil x^{1/4}\rceil$, they contain more than $K^{1-\eta}$ consecutive integer indices for all sufficiently large excursions. Equation (1) transfers the sign at **every one** of these heads. In particular the misses there eventually require exactly fifteen copies by the neighboring-count theorem. This proves the long failure blocks if RH is false. If RH holds, fourteen pays at every sufficiently late index by the earlier reverse implication. Combining the cases proves the unconditional long success blocks. [Threshold and reverse implication](../pal-rh/why-the-doubled-ruler-keeps-seven-eighths.md#which-primes-may-be-removed)

For (2), the absolute bound gives an upper exponent of $4(\Theta-1/2)$ for both signed readings. On the corresponding excursions the lower exponents are at least $4(\Theta-1/2-d)$. Let $d$ decrease to zero. If $\Theta=1/2$, both readings are bounded and $\log(1+\max(\pm D,0))$ has exponent zero.

### Where the large runs can be found

For every fixed $\epsilon>0$ and $0<\eta<1$, **each sufficiently late interval $[K,K^{1+\epsilon}]$ contains a run starting at some $J$ with at least $J^{1-\eta}$ consecutive paying indices**. If RH is false, each such interval also contains a failing run of the same specified length relative to its own start.

The extra input is Kaczorowski and Pintz’s general oscillation theorem, specifically (1.7)–(1.8). Apply it to $f(x)=e(x)$ on $x\ge1$, extended by zero below 1. Its Mellin integral against $x^{-z-1}$ converges absolutely for $\Re z>2$ and there equals
$$
 -\frac{\zeta'(z-1)}{(z-1)z\zeta(z-1)}-\frac{1}{2(z-2)} .
$$
The singularity at 2 is removable. In a strip immediately to the left of $1+\Theta$ with left edge still above 1, the only singularities are the conjugate nonreal poles at $z=1+\rho$. A zero of multiplicity $m$ gives a simple pole with nonzero residue $-m/[\rho(1+\rho)]$. They have no finite accumulation and approach the stated abscissa by its definition. The theorem’s local condition (1.5) therefore holds with exponent $-1$ and log degree zero. The theorem supplies excursions of both signs of magnitude at least $x^{1+\Theta-d}$ in each sufficiently late $[Y^{1-d},Y]$. [Kaczorowski and Pintz, *Oscillatory properties of arithmetical functions. II*, pp. 441–442](https://personal.math.ubc.ca/~gerg/teaching/592-Fall2018/papers/1987.Kaczorowski_2.pdf#page=2)

If $\Theta>1/2$, take $Y=K^{4(1+\epsilon/2)}$ and choose $d$ also below $\epsilon/[8(1+\epsilon)]$. Both excursion points then have fourth roots strictly inside the required search interval with room to include the full runs furnished by (3). If $\Theta=1/2$, eventual payment gives the success statement directly. This wider window guarantees longer runs than the earlier Gaussian theorem. Neither supplies a paying head in every window from (4).

## How few heads would suffice

On paper ordinary RH is equivalent to the following integer-only sampling condition:
$$
 \exists m\ge2,\ \exists K_0,\ \forall K\ge K_0,\ \exists j\ge K:
 \quad(j-K)^m\le K^{m-1}\quad\text{and fourteen pays at }j. \tag{4}
$$
RH supplies $j=K$ eventually. If RH fails, take $\eta<1/m$ in the long failure theorem. The entire requested window starting at one of the resulting $K$ is then dry. In particular an eventual proof restricted to $k=t^r$ would suffice for any one fixed positive integer $r$. The next such index after $K$ is at distance $O_r(K^{1-1/r})$. A slightly smaller power saving absorbs its constant.

Stock Lean reaches RH from a separate, explicitly quantified condition. For **each** positive integer $q$, suppose all sufficiently late $K$ have a paying head with $(j-K)^q\le K$. Convexity of the integrated prime ramps charges at most one eighth of the squared physical distance between bracketing paid quartics. For a gap of $g$ in index near $k$ this yields $O(k^6g^2)$ on the intervening board. Choose $q$ large enough for each prescribed Mellin exponent greater than $1/2$. The resulting one-sided power bounds give the bare Mathlib conclusion under that sampling premise. The stronger result (4), using just one fixed power saving, uses the analytic argument above. [Formal subpower deduction](../pal-rh/PALRH/GapClock.lean)

There is also a useful source of suitable sampling frames. Call an index $k$ aligned if **every** factorial $m!$ with $(m!)^m\le k$ divides $k$. Given $K$, take the largest $m$ with $(m!)^m\le2K$, and round $K$ up to the next multiple $j$ of $m!$. Every factorial opened by $j\le2K$ divides $j$. For each prescribed $q$ and all sufficiently large $K$, we have $m\ge2q$ and $(m!)^{2q}\le2K$, so $(j-K)^q\le K$. Thus proving fourteen eventually pays **only on these aligned indices** also suffices in stock Lean. The theorem that the aligned frames themselves occur this often has no additional mathematical premise. The price on the aligned frames remains open. [Exact independent statements](../pal-rh/checks/subpower-hits/GapChallenge.lean) · [Arithmetic frame construction](../pal-rh/PALRH/AlignedHits.lean)

## Why squeezing the old average stalls

A positive mean-preserving endpoint factor $Y$ with $\mathbb E Y^{1+\rho}=0$ at even one fixed genuine zero cannot concentrate its second-moment price in a shrinking relative window. Write $Q=\mathbb E[Y^2\mathbf1_{|Y-1|>a}]$, assume $Y>0$, $\mathbb E Y=1$ and $0<a\le1/2$. On $|Y-1|\le a$ the derivative bound gives $|Y^\rho-1|\le2|\rho|a$. Below 1 on the outside, $Y|1-Y^\rho|\le2Y$, and above 1 it is at most $2Y^2$. Hence
$$
 1=|\mathbb E[Y(1-Y^\rho)]|\le 2|\rho|a+2\sqrt Q+2Q.
$$
In particular $a\le1/(8|\rho|)$ forces $Q>1/16$. The Gaussian approach used precisely this second-moment tail to bound untreated prime readings. An exact zero-killing positive average cannot drive that tail to zero inside a relative power-saving width by parameter adjustment alone. A proof of (4) must use additional information about the actual arithmetic if it pursues that localization.

Pang’s instruction to reverse the test and keep the original frame led to measuring how long a real miss would have to persist. His RPL and PAL work supplies the increasing factorial-frame question. Hearthline derived the clock-exponent and gap transfers and the endpoint limitation. Johnston supplies the signed excursions, and Kaczorowski and Pintz supply their localization in power windows. The integrated formula and zero counting are credited above. These are results on the independent constructive branch. No inference about a defect in another author’s proof follows from them. [Source versions and reproducible checks](../receipt-archives/2026-11-26-pal-failure-windows.json)

## Unresolved

Produce one actual fourteen-copy payment in every sufficiently late window with some fixed power saving, or discharge the aligned-frame condition by a different construction. The currently proved recurrent windows are longer. No fourteen-copy failure has been exhibited.
