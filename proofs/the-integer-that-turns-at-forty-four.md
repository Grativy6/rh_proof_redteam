# The integer that turns at 44

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). Pang asked which distinction travels between successive frames. The direction of the one-head primitive has an integer answer.

Put $M_a(x)=\sum_{n\le x}a(n)$, with $a(v^2d)=v\mu(d)$ for $v=2^i3^j$, $(d,6)=1$, and zero elsewhere. The running mass is **+1 at 43**. The next label is $44=2^2\cdot11$, with mark $-2$, so the mass becomes **−1**. Our direct arithmetic proves it stays strictly negative through **27,373,823,781**. A separate transfer using Lioen and van de Lune’s published finite bound for the ordinary Mertens function keeps it strictly negative through **10 trillion**.

**If this integer is nonpositive at every sufficiently large input, then stock Mathlib RH follows.** A finite divisor argument connects that sign to the [one-head primitive](one-quantity-at-each-fourth-power.md). There is also a weaker paper criterion that allows many exceptions. [How many changes of direction a zero would force](../pal-rh/how-many-rising-steps-would-a-zero-force.md)

## Why a negative count produces a positive height

Write $B(Y)=\sum_{n\le Y}a(n)(Y/n-1)$. At noninteger $t$,
$$
 \frac{d}{dt}\frac{B(t)}{t}=\frac{M_a(t)}{t^2}.
$$
The following proof of the implication only uses finite sums. Let $Y$ be a positive integer and choose $X=Y!$. The divisor convolution $b=a*\mathbf1$ is nonnegative. At $2^i3^j$ it equals $(2^{\lfloor i/2\rfloor+1}-1)(3^{\lfloor j/2\rfloor+1}-1)/2$ and it vanishes off the smooth integers. Consequently
$$
 \sum_{r\le X}M_a(\lfloor X/r\rfloor)=\sum_{m\le X}b(m)\ge0 .
$$
If $M_a(n)\le0$ for every $n\ge Y$, the terms $r\le X/Y$ are all nonpositive. The remaining rows have nonnegative total. Count them the other way. Label $n\le Y$ appears at exactly $X/n-X/Y$ multipliers, because every such $n$ divides $X$. Therefore
$$
 0\le\sum_{X/Y<r\le X}M_a(\lfloor X/r\rfloor)=\frac XY B(Y).
$$
Once the running sign holds at all late inputs, the primitive is nonnegative at every sufficiently late doubled fourth power. The Lean proof implements this exact finite implication. Its independent reference defines the running mass as an integer using ordinary Mathlib Möbius coefficients. The fixed conditional statement passed the separate Linux comparison, and another build reproduced both exports byte for byte. [Finite rectangle and stock implication](../pal-rh/PALRH/RunningMass.lean) · [Mathlib-only challenge](../pal-rh/checks/running-mass/MassChallenge.lean) · [Solution](../pal-rh/checks/running-mass/MassSolution.lean)

## A shorter finite frame can tolerate a square-root error

The factorial makes both endpoints exact, but a comparison at the resolution needed for RH can be made in a much smaller frame. For any integer $X\ge Y$ let $A(X,Y)$ denote the same sum over $r>\lfloor X/Y\rfloor$. Then
$$
 A(X,Y)=\sum_{n\le Y}a(n)\bigl[\lfloor X/n\rfloor-\lfloor X/Y\rfloor\bigr].
$$
Take $m\ge1$ independent uniform integers from $0$ through $Y-1$, and let $X$ be $Y$ plus their sum. Expectation here means a finite rational weighted sum. For every $n\le Y$, write $Y=qn+r$. One draw modulo $n$ consists of $q$ complete cycles and $r$ extra residues. Its distribution is exactly uniform with coefficient $1-r/Y$, plus an arbitrary leftover distribution with coefficient $r/Y<1/2$. In the sum of $m$ independent draws, any complete-cycle component makes the result uniform. The remaining fraction is below $2^{-m}$. Thus the expected fractional part of $X/n$ differs from $(n-1)/(2n)$ by at most $2^{-m-1}$. At $n=Y$ the distribution is exactly uniform.

For $\bar X=Y+m(Y-1)/2$ it follows that
$$
 \left|\mathbb E A(X,Y)-(\bar X+1/2)\frac{B(Y)}Y\right|
 \le 2^{-m-1}\sum_{n\le Y}|a(n)|\le 3Y\,2^{-m-1}.
$$
The half unit comes from the two discrete mean residues, including the one at $Y$. The last bound holds because $\sum_v 1/v=3$. Taking $m=\max(1,\lceil\log_2\sqrt Y\rceil)$ puts this error within $3\sqrt Y/2$. Every sampled $X$ is at most $(m+1)Y$, and each reading that precedes $A(X,Y)$ needs at most $m+1$ running counts $M_a(\lfloor X/r\rfloor)$. Their signed sum can be compared with the known nonnegative $\sum_{n\le X}b(n)$. This is a finite alternative to enumerating a factorial-sized frame. Its unknown is the actual signed contribution of those earlier rows. [Exact small-window and factorial replays](../receipt-archives/check_pal_signed_mass.py)

## How far the running sign is established

**Independent integer calculation.** We factored the physical coefficients through 200 million, including the return to negative at 44. Above this range we computed $M_a(\lfloor T/k\rfloor)$ at 159,602 consecutive quotient indices for $T=32$ trillion. One calculation works directly with the nonnegative smooth $b$ and the recurrence $\sum_r M_a(\lfloor n/r\rfloor)=\sum_{q\le n}b(q)$. Another inverts only multipliers coprime to six on the rough Möbius stream and sums the smooth squares afterward. The raw grid files agree byte for byte despite different recurrences and sieve cutoffs.

On each pair of adjacent endpoints $l<r$, any $l\le t\le r$ satisfies
$$
 2M_a(t)\le M_a(l)+M_a(r)+\sum_{l<n\le r}|a(n)|.
$$
Counting the allowable rough cofactors gives the last upper bound, with a tighter count excluding four small prime squares when necessary. This pays every interval continuously up to **27,373,823,781**. On the immediately following interval the two endpoint masses are −10,843,334 and −10,855,494. The absolute upper allowance of 21,715,074 is too large for that particular test. The allowance identifies its own stopping point. [Two quotient recurrences](../receipt-archives/physical_mass_grid.cpp) · [Interval replay](../receipt-archives/check_pal_signed_mass.py)

**Extension using a published finite input.** Write $M_\mu(z)=\sum_{d\le z}\mu(d)$ for the ordinary Mertens function. Since $a=\mu*b$,
$$
 M_a(t)=\sum_{q=2^i3^j\le t} b(q)M_\mu(\lfloor t/q\rfloor).
$$
For ordinary arguments through 200 million we sieved $\mu$ ourselves and retained exact maxima in 26,765 integer bins. Above that cutoff we used only Lioen and van de Lune’s upper bound $M_\mu(z)<0.571\sqrt z$, proved by their exhaustive computation for $200<z\le10^{13}$. We independently checked that bound in our own direct range. For each of 22,165 subsequent physical intervals $[l,r]$, every $M_\mu(\lfloor t/q\rfloor)$ is bounded above by the measured maximum over the bins it can visit, or by the published upper bound at $\lfloor r/q\rfloor$. Multiply by the nonnegative integer $b(q)$ and add. Every resulting upper bound is negative. [Lioen and van de Lune, Section 6](https://ir.cwi.nl/pub/13491/13491D.pdf) · [Our envelope calculation](../receipt-archives/signed_mass_envelope.cpp)

The proved margin on the part beyond 200 million is at least **$2.980492\sqrt n$** at every integer through $10^{13}$. The same interval arithmetic would suffice with an ordinary constant of 0.594 for this full range, or 0.785 for the part through two trillion. At the final input, two separate exact quotient calculations give **$M_a(10^{13})=-274{,}138{,}671$** and $594{,}102{,}836<B(10^{13})<594{,}103{,}671$. Since $B(t)/t$ decreases while $M_a$ is negative, its positive value at the final head proves positivity throughout the preceding interval. The extension above two trillion uses the named finite input. The [two-trillion primitive proof](one-quantity-at-each-fourth-power.md) uses only our own endpoint enclosures and the elementary gap bound.

On the doubled fourth powers up to root **342**, our independent calculations find one rising transition of $B(2j^4)/(2j^4)$, from root 1 to 2, and 340 falling transitions. The finite extension reaches root **1,495**, with that same one rise and 1,493 falls. The early transition from root 2 to 3 is checked directly. [Integer evidence and exact source](../receipt-archives/2026-11-25-pal-running-mass.json)

## Why the finite envelope cannot prove the infinite sign as it stands

Hold the directly sieved bound $D$ fixed and replace every larger $M_\mu(t/q)$ independently by any fixed positive multiple of $\sqrt{t/q}$. The upper allowance, divided by $\sqrt t$, grows at least as fast as $(\log t)^2$. Indeed $b(q)/\sqrt q\ge1/\sqrt6$ for every smooth $q$, and $\gg(\log t)^2$ such $q$ have $q\le t/(2D)$. The known small arguments $1\le t/q\le D$ contribute only $O_D(\log t)$ in the same units, since they occupy a fixed-width strip in the logarithms of the smooth roots. Even an indefinitely valid constant majorant would lose the sign in this procedure. The actual relationship among unbounded rough readings has to enter. A definite negative contribution from that relationship can already be isolated on every sufficiently late scale. [The negative coefficient on physical marks](../pal-rh/where-the-negative-running-mass-comes-from.md)
