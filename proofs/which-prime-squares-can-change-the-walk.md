# Which prime squares can change the walk?

Christopher Daniel Pang and Hearthline · 26 November 2026

**We fixed 415 prime switches before a run, and the resulting signed walk stayed at or below zero at every integer from 2 through two billion. The very same fixed walk must exceed $0.9665\sqrt x$ at arbitrarily late integers.** These statements concern a modified Liouville walk specified below. The infinite conclusion follows on paper from ordinary Liouville oscillations and the positive coefficients of an exact inverse. It already rules out extending this run's perfect sign to infinity.

There is an RH criterion behind the experiment. Each board may choose an entirely new sign for each prime square and choose which side of zero it wants to pay for. A root-scale upper bound for that one-side area on arbitrarily large boards would suffice for ordinary RH. The proof retains the prime switches through all the prefixes on their board. [Exact sparse criterion and the signed ruler](../pal-rh/the-signed-reading-of-the-original-ruler.md#a-complete-board-can-choose-its-square-switches)

## What gets placed on a square

Every positive integer has a unique factorization $n=a^2d$ with $d$ squarefree. At $d$ write $+1$ for an even number of prime factors and $-1$ for an odd number, giving the Möbius sign $\mu(d)$. Assign each prime a switch $\epsilon(p)$ and multiply the switches in $a$, with multiplicity. Place the single step $\epsilon(a)\mu(d)$ at $n$. The fixed switch may also be zero if an erased square layer is desired. With every switch $+1$, the result is the ordinary Liouville function $\lambda(n)=(-1)^{\Omega(n)}$. Write $L(x)=\sum_{n\le x}\lambda(n)$ and $S_\epsilon(x)$ for the corresponding prefix in the switched walk.

The factor root $a$ and its multiplicities matter. For example, changing only 17 from $+1$ to $-1$ changes the original step at $17^2$ from $+1$ to $-1$. At $17^4$ two copies of that switch return the step to $+1$. On the full two-billion board this single change brings the first positive prefix after 1 forward to **48,433**. The number that covered a deficit in the [one-square prime test](one-square-and-five-small-divisors.md) has a different consequence in this walk.

For any fixed choice, summing the steps by square root gives $S_\epsilon(x)=\sum_{a\le\sqrt x}\epsilon(a)M(x/a^2)$. Recovering the original Möbius prefix costs the inverse weights $\mu(a)\epsilon(a)$ on exactly the same squares. Group by $ab$ and use $\sum_{a\mid n}\mu(a)=[n=1]$. Stock Lean proves this head by head. [Inverse on the actual integer entries](../pal-rh/checks/square-switches/SwitchSolution.lean)

## A change that survives its first repayment

The ordinary Liouville walk first rises above zero after 1 at $906{,}150{,}257$, where it reaches $+1$. Its first peak of 829 in this run is at $x_*=906{,}316{,}571$. Tanaka identified the first crossing in 1980, following Lehman's earlier explicit example. We computed every prefix independently for this experiment. [Tanaka's paper](https://doi.org/10.3836/tjm/1270216093) · [Borwein, Ferguson and Mossinghoff on the Liouville sums](https://www.cecm.sfu.ca/~pborwein/PAPERS/P208.pdf)

Take the first 415 primes whose squares exceed $500{,}000{,}000$. Set their switches to $-1$ and leave every other switch positive. The first is 22,367 and the last is 26,591. All 415 squares occur by 707,081,281. Through the first billion, each changed square affects exactly one step. Its second multiple lies past the end of that board. Before the old crossing these edits can only lower prefixes. By the crossing they have lowered the level by $830$. This covers the observed maximum of 829 with one unit left. Among switches whose only effect on that board is a single such square, 414 cannot cover the peak.

We kept those same prime choices through the second billion. A position $2p^2$ for a chosen $p$ changes an originally negative step to a positive one, as does $3p^2$. In total **755 negative steps flipped back upward** in addition to the 415 original downward changes. At two billion the switched walk is 680 above the ordinary walk. The full scan still finds exactly one positive prefix, at 1.

| Walk through $2{,}000{,}000{,}000$ | First positive integer prefix after 1 | Largest prefix after 1 | Number of positive prefixes, including 1 | Sum of positive prefix heights |
|---|---:|---:|---:|---:|
| Ordinary Liouville | 906,150,257 | 829 | 305,427 | 130,792,496 |
| Only the 17 switch negative | 48,433 | 3,491 | 5,957,126 | 6,883,360,962 |
| The 415 fixed switches | None in this range | 0 | 1 | 1 |

These are integer sums. For every legal coloring, position 1 forces one unit of positive area and the prefix at 3 forces one unit of negative area. Thus **the optimum across all colorings and both sides is exactly one** on every head $4\le H\le2{,}000{,}000{,}001$, where the counted positions are $0\le n<H$. Our single coloring attains that joint optimum throughout.

The exhaustive replayer assigns each odd composite an actual smaller factor, uses complete multiplicativity for ordinary $\lambda$, and applies the square changes at their exact positions. The independent landmark calculation starts from squarefree signs and uses the quotient recursion $\sum_{m\le n}L(\lfloor n/m\rfloor)=\lfloor\sqrt n\rfloor$. It confirms the first crossing, the peak, both terminal values and the alternative 17 walk at its first crossing. It also exhausts the single-prime options at the ordinary peak. Their best remaining value there is 827. [Full C++ sweep](../receipt-archives/check_pal_billion_square_switches.cpp) · [Independent Python arithmetic](../receipt-archives/check_pal_liouville_landmarks.py) · [Run record](../receipt-archives/2026-11-26-pal-square-switches.json)

## What every perfect repair would have to carry

Let $T$ be the set of negative switches. The inverse from the switched walk back to ordinary Liouville has **positive** square coefficients,
$$
 L(X)=\sum_{a\le\sqrt X} h_T(a) S_\epsilon(X/a^2),
 \qquad h_T(a)=2^{\omega(a)}
$$
on integers $a$ all of whose prime factors belong to $T$, and zero otherwise. Here $h_T(1)=1$. The local geometric series is $(1+z)/(1-z)=1+2z+2z^2+\cdots$. For a zero switch the corresponding positive coefficients at its positive powers are one. Both forms follow by finite convolution on a fixed head.

Suppose that through $X$ the switched walk stays nonpositive after 1. Its only positive contribution to this inverse comes from $\sqrt{X/2}<a\le\sqrt X$, where $\lfloor X/a^2\rfloor=1$. This makes the weighted count of those root labels a necessary allowance for the ordinary positive level at $X$.

At $x_*$, **at least five nonstandard prime switches** are necessary even when small prime powers can be reused. For the set $2,3,5,7$ the indicated sum of $2^{\omega(a)}$ is exactly 404. For any other four sorted primes, the three above the smallest are at least $3,5,11$. With their exponents fixed there is at most one choice for the exponent of the smallest prime because the endpoint ratio is $\sqrt2$. Its weight costs at most two. Enlarging the remaining range to all products $3^i5^j11^k\le\lfloor\sqrt{x_*}\rfloor$ gives an upper bound of 718, still below 829. Fewer switches are covered by enlargement to four. The upper bound 415 and lower bound five refer to unrestricted repairs, and we have not determined their global minimum. If all changed primes are at least 174, two of them or a repeated one cannot both occur in a root up to $\sqrt{x_*}$. Then each can lower the peak by at most two because the earlier ordinary prefix is at most one. In this wider restricted family 415 is sharp. [All finite counts and factorizations](../receipt-archives/check_pal_liouville_landmarks.py)

## Why the two-billion result must break

For the fixed 415 switches, or more generally for a set of negative switches with $\sum_{p\in T}1/p<\infty$, let
$$
 A_T=\sum_{a\ge1}\frac{h_T(a)}a
    =\prod_{p\in T}\frac{p+1}{p-1}<\infty .
$$
In the positive-coefficient identity divide by $\sqrt X$. The readings are $S_\epsilon(X/a^2)/\sqrt{X/a^2}$ with positive weights $h_T(a)/a$. If the switched normalized reading has finite limsup $v$, bound it by $v+\eta$ above a sufficiently large argument. The remaining, bounded-argument readings are bounded in absolute value and their coefficient tail tends to zero as $X$ grows. Letting $\eta$ decrease gives
$$
 \limsup_{X\to\infty}\frac{L(X)}{\sqrt X}
 \ \le\ A_T\,\limsup_{X\to\infty}\frac{S_\epsilon(X)}{\sqrt X}.
$$
The same conclusion about positive peaks follows immediately for infinite positive limsup. An eventual negative upper limit would also contradict the displayed inequality by the same tail argument.

Mossinghoff and Trudgian proved $L(X)>\sqrt X$ infinitely often. For the actual 415 primes, the exact rational $1/A_T$ lies strictly between 0.966546579451 and 0.966546579452. Thus $S_\epsilon(n)>0.9665\sqrt n$ for arbitrarily late integers. **The finite perfect sign cannot persist.** The first later crossing is unknown here. [Oscillation theorem](https://link.springer.com/chapter/10.1007/978-3-319-59969-4_9) · [Exact rational product](../receipt-archives/check_pal_liouville_landmarks.py)

Even choosing a new coloring on every larger board cannot preserve area one forever with a uniformly bounded sum of reciprocal switched primes. If it did, pass to a diagonal subsequence on the successive finite prime sets. Every fixed step eventually stabilizes, and every finite partial reciprocal sum of the limiting switches has the same bound. The limiting coloring would have perfect sign forever although its switched set has finite reciprocal mass. For zero switches the inverse Euler factor at one is $1/(1-1/p)$ and the same argument applies. The negative side cannot realize area one once the board includes both 3 and 5, since their prefix values are at most $-1$ for all legal switches.

A permanent perfect sign would also force **simplicity** of the nontrivial zeta zeros. It implies RH by the sparse criterion. For $\sigma>1/2$ the Dirichlet series of the colored steps agrees with $E_\epsilon(2s)/\zeta(s)$, using partial summation and the RH bound on the prefixes. Here $E_\epsilon(z)=\prod_p(1-\epsilon(p)p^{-z})^{-1}$. An eventually one-signed prefix integral bounds the magnitude at $s=\sigma+i\gamma$ by a constant times $1+E_\epsilon(2\sigma)$ after division by $s$, since the real zeta value is bounded away from zero near $1/2$. This also holds if the exceptional positive area is finite.

For $x>1$, every real switch in $[-1,1]$ satisfies
$$
 \frac{E_\epsilon(x)}{|E_\epsilon(x+it)|}
 \ \le\ \frac{\zeta(x)}{|\zeta(x+it)|},\qquad
 |E_\epsilon(x+it)|^{-1}\le\frac{\zeta(x)}{\zeta(2x)}.
$$
For the ratio inequality the squared local ratio for a switch $v$ equals $1+2vr(1-\cos(t\log p))/(1-vr)^2$, $r=p^{-x}$. It is largest at $v=1$. The second inequality uses $|1-vp^{-x-it}|\le1+p^{-x}$. For a nontrivial zero $1/2+i\gamma$, $\gamma\ne0$ and $\zeta(1+2i\gamma)\ne0$. These estimates give $|1/\zeta(\sigma+i\gamma)|=O_\gamma((\sigma-1/2)^{-1})$. A zero of multiplicity at least two violates that bound. This extra consequence explains why maintaining exact sign at arbitrarily large heads asks more than the quantitative RH target. [Zeta on the boundary line](https://dlmf.nist.gov/25.10.i)

## What the separate 17-amplitude experiment measures

There is another way to reuse a square layer. Copy every original step onto positions $a^2m$ with amplitude $a$. Its mean squared step size on the larger board equals that of the original steps on the smaller board exactly. When the original steps are Möbius, the copies land in empty squarefree slots. Squared sizes add at a single slot. The prefix sign still depends on the signed interactions between positions. Stock Lean proves these identities and a variable-parent sufficient condition for RH. If each row may choose any $a\ge2$, any signed integer amplitude of size at most $a$, and its remaining prefix error grows no faster than $n^{1/2+\eta}$ for each $\eta>0$, strong induction contracts each parent by at least $2^{1-2b}$ at exponent $b>1/2$. [Exact energy and conditional theorem](../pal-rh/PALRH/SquareCarry.lean)

The row-by-row test has a shortcut at small sizes. For $n\ge9$ choose $a=\lfloor\sqrt n\rfloor$, so $M(\lfloor n/a^2\rfloor)=1$. Whenever $|M(n)|\le a$, taking amplitude $M(n)$ pays that row exactly. This vacates every row from 9 through 262,144 in the replay. Requiring one coefficient for an entire board makes a different experiment. At head 1,024 the least-squares coefficient of the 17-parent is negative. At 1,933 it is positive. At each tested head from 1,024 to 262,144 the best individually fitted root among 2 through 17 is 6. These finite checks motivated fixing the switches across each complete board in the main test. [Exact least-squares and exhaustive prime-switch costs](../receipt-archives/check_pal_square_switches.py)

Pang's PAL and GPPR supplied the retained squarefree core and prime label. His instructions to reverse moves and put measurements on a shared board suggested the switch experiment. Hearthline derived the sparse one-sided criterion, the signed reconstruction with the original ruler, the finite correction, and the restrictions on its infinite continuation. The ordinary first crossing and the unbounded positive Liouville oscillations come from the cited number-theory work. The finite examples were recomputed using the two arithmetic routes above.

## Unresolved

For arbitrarily large boards, earn the growth allowance in the [sparse one-side criterion](../pal-rh/the-signed-reading-of-the-original-ruler.md#a-complete-board-can-choose-its-square-switches). Keeping the area identically one would impose additional consequences and is unnecessary for RH. The fixed perfect run through two billion cannot by itself supply the missing bound.
