# How much can the newest half gain?

Christopher Daniel Pang and Hearthline, 26 November 2026 (New York).

At 16, keep the marks that arrived after 8. They are $+3$ at 9, $-1$ at 11, $-1$ at 13 and $+4$ at 16. The newest half gained **five**. If we could bound every positive gain of this sort by a constant times the square root of the head, we would have an independent proof of RH. The constant can be as large as necessary. Downward changes cost nothing.

This tests the [two-root allocation](why-the-last-two-square-roots-remain.md) from the other direction. On every owner $n>t/2$ only the root 1 is present, and the divisor allocation has spent zero on it. So the newest half is an actual collection of whole, still-available marks. Adding it to the previously earned signed portion never spends a mark twice.

## A hand proof of the implication

Write $M(n)=\sum_{k\le n}a(k)$, with $a(v^2d)=v\mu(d)$ for $v=2^i3^j$ and $(d,6)=1$, zero elsewhere. Set $M(0)=0$ and $H(n)=M(n)-M(\lfloor n/2\rfloor)$. Suppose $H(n)\le C\sqrt n$ for every integer $n$. Repeated halving gives
$$
 M(n)=H(n)+H(\lfloor n/2\rfloor)+H(\lfloor n/4\rfloor)+\cdots
 \le\frac{C\sqrt n}{1-1/\sqrt2}<4C\sqrt n .
$$
The terms on the right of the identity are the signed counts of disjoint intervals. Any finite initial set of positive exceptions can be absorbed in $C$.

For completeness, write $U$ for a constant with $M(n)\le U\sqrt n$. At a positive integer $T$ put $X=T!$. Grouping the divisors of each original mark gives $\sum_{r\le X}M(\lfloor X/r\rfloor)\ge0$, since $a*1$ has nonnegative coefficients. The part with $r\le X/T$ is at most $U\sqrt X\sum_{r\le X/T}r^{-1/2}\le2UX/\sqrt T$. The remaining rows contribute exactly $(X/T)B(T)$, where
$$
 B(T)=\sum_{k\le T}a(k)(T/k-1).
$$
Indeed an occupied $k\le T$ occurs $X/k-X/T$ times in those rows, and no larger $k$ occurs. Hence $B(T)\ge-2U\sqrt T$. At $T=2j^4$ this is the fourth-power floor already shown to imply stock Mathlib RH. The factorial counts a finite rectangle on paper and need never be evaluated. [The fourth-power implication](one-quantity-at-each-fourth-power.md) · [Formal window proof](../pal-rh/PALRH/TerminalWindows.lean)

The second window takes one more difference,
$$
 D(n)=H(n)-H(\lfloor n/3\rfloor)
 =M(n)-M(\lfloor n/2\rfloor)-M(\lfloor n/3\rfloor)+M(\lfloor n/6\rfloor).
$$
A bound $D(n)\le C\sqrt n$ suffices as well. Undo the thirds first, then the halves. Every coefficient used to reconstruct an upper bound is positive. The two fixed Lean challenges state these premises using integers alone, as $\max(0,H(n))^2\le Kn$ or $\max(0,D(n))^2\le Kn$ with some natural $K$. [Independent fixed statements](../pal-rh/checks/terminal-windows/WindowChallenge.lean) · [Solutions with their premises visible](../pal-rh/checks/terminal-windows/WindowSolution.lean)

## Where the paired marks went

Fix an odd cofactor $u=3^{2j}d$ with $(d,6)=1$. As $t$ passes $4^iu$, the half-window receives $+2^i3^j\mu(d)$. At $2\cdot4^iu$, exactly that mark leaves. All earlier complete pairs cancel. For each such $u$, at most its latest power-of-four mark remains. Squarefree factorization gives its sign even if every earlier pair is discarded. This description also explains why a positive mark at a square can be large.

There is an especially simple second description of the mixed difference. Let $M_\mu(x)=\sum_{d\le x}\mu(d)$ be the **ordinary** Mertens count. Removing multiples of 2 and 3 from the original rough Möbius sum and reversing those two removals gives
$$
 D(n)=\sum_{\substack{v^2\le n\\v=2^i3^j}} v\,M_\mu(\lfloor n/v^2\rfloor).
$$
To see it prime by prime, at 2 the ordinary Möbius factor is $1-2^{-s}$, and at 3 it is $1-3^{-s}$. Their four finite shifts multiply the rough seed by the missing two factors. Equivalently $\mu(u)=m(u)-m(u/2)-m(u/3)+m(u/6)$, where $m$ is rough Möbius and noninteger arguments mean zero. The smooth-square copies retain their weights throughout. For $H$ the corresponding positive coefficients at $q=2^{2i}3^j$ are $2^i(3^{\lfloor j/2\rfloor+1}-1)/2$. These formulas let us check the windows starting from ordinary integer counts.

The mixed description has a signed contribution with a particularly short explanation. The divisor sum of ordinary Möbius is 1 at the unit and zero everywhere else. Therefore the divisor integral of the earlier square-root weight $k$ on this seed is exactly
$$
 \int_1^K M_\mu(y)k(K/y)y^{-3/2}\,dy=(1+\log K)/\sqrt K-1.
$$
Selecting the fraction $k(Kv^2/t)/c$ on each included smooth row $v$ with $1\le t/v^2\le K$ consequently gives a signed contribution asymptotic to $-\sqrt t\log t/(c\log4\log9)$ for the slowly growing cutoff in the previous proof. The underlying positive divisor source has become a single unit. The unselected parts of the same rows still require a bound. [Derivation of the smooth-row limit](../pal-rh/where-the-negative-running-mass-comes-from.md)

## What actually happened in the windows

We enumerated every head through 50,000,000. Positive half-windows occurred just **14** times, the last at 40. The last zero was 66. The largest ratio of positive rise to $\sqrt n$ was **5/4**, attained by the example at 16. The mixed window had **59** positive heads, the last at 1457. Its largest ratio was **1**, attained at 1. A sixteenth-width window was still positive at 48,955,391. The choice of width changes what is visible.

| Exact head | Half-window $H$ | Mixed window $D$ |
| ---: | ---: | ---: |
| 50,000,000 | −102,463 | −51,919 |
| 5,000,000,000,000 | −61,746,438 | −30,432,294 |
| 10,000,000,000,000 | −83,940,561 | −36,276,245 |

The trillion-scale entries are individual integer calculations from two quotient recurrences. To fill in *every intervening integer*, use the positive ordinary-Mertens coefficients above and the earlier exact binned maxima through 200 million. Beyond that ordinary range, Lioen and van de Lune’s published bound supplies an upper envelope up to ten trillion. At the last endpoint $\mu(10^{13})=0$ also gives equality to the preceding ordinary count. With that outside input the half-window stays strictly negative from 67 to **2,473,896,033,938** and the mixed one from 1458 to **153,389,176,633**. The first upper envelopes that cross zero do not give examples of a positive window. Allowing the square-root rises in the actual challenges gives **$K=26$ for the half and $K=36$ for the mixed window through every integer up to ten trillion**. [Exact bounds, first gaps and native counts](../receipt-archives/2026-11-26-pal-terminal-windows.json) · [Lioen and van de Lune, §6](https://ir.cwi.nl/pub/13491/13491D.pdf)

## How narrow can the question get?

The known signed portion $P(t)$ from the two-root calculation satisfies $P(t)\sim-\kappa\sqrt t(\log t)^2$ with $\kappa>0$. An entire newest window $I=(t-w,t]$ is available for $1\le w\le t/2$. Suppose the selected total $P(n)+M(n)-M(n-w(n))$ were eventually nonpositive. Each step backward then costs at most $O(\sqrt n\log^2 n)$.

If for every $\eta>0$ eventually $w(n)\ge n^{1-\eta}$, this still implies RH. In a dyadic interval $[Y,2Y]$ the descending chain takes at most $1+Y^\eta$ steps before leaving it. Summing the costs over the dyadic intervals gives $M(n)\ll_\epsilon n^{1/2+\epsilon}$ from above alone. For any $\alpha>1/2$, subtract $M(t)$ from an adequate $C_\alpha t^\alpha$. The resulting nonnegative function has Mellin transform $C_\alpha/(s-\alpha)-A(s)/s$, initially on $\Re s> \max(1,\alpha)$, where $A(s)$ is the original Dirichlet series. This transform is regular at real $s>\alpha$, while each zeta zero with real part $>\alpha$ would give a pole. The real-singularity argument in the square proof finishes the implication. The choice $w(n)=\lceil n/(1+\lfloor\log_2 n\rfloor)^2\rceil$, eventually below half a head, is one example. [Mellin argument](../pal-rh/what-the-last-two-square-roots-carry.md)

A genuinely short window shows why the width matters. Its absolute input is at most
$$
 \sum_{n-w<k\le n}|a(k)|\le
 \sum_{v^2\le n}v(w/v^2+1)
 \le 3w+2\sqrt n(1+\log_3\sqrt n).
$$
The last bound sums the powers of two at each fixed power of three. With $w=\lfloor\sqrt n\rfloor$, this is $o(\sqrt n\log^2n)$. The selected total is then eventually negative unconditionally. Such a window takes too many steps to recover the required global bound by telescoping. For a numerical model of the loss take $F(n)=\lfloor n^{3/4}\rfloor$ and $w(n)=\lfloor n^{3/4}\rfloor$. The mean value theorem gives $F(n)-F(n-w(n))=O(\sqrt n)$, although $F(n)$ itself grows as $n^{3/4}$. The proof that a narrow strip is cheap and the proof that it still carries the target are independently testable.

## Unresolved

The fixed integer tests need **one** upper bound valid for every head in either window. The unbounded source consists of ordinary Möbius counts with explicit positive weights. The experiments supply a finite ceiling. No value of $K$ has been established for all integers.

Pang’s PAL v2.4 frame and RPL old/detail distinction suggested restricting the observation to newly arrived marks and then turning the comparison around. Hearthline derived the window tests, return costs, single-unit source and width argument in Pang’s constructive program. [Corpus routes and attribution](../pal-rh/CORPUS-ROUTES.md)
