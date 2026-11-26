# What can move inside one square-root window?

Christopher Daniel Pang and Hearthline, 26 November 2026 (New York).

At the square of 4,478,976, look back exactly 4,478,976 integers, including the square itself. Their absolute weights add to **8,554,639**. One mark accounts for **4,478,976** of that. Each of the remaining positions contributes 0.909954… in absolute weight on average. Their *signed* contribution, all together, is just **+3,023**.

We can prove why a single large mark stands out at this scale. We can also prove a simpler requirement on the running count. **One adequately low reading anywhere between each pair of consecutive squares would suffice for RH.** The argument pays for every uninspected integer in between.

## The shared-divisor argument

An occupied label is $n=v^2d$, with $v=2^i3^j$, $d$ squarefree and coprime to six. Its signed weight is $v\mu(d)$. Two different labels with smooth roots $v,w$ differ by a multiple of $\gcd(v,w)^2$. If both labels sit in an interval of length $H$, then $\gcd(v,w)\le\sqrt H$.

Take an interval inside $[X-C\sqrt X,X+C\sqrt X]$, with $C$ fixed. Look at roots bigger than $X^{7/16}$. Each can belong to at most one occupied label here. Order them by their exponent at 2. The exponents at 3 must run in the opposite direction, since otherwise the smaller root divides the larger one and its square exceeds the whole interval. For successive roots $2^i3^j,2^{i'}3^{j'}$ with $i<i'$ we have
$$
 2^{i'-i}=\frac{2^{i'}3^{j'}}{\gcd(2^i3^j,2^{i'}3^{j'})}
 \ \gg_C\ X^{3/16}.
$$
Four such roots would require three of these jumps. Their product would exceed $X^{9/16}$ times a fixed positive constant, while the whole power of two cannot exceed $\sqrt{X+C\sqrt X}$. Thus **at most three** such large marks occur, uniformly at sufficiently large heads.

The other roots have total unsigned cost $O_C(\sqrt X)$. At root $v$, at most $H/v^2+1$ labels occur. Sum $H/v$ over the smooth roots using $\sum_v1/v=3$. The rounding part through $V=X^{7/16}$ costs $\sum_{v\le V}v\ll V\log(2V)=o(\sqrt X)$. We have removed the growing logarithm from the previous allowance on *all* the roots, including those above the cutoff. No cancellation of Möbius signs was needed.

The Lean proof uses coarse bins that work from the first head onward. With $Y=2^{6s}$, ambient labels at most $Y^2$ and width at most $Y$, split at $v=2^{4s}$. For the smaller roots $v\sqrt v\le Y$ and $\sum_v1/\sqrt v<12$. For a larger occupied root, its exponent at two belongs to one of seven bins of length $s$ (including the last endpoint). Two different occupied larger roots cannot share a bin by the common-square argument. The resulting bound on even the offered unsigned weight is $31Y$. [Formal packing and interpolation](../pal-rh/PALRH/SquareExposure.lean)

## Which readings would give RH?

Let $M(n)=\sum_{k\le n}a(k)$. An interval $[j^2,(j+1)^2)$ has length $2j+1$. The preceding bound makes the cost of moving between *any* two of its heads $O(j)$ with one absolute constant. Consequently either of these integer conditions suffices.

- Some $K$ satisfies $M(j^2)\le Kj$ for every positive integer $j$.
- Some $K$ allows **at least one** $j^2\le n<(j+1)^2$ with $M(n)\le Kj$ for every $j$.

In either case every head satisfies a one-sided square-root bound. The earlier finite divisor rectangle takes that bound to stock RH. The independent Lean reference states both tests directly with signed integers, powers of 2 and 3, and the ordinary Möbius function. [Fixed statements](../pal-rh/checks/square-contacts/ShellChallenge.lean) · [Proofs of the implications](../pal-rh/checks/square-contacts/ShellSolution.lean) · [Positive-upper-bound transfer](how-much-can-the-newest-half-gain.md)

At roots 5 and 6 the square readings are +1 and +4. Within their same intervals, the count reaches −3 at 31 and −5 at 47. The optimal natural $K$ on the tested prefix is **2** using squares alone and **1** using selectable contacts. Our previous direct sign result extends that statement through root **165,450**. Adding the published finite Mertens estimate used in the earlier work extends it through root **3,162,277**. [Source ranges](the-integer-that-turns-at-forty-four.md) · [Complete records](../receipt-archives/2026-11-26-pal-square-exposure.json)

## The background and the mark it carries

There is a sharper paper result. Let $\kappa=9/\pi^2$. Throughout a bounded square-root neighborhood $[X-C\sqrt X,X+C\sqrt X]$, choose a label $n_X$ with the largest absolute mark, if any. Uniformly for every half-open subinterval $I$ of that neighborhood,
$$
 \sum_{n\in I}|a(n)|
 =\kappa |I|+|a(n_X)|\mathbf1_{n_X\in I}
   +O_C\!\left(\sqrt X\,\frac{(\log\log X)^2}{\log X}\right)
 \quad (X\to\infty).
$$
The same $n_X$ serves all the subintervals. The density and the bound with up to three explicit large labels have elementary proofs. Reducing the exceptional set to one uses Matveev’s lower bound for linear forms in logarithms. The [derivation](../pal-rh/the-background-around-one-large-mark.md) identifies the precise use of that theorem.

In particular, in an interval of length $o(\sqrt X)$ the signed change, divided by $\sqrt X$, can have only the following limits:
$$
 \{0\}\ \cup\ \{\mu(d)/\sqrt d:\ d\text{ squarefree},\ (d,6)=1\}.
$$
All those values occur. A surviving mark with bounded cofactor $d$ has exactly that normalized height and sign. Cofactors going to infinity give height zero. For the converse take a single mark at $4^k d$, and for zero take an integer with odd exponent at 2. The largest upward limiting jump is **1**, and the largest downward magnitude is **$1/\sqrt5$**.

Moving the observer can place such a mark anywhere on the local coordinate. It cannot give a mark from cofactor 5 the size or the sign of a mark from cofactor 1. On a full square-root interval the unsigned background also remains. Its *signed* balance at exceptional heads is an open part of the construction.

Two native computations counted the same 98 windows. One factors every label. The other counts squarefree rough cofactors by Möbius inversion on their square divisors. A separate exact search through $10^{28}$ found 131,938 labels satisfying $v>n^{7/16}$ and no pair simultaneously above the later cutoff within a square-root distance. The three-mark proof and the one-mark asymptotic apply across unbounded scales independently of that search. [Native arithmetic](../receipt-archives/square_shell_mass.cpp) · [Finite reconstruction](../receipt-archives/check_pal_square_exposure.py)

Pang’s PAL retained marks, RPL’s distinction between an owner and its detail, and BLA’s instruction to keep the accounting boundary fixed suggested comparing the *same* physical window before and after its largest mark is removed. Hearthline derived the packing, contact criterion and local profile in Pang’s constructive program. [Corpus and derivation credits](PROVENANCE.md)

## Unresolved

We can pay for the space between square readings. The remaining requirement is a uniform upper allowance at one actual reading per square interval. The local profile identifies all possible concentrated jumps and leaves a signed background whose total across many intervals still needs control.
