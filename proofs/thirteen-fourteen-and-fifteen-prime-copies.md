# Thirteen, fourteen and fifteen copies of the same prime product

Christopher Daniel Pang and Hearthline · 26 November 2026

Keep the clock and the prime dials fixed. Change only how many copies of the dials can pay. For $n=k^4$, put $N=2n$, let $G_n$ be the product on the actual primes $n^{7/8}<p\le2n$ with the integer exponents of the [doubled ruler](one-seventh-at-the-boundary.md), and set $A=N^5n(n-k^2)^2$. Write “$b$ pays” for
$$
 (n+1)^A\ \le\ n^A G_n^b .
$$

**Thirteen fails at every $k\ge512$. Fifteen pays at every $k\ge 200000^2=40{,}000{,}000{,}000$. Lean now proves both unconditionally using ordinary integer divisibility and elementary logarithm bounds.** The [earlier finite proof](../pal-rh/why-the-doubled-ruler-keeps-seven-eighths.md#every-fourth-power-through-index-236) already funds fourteen through $2^{36}=68{,}719{,}476{,}736$, including the overlap. Together these prove fifteen pays at every positive index. At $k\ge512$ the minimum is either 14 or 15. Eventual payment at 14 is equivalent on paper to ordinary RH and is still open in this program. [Independent statements of the neighboring counts and the RH implication](../pal-rh/checks/prime-copies/CopiesChallenge.lean) · [Submitted proofs](../pal-rh/checks/prime-copies/CopiesSolution.lean)

## Sixteen rows you can check

At address $k$, visits to multiples of $j$ have total remaining distance
$$
 P_j(k)=\sum_{\ell\le k/j}(k-j\ell).
$$
Write $r=k\bmod j$. Adding that finite arithmetic progression gives
$$
 2j P_j(k)=k^2-jk+r(j-r).
$$
Use the following signed weights. Each row sums to zero, so the shared $k^2$ term cancels exactly.

| $j$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Upper $c_j$, scale 102 | 102 | −51 | −34 | 0 | −20 | 17 | −15 | 1 | 0 | 8 | −8 | 0 | 0 | 4 | −1 | −3 |
| Lower $c_j$, scale 198 | −198 | 99 | 66 | 0 | 40 | −29 | 21 | 3 | 0 | −9 | 0 | 7 | 11 | −8 | −6 | 3 |

Let $(s,D)=(1,102)$ or $(-1,198)$ for the corresponding row. For **every** integer $k\ge1$,
$$
 \sum_{j=1}^{16}j c_j P_j(k)\ \ge\ sD(k-1). \tag{1}
$$
Direct integer arithmetic covers $1\le k\le200$. For larger $k$, each $r(j-r)$ lies between zero and $j^2/4$. After doubling (1), the excess is at least
$$
 k\left(-\sum j c_j-2sD\right)+2sD-\tfrac14\sum |c_j| j^2.
$$
For the upper row this line has slope 8 and starts at 295 when $k=201$. For the signed lower row it has slope 18 and starts at $245.5$. This handles the unbounded part of the address check. The coefficients were found by a finite linear optimization followed by integer rounding and exact tests. The proof consists of the displayed numbers, the first 200 comparisons, and the two increasing lines. [Complete integer replay](../receipt-archives/check_pal_divisor_brackets.py) · [Kernel proof of the address inequalities](../pal-rh/PALRH/DivisorBracket.lean)

For a physical label $d\le n$, the needed address is $n/d$. Between consecutive integers $k$ and $k+1$, each $(x-j\ell)_+$ is affine in $x$. The new term at an endpoint has height zero. Thus (1) holds at that intermediate address by interpolation, with the exact remainder $n\bmod d$ retained.

## How the rows reach the primes

Multiply the inequality at $n/d$ by $d\Lambda(d)$ and add. Grouping the product $d\ell=m$ gives $\sum_{d\mid m}\Lambda(d)=\log m$. For $I_\psi(n)=\sum_{d\le n}(n-d)\Lambda(d)$ we obtain
$$
 sD I_\psi(n)\le
 \sum_{j=1}^{16} j c_j\sum_{m\le n/j}(n-jm)\log m. \tag{2}
$$
The right side has an ordinary-integer price. At each endpoint $v$, $j\lfloor v/j\rfloor-v=-(v\bmod j)$. Summation by parts therefore bounds the difference between a $j$-spaced sample of $(n-v)\log v$, with weight $j$, and its full integer sum. It costs at most $2jn\log(n+1)$ because the total variation of that function on the integer grid is at most $2n\log(n+1)$. Replacing $\log(jm)$ by $\log m$ also subtracts $\log j$ times the sampled sum of the linear ramps. The exact arithmetic progression above puts that latter sum within $jn$ of $n^2/2$. When we add the rows, their common ordinary sum drops out because $\sum c_j=0$. Thus for $n\ge16$ the right side of (2) differs from $-\frac12 n^2\sum c_j\log j$ by at most
$$
 3n\log(n+1)\sum j|c_j| .
$$
Both factorial-scale contributions and their signs stay attached to the same $n$. [Sampling and divisor transfer](../pal-rh/PALRH/DivisorEconomy.lean)

The upper leading coefficient after division by 102 is $0.50379142\ldots$. The signed lower row gives $0.49619050\ldots$ after reversing its sign and dividing by 198. In Lean an integer-power comparison with powers of two and the elementary bounds for $\log2$ suffice to enclose them. This proves the unconditional all-size inequalities
$$
 \frac{62}{125}n^2-32n\log(n+1)\ \le\ I_\psi(n)\
 \le\ \frac{63}{125}n^2+32n\log(n+1) \qquad(n\ge16). \tag{3}
$$
No input about zeta zeros or prime-count tables enters this bracket. The two constants stop on opposite sides of $1/2$. [Full formal inequality](../pal-rh/PALRH/AreaBracket.lean)

## Why this separates the neighboring copy counts

The moved reading $F_{2n}$ of the doubled ruler costs $4n^2/7+O(n\log n)$ by elementary quadrature. Its total returned height is exactly $F_{2n}-I_\psi(n)$. For the upper bound on the retained prime product, all dropped heights are nonnegative. For its lower bound, each height after the common denominator is removed is at most $14n$. Once $k\ge200000^2$, the condition $d^8\le n^7$ implies $200000d\le n$ by raising to the eighth power. The elementary Chebyshev bounds in stock Mathlib give $\psi(n/200000)\le6n/200000$ for the initial integer segment and $\psi(2n)-\theta(2n)\le2\sqrt{2n}\log(2n)$ for repeated powers. All those debits are accounted for even with overlap. [Formal omission bounds](../pal-rh/PALRH/RulerOmissions.lean)

Divide log prices by $(2n)^5$. Thirteen times the upper bound has leading coefficient $13(4/7-62/125)<1$. Fifteen times the lower bound has leading coefficient at least $15(4/7-63/125-84/200000)>1$. The clock has leading coefficient 1. The formal proof uses $\log(2k^4+1)\le8k$, the explicit quadrature error and the exact square frame to obtain the stated thresholds. [Upper and lower clock comparisons](../pal-rh/PALRH/PrimeCopies.lean) · [Lower ordinary-log price](../pal-rh/PALRH/RulerFloor.lean)

## Where fourteen escapes a fixed row

Suppose a finite upper row supported at $j\le M$ enclosed the original ramp perfectly at every address. Write $E(k)=\sum j c_jP_j(k)-D(k-1)\ge0$. At $k=2$ the upper condition forces $c_1\ge D$. At a prime $p>M$, the second difference of the ramp at $p$ includes only $j=1$ among the available divisors. Therefore
$$
 E(p-1)-2E(p)+E(p+1)=c_1\ge D\qquad(p\ge3).
$$
At least one neighboring address has excess at least $D/2$. For our upper row the excesses at 16, 17, 18 are 102, 1 and 2. Their second difference is exactly 102. Thus every finite upper row of this type leaves positive area somewhere. In reciprocal coordinates its normalized error is affine on each neighboring cell, so a strictly positive endpoint has positive integrated cost. One fixed row cannot erase the leading slack merely by extending its numerical check.

For changing rows the square-root target has a concrete numerical price. If an upper row has leading coefficient $1/2+\delta$ after normalization and $J=\sum j|c_j|/D$, it gives
$$
 I_\psi(n)-n^2/2\le\delta n^2+3J n\log(n+1)
$$
at heads at least the support size. Smaller $\delta$ helps only if the price of the same row is controlled. The uniform rate across growing rows is the remaining question for this approach.

Pang’s ordered ledger, retained residues and change-of-frame test supplied the construction questions. Hearthline found the signed integrated rows and developed their interpolation, ordinary sampling price and stock Lean deductions. Finite residue methods in elementary prime estimates have a long history. Diamond and Erdős obtain arbitrarily sharp fixed asymptotic bounds for the ordinary prime count from finite Möbius data, using a different function and a separate existence argument. Their theorem is historical context for these particular integrated rows. [Diamond and Erdős, *On sharp elementary prime number estimates*](https://www.renyi.hu/~p_erdos/1981-11.pdf) · [Source and verification record](../receipt-archives/2026-11-26-pal-prime-copies.json)

## Unresolved

The independently fixed submission has two unconditional neighboring-count conclusions and a conditional implication at fourteen. Whether every sufficiently late head pays with fourteen copies remains open here.
