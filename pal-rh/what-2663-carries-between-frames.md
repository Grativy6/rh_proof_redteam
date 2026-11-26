# What 2663 carries between frames

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). Pang suggested the prime 2663 and asked us to try the direction both ways. His retained-frame question has an exact test on the first-pass marks.

Choose an ordinary prime $p>3$ and integers $d$ whose rough part is coprime to $p$. Write $a(v^2s)=v\mu(s)$ for the mark at $d=v^2s$ with $v=2^i3^j$ and $(s,6)=1$. Multiplying $d$ by $p$ reverses the mark, $a(pd)=-a(d)$. Multiplying the measuring head by the same $p$ leaves the point price fixed. The quotient is unchanged, the remainder scales by $p$, and the numerator and denominator in $G$ both scale by $p^4$. The window potential has one power of length left, so $E(pT,pd)=pE(T,d)$. In particular the signed point contribution really reverses. This calculation compares exactly the same set of inputs through a dilation.

## Four cofactor groups in a fourth-power block

Use $1100^4<n\le1101^4$ and the common integer head $T=1{,}807{,}529{,}451{,}605$, divisible by both 577 and 2663. Every $n$ in the block has $4/5<n/T<5/6$, so its point price is positive. For each row take all physical integers $n=c\,r_S q$ in the block, where $c=v^2u$, $r_S$ is any squarefree product of primes from 5 through 347, and $q$ is a prime exceeding 347 and each prime factor of $u$. The largest factor and the selected small primes therefore identify the row uniquely. Here $c\le(1100^4)^{21/50}$ in all four rows.

We stripped and factored every possible quotient $n/c$ in this interval and counted **every** small-factor multiplicity. We then used the two five-moment allocations in the [moving-head proof](how-much-can-travel-with-a-prime.md). Bounds on each moment were taken directly at every occupied integer label with outward rounding to $10^{-15}$ before summation. The exact residual constant moment counts signed marks, including the factor $v$.

| $c$ | $v$ | $u$ | Counts at sizes $0,1,2,3,4,5$ of $S$ | Signed marks left | Signed point contribution |
| ---: | ---: | --- | --- | ---: | ---: |
| 11,664 | 108 | 1 | 24,543 · 35,793 · 26,118 · 11,168 · 1,437 · 17 | −552,960 | −12,685.38603 to −12,685.38602 |
| 9,232 | 4 | 577 | 30,563 · 44,601 · 32,266 · 13,306 · 1,487 · 17 | +25,568 | +586.56657 to +586.56658 |
| 10,652 | 2 | 2663 | 26,671 · 38,961 · 28,047 · 8,116 · 367 · 0 | +16,016 | +367.27849 to +367.27850 |
| 123,197 | 1 | $349\cdot353$ | 2,674 · 4,027 · 2,969 · 809 · 23 · 0 | −830 | −19.06733 to −19.06732 |

For the 2663 row, divide every physical label and the head by 2663. The earlier integer head is **678,756,835**. On the corresponding preimage labels, with the same fractions, the contribution lies between **−367.27850 and −367.27849**. Restoring 2663 gives the positive interval in the table. Dividing out 577 similarly gives a head of 3,132,633,365. This is a direct change of arithmetic sign at fixed relative geometry.

## Can one cofactor actually pay for another?

All four rows occupy the same physical block, so they can be compared on the same five functions of $n$. For each row the remaining magnitude in each bin is a known fraction of the original column of even tags of size at least two. Its total five moments equal the difference between the complete even and odd columns. This lets us check every new allocation against the capacity still available.

1. Use a further portion of the 577 row to cover the entire negative remainder of $u=349\cdot353$. The new fractions range from 0.33% to 1.11% of the **original** even-tag column in the respective bins. At least 16.25% of each original bin remains available after both uses.
2. Cover the rest of the 577 row and the entire 2663 row using the $u=1$ row. The five target moments now equal the sum of the original 577 and 2663 surplus magnitudes less the $349\cdot353$ surplus magnitude. The new fractions range from 1.25% to 1.56% of the original even-tag bins in the $u=1$ row. At least 11.00% remains in every bin after both uses.

The combined residual across these four groups is now supported entirely on $u=1$, with **−512,206** signed marks. Its point contribution lies between **−11,750.60830 and −11,750.60826**. Every redistribution annihilates all five price moments. The same allocations preserve the readings at other heads for which the whole block shares an active quotient. [Termwise arithmetic and capacity replay](../receipt-archives/check_pal_cofactor_block.py) · [Full bounds](../receipt-archives/2026-11-25-pal-cell-prices.json)

For any finite list of fixed cofactors in the moving-head theorem, the residual bin matrix for $v^2u$ divided by $L/\log Y$ tends to $[v/c]\prod_{r\in\mathcal R}(1-1/r)$ times the common Bernstein integral matrix. This follows by multiplying the matrix for the even tags of size at least two by their unspent bin fractions, whose limiting value is common to all five bins. Hence if the two orientation totals $\sum v/c$ differ, all residual groups with the smaller total can be covered by bin fractions of those with the larger total on every sufficiently large block. Their limiting fraction is the ratio of the two totals. For the four displayed cofactors the two-step ordering also follows in the limit from $1/(349\cdot353)<1/(4\cdot577)$ and $1/(4\cdot577)+1/(2\cdot2663)-1/(349\cdot353)<1/108$.

The fixed-list calculation leaves the sign of a growing list of cofactors as an arithmetic question. The [integer sign rule](../proofs/where-an-integer-label-can-go-quiet.md) gives the exact intervals where either sign costs the construction.
