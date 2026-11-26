# Which window pays for the return?

Christopher Daniel Pang and Hearthline, 26 November 2026 (New York). The [adaptive-row proof](../proofs/how-far-a-square-mark-must-reach.md) allows the starting point to change at every integer. This calculation identifies an amount of the necessary price on the actual signed labels of the chosen window.

## The same constant appears twice

At head $t$ choose $0\le\alpha<1$ and put
$$
 w_\alpha(u)=\frac{u-\alpha}{1-\alpha}\quad(\alpha\le u\le1),
$$
zero elsewhere. The raw signed reading is $W_\alpha(t)=\sum_{n\le t}a(n)w_\alpha(n/t)$. At an integer $t$ with integer $\alpha t$ it equals $T(t,(1-\alpha)t)/[(1-\alpha)t]$. It charges one whole copy of the newest mark and an increasing fraction of each preceding mark.

Let $P(t)=M(t)/\sqrt t$ and remove the endpoint term in finite summation by parts, or integrate the step function $M$ on the interval. The exact formula for any real $t>0$ is
$$
 P(t)=\frac{W_\alpha(t)}{\sqrt t}
       +\frac1{1-\alpha}\int_\alpha^1 \sqrt u\,P(tu)\,du .
$$
Values below one are zero. The average of the older normalized heights has total coefficient $1-I_\alpha$, where
$$
 I_\alpha=1-\frac1{1-\alpha}\int_\alpha^1\sqrt u\,du
 =\frac{(1-\sqrt\alpha)(1+2\sqrt\alpha)}{3(1+\sqrt\alpha)}
 =\frac12\int_\alpha^1w_\alpha(u)\,\frac{du}{\sqrt u}.
$$
In particular $(1-\alpha)/4\le I_\alpha\le(1-\alpha)/3$. The last equality follows by integration by parts and explains the agreement of the two costs. More generally it is $1-\int \sqrt u\,dw(u)=\tfrac12\int_0^1 w(u)du/\sqrt u$ when the increasing window profile ends at one, with $dw$ taken up to that endpoint.

At a positive record of $P$ up to $t$, every older height is at most its current value. The chosen row must therefore show at least $I_\alpha M(t)$. This works for any choice of $\alpha$ at that head. The discrete proof describes the closely related integer barrier and does not require integrating on the computer.

## Take a fraction only inside that window

Write $m(d)=\mu(d)\mathbf1_{(d,6)=1}$, $v=2^i3^j$, $y=t/v^2$, $h=\log4$ and $\ell=\log9$. On the rough seed put $V_\alpha(y)=\sum_{d\le y}m(d)w_\alpha(d/y)$. Then $W_\alpha(t)=\sum_{v^2\le t}vV_\alpha(t/v^2)$. In each row with $1\le y\le K$, take the fraction $k(K/y)/c$ of its existing marked window, where
$$
 k(x)=\frac{\lfloor x\rfloor}{\sqrt x}-\frac12\sum_{r\le x}r^{-1/2},
 \qquad c=-\zeta(1/2)/2 .
$$
The previous arithmetic bounds give $0\le k/c\le1$ and $k=0$ below one. Thus the signed portion $P_{\alpha,K}(t)$ is obtained from specified fractions of the original marks in this very interval. [Divisor weight and smooth-row transfer](where-the-negative-running-mass-comes-from.md)

The ordinary divisor sum of $m$ is the indicator of a smooth integer. Hence $S_\alpha(x)=\sum_{r\le x}V_\alpha(x/r)=\sum_{s\le x,\ s\ {\rm smooth}} w_\alpha(s/x)$ is nonnegative. Expanding $k$ and changing variables gives
$$
 D_\alpha(K)=\int_1^K V_\alpha(y)k(K/y)y^{-3/2}\,dy
 =K^{-1/2}\int_1^K S_\alpha(x)\frac{dx}{x}
 -\frac12\int_1^K S_\alpha(x)\frac{dx}{x^{3/2}}.
$$
Over the entire positive half-line the second integral, including its factor $1/2$, equals $E I_\alpha$, where
$E=\sum_{s\ {\rm smooth}}s^{-1/2}=[(1-2^{-1/2})(1-3^{-1/2})]^{-1}$.
This is precisely the same $I_\alpha$ that prices recovery of the full height.

Uniformly for $1/2\le\alpha<1$,
$$
 |D_\alpha(K)+E I_\alpha|\ \ll\
 I_\alpha\,\frac{(1+\log K)^2}{\sqrt K}.
$$
Indeed the contribution to the first integral from each $s\le K$ is at most $\int_\alpha^1w_\alpha(u)du/u\le2\sqrt2 I_\alpha$, with $O((1+\log K)^2)$ possible smooth $s$. The tail of the second integral comes only from $s\ge K/2$, and it costs at most $I_\alpha\sum_{s\ge K/2}s^{-1/2}$. A dyadic interval $[z,2z]$ contains $O(1+\log z)$ smooth integers by fixing the power of three. This bounds the tail by $O(I_\alpha(1+\log K)/\sqrt K)$.

## The width may shrink at every head

For $L=\log t$ periodize $e^{-z/2}V_\alpha(e^z) k(K/e^z)/c$ on $0\le z\le\log K$, zero outside. Before summing over $d$, each window term jumps once from zero to one at $e^z=d$ and decreases to zero. It has variation at most two independently of the width. Consequently $\|V_\alpha\|_\infty$ and its variation through $K$ are $O(K)$, and the periodized product has variation $O(K^{3/2})$. The variation of $k$ is $O(\sqrt K)$ here. The earlier integer-separation proof bounds discrepancy of the $\ell/h$ rotation in $O(L)$ complete rows by $O(1/\log(2+L))$. The incomplete end rows cost $O(K(1+\log K)^2/L)$ after normalization. This gives
$$
 \frac{P_{\alpha,K}(t)}{\sqrt t\log t}
 =\frac{D_\alpha(K)}{ch\ell}
 +O\left(\frac{K^{3/2}}{\log(2+L)}
          +\frac{K(1+\log K)^2}{L}\right).
$$

For example, set $Q=\log(3+\log t)$ and $K(t)=\max(10^6,Q^{1/8})$. At *every* sufficiently late head one may choose any $1/2\le\alpha(t)<1$ with $1-\alpha(t)\ge Q^{-1/2}$. The estimates above give the same limit uniformly over those choices:
$$
 \boxed{\displaystyle \frac{P_{\alpha(t),K(t)}(t)}
                 {I_{\alpha(t)}\sqrt t\log t}
   \longrightarrow-\frac{E}{c\log4\log9}
   =-3.6320505\ldots .}
$$
Shrinking the width reduces the negative amount that has been identified. It also reduces the signed amount that the row needs to show at a record, at exactly the same first-order price. If the unassigned part at one such selectable width per late integer is at most $(E/(ch\ell)-\epsilon) I_\alpha\sqrt t\log t$, the row is eventually nonpositive. The fixed integer sign implication applies when $\alpha t$ is an integer. The theorem above allows those integer endpoints.

## How the two orientations behave on the same data

The complementary window assigns weight $1-w_\alpha$ on the same included labels. The two readings add to $M(t)-M(\alpha t)$. The table gives signed values rounded to the nearest integer. The divisor-selected fraction here has $K=10^6$. The first two columns use two independent exact quotient recurrences on the full stream.

| Head | Earlier endpoint | Newest-weighted | Oldest-weighted | Selected part of newest-weighted |
| ---: | ---: | ---: | ---: | ---: |
| 10,000,000,000,000 | 5,000,000,000,000 | −40,433,883 | −43,506,678 | −38,724,423 |
| 2,500,000,000,000 | 2,000,000,000,000 | −6,198,234 | −5,609,032 | −6,299,063 |
| 156,250,000,000 | 153,846,153,846 | +120,240 | +7,742 | +130,681 |
| 39,062,500,000 | 38,910,505,836 | +32,448 | −5,329 | +32,927 |

The last row pays opposite signs on the very same half-open interval. The growing-cutoff limit does not assert negativity at these particular heads. [Arithmetic and fixed-target records](../receipt-archives/2026-11-26-pal-trailing-rows.json)

## Unresolved

The unassigned parts retain the signed rough Möbius marks at their original labels. Locating a sufficiently cheap width uniformly at every late head is the remaining mathematical obligation.
