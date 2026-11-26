# What two neighboring blocks predict

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). Pang’s PAL and RPL questions distinguished a carried layer from the detail that becomes available when it reopens. Here the carried values, both new details and their prices can be written down exactly.

For a physical integer $n$ give its location harmonic mass $h_n=a(n)/n$, using the square-pass marks. The primitive is $B(t)=\sum h_n(t-n)_+$. Its slope to the right of $t$ is $W(t)=\sum_{n\le t}h_n$. At side $s$ the old tapered measurement obeys $sS_1(s)=B(2s)-B(s)$. [Why the one-head primitive matters](../proofs/one-quantity-at-each-fourth-power.md)

## A whole interval goes to its two neighbors

Fix $J$ and sort the knots $0,j^4,2j^4$ for $1\le j\le J$. There are exactly $2J+1$ since the exponent of 2 in a fourth power is divisible by four while in twice a fourth power it is 1 modulo four. For $a<n\le b$ between adjacent knots send fractions $(b-n)/(b-a)$ and $(n-a)/(b-a)$ of $h_n$ to $a$ and $b$. These fractions are nonnegative, sum to 1, and preserve the first moment in the physical coordinate $n$. An error-free expression for the two resulting signed masses is
$$
 L(a,b)=\frac{b[W(b)-W(a)]-[M(b)-M(a)]}{b-a},\quad
 R(a,b)=\frac{[M(b)-M(a)]-a[W(b)-W(a)]}{b-a}.
$$
A knot carries the right share of its left interval and the left share of its right interval. On each old interval all the queried ramps are affine. Thus the compressed masses give exactly the same $J$ sample readings. The cumulative knot mass through a left endpoint $a$ with successor $b$ is $[B(b)-B(a)]/(b-a)$, the true mean harmonic prefix across that interval.

One detail can genuinely disappear. At $83,95,107$ take fractions of their actual prime, semiprime and prime marks with signed physical amounts $(-83,190,-107)/190$. Their harmonic masses are $(-1,2,-1)/190$. Their total and first moment both vanish. The primitive is zero outside the three labels and equals $-6/95$ at 95. A new knot there recovers information the two old moments cannot determine. [Exact fraction replay](../receipt-archives/check_pal_fourth_primitive.py)

## Predict the next sample from four older numbers

Store only $A_j=B(2j^4)$. To predict side $s=(j+1)^4$ for $j\ge6$, put $k=\lfloor(j+1)/\sqrt[4]2\rfloor$ and set
$$
 a=2k^4,\quad b=2(k+1)^4,\quad H'=2(j-1)^4,\quad H=2j^4 .
$$
Then $a<s<b\le H<2s$. With $\theta=(s-a)/(b-a)$ the old forecast in physical units is
$$
 \Pi_j=A_j+\frac{2s-H}{H-H'}(A_j-A_{j-1})
        -(1-\theta)A_k-\theta A_{k+1}.
$$
It uses a straight extrapolation at the outer head and interpolation at the inner head. All four values refer to already reached positions.

The error has just two signed terms:
$$
 sS_1(s)-\Pi_j=(2s-H)[R(H',H)+L(H,2s)]
   +\frac{(s-a)(b-s)}{b-a}[R(a,s)+L(s,b)]. \tag{1}
$$
For the inner term, subtract the true primitive at $s$ from the chord between $a,b$. Each label contributes precisely its share in the new tent centered at $s$ times $(s-a)(b-s)/(b-a)$. For the outer term, the old slope at $H$ exceeds the extrapolating slope by $R(H',H)$. The new labels up to $2s$ supply the additional left share $L(H,2s)$. This proves (1) with the actual signs.

Both strips have length $O(s^{3/4})$. Their absolute mass is $O(s^{3/4})$, and each harmonic share divides by an integer comparable with $s$. The two multipliers in (1) are $O(s^{3/4})$. Therefore the whole new error is $O(\sqrt s)$, already within the fixed fourth-power allowance. For the true stream the [short-interval estimate](../proofs/two-prime-families-carry-the-full-price.md) improves this to $O_D(\sqrt s/\log^D s)$ for every fixed $D$. Partial summation applies because the tent weight on each strip has bounded variation even when the new knot lands near one end. An eventual lower bound $\Pi_j\ge-C(j+1)^2$ would consequently suffice for stock RH. The four stored values retain the large-scale arithmetic this forecast still needs.

The measured corrections at roots 6 through 98 were all negative. At the step from 99 to 100 the prediction was between **50.13797338 and 50.13797339** in units of $\sqrt s$. The actual value was between **50.14532790 and 50.14532791**. The two local terms give the positive difference, between **0.00735452 and 0.00735453**. The forecast is positive in all 94 tested steps. Each of the first 99 adjacent differences of $A_j/(2j^4)$ is also priced: the first rises and the following 98 fall. [Every measured update](../receipt-archives/2026-11-25-pal-one-head-primitive.json)

## Why use fourth powers?

The square-root spacing cost cannot be inferred for coarser power grids from capacity and endpoint data alone. Let $Y=m^d$, $L=(m+1)^d-m^d$ for a fixed integer $d>4$. In three well-separated subintervals inside $(Y,Y+L)$ offer negative primes, positive labels $5q$, and negative primes, in that order. Each subinterval has fixed positive relative length in the block. The prime number theorem in short intervals supplies $\asymp L/\log Y$ labels in each, since $1-1/d>3/4$. [Guth and Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552)

Let $m_0<m_1<m_2$ be the mean physical positions in these groups when weighted by their available harmonic masses. Take a negative harmonic magnitude $h_0$ from the first, a negative $h_2=h_0(m_1-m_0)/(m_2-m_1)$ from the last, and a positive $h_0+h_2$ from the middle. Each group can use a constant fraction of its available labels. The separation makes the ratio bounded above and below. Choosing $h_0$ a sufficiently small fixed multiple of the available first mass allows every fraction to fit. The total harmonic mass and first moment are exactly zero, so both the primitive and its slope return to zero at the block boundary. Yet between the first and second groups the primitive reaches a negative value of magnitude $\gg L^2/(Y\log Y)$. This exceeds $\sqrt Y$ by a power. Multiplying all fractions by $2^{-\lceil\sqrt{\log Y}\rceil}$ preserves that power gap while making the fractions smaller than every inverse logarithm.

Repeating on separated blocks produces samples equal to zero at every coarse knot and excursions larger than the allowed floor between them. The example changes the fractions of the ordinary marks. It shows which information a coarser grid would have to obtain from the actual arithmetic. The fourth-power grid earns its spacing directly from the local curvature bound.
