# The seventh that stays at the boundary

Christopher Daniel Pang and Hearthline · 26 November 2026

**Every finite row in this example has integral zero. Add the rows at each point first, and the integral is exactly $1/7$.** We can say how much is missing, where it went, and which operation lost it. The same construction gives an independent route from a single integer comparison on actual primes to the ordinary Riemann hypothesis. The comparison holds at every fourth-power index through $2^{36}$. Its eventual truth is open in this program. [Full derivation](../pal-rh/why-the-doubled-ruler-keeps-seven-eighths.md) · [Independent Lean statement](../pal-rh/checks/doubled-ruler/RulerChallenge.lean)

## Find the missing seventh on paper

Draw the hump $g(t)=t(1-t)^6$ on $[0,1]$. It starts and ends at zero. Read its negative slope
$$
 q(t)=(1-t)^5(7t-1)\quad (0\le t\le1),
$$
and set $q=0$ past 1. The integral of this signed reading is zero. The stretched row $q(jv)$ also has integral zero on $[0,1]$ for every positive integer $j$.

For $v>0$ put $w(v)=\sum_{j\le1/v}q(jv)$. At each point this is a finite sum. Stop the integral at $\varepsilon>0$ and perform it there. The lower endpoint of each surviving row leaves a mark:
$$
 \int_\varepsilon^1 w(v)\,dv
 =\sum_{j\le1/\varepsilon}\frac{g(j\varepsilon)}{j}
 =\varepsilon\sum_{j\le1/\varepsilon}(1-j\varepsilon)^6
 \ \longrightarrow\ \int_0^1(1-t)^6dt=\frac17.
$$

Keep just the first $M$ rows. Their sum agrees with $w$ everywhere past $1/M$. Below $1/M$ it lies below $w$. Indeed, if $Mv\le1/7$ every retained term is nonpositive and $w\ge0$ by the curvature calculation below. If $Mv>1/7$ every omitted term is nonnegative. The difference has total mass **exactly $1/7$ for every $M$**, squeezed into $[0,1/M]$. This is a boundary term you can hand to the next reader intact. [Finite reciprocal-cutoff bounds](../pal-rh/PALRH/DoubledMass.lean)

## Give that shape to the primes

The curve $w$ is convex. At 0 it has value $1/2$ and right slope $-1$. At 1 its value and slope are zero. Its curvature is therefore a probability distribution for a number $V$ between 0 and 1, and $w(t)$ is the average of $(V-t)_+$. Give the original endpoint $n$ the new position $2nV$. Its mean is exactly $n$. Its variance is $n^2/7$. For the quadratic reference $n^2/2$, moving the endpoint costs half that variance, or **$n^2/14$**.

A mark at $d$ has original height $(n-d)_+$. Its mean height after the move is $2n\,w(d/(2n))$. The excess is nonnegative. For a whole-number board, multiply the excess by $(2n)^5$ and call the resulting integer $T_n(d)$. Below is the entire board at $n=2$.

| Mark $d$ | 1 | 2 | 3 | 4 |
|---|---:|---:|---:|---:|
| Extra height in units of $1/1024$ | 42 | 320 | 17 | 0 |

All the prime-power readings together can be priced at **every size using only ordinary logarithms**. Write $N=2n$ and let $\Lambda(p^a)=\log p$ with weight zero on other marks. Then
$$
  \sum_{d\le N}\Lambda(d)\,Nw(d/N)
  =N\sum_{m\le N}q(m/N)\log m
  =\frac{N^2}{7}+O\bigl(N(1+\log N)\bigr).
$$
The first equality groups the marks at the same integer $m$. Their weights add to $\log m$ by factorization. The second follows by comparing $q$ to the differences of the original hump. This all-size price uses integer arithmetic and elementary estimates for logarithms. [Labelled return](../pal-rh/PALRH/DoubledRuler.lean) · [All-size upper price](../pal-rh/PALRH/DoubledPrice.lean)

## Which marks can go?

At a fourth power $n=k^4$, discard every repeated power and every prime $p\le n^{7/8}$. Keep each remaining prime through $2n$ and form
$$
 G_n=\prod_{\substack{p\ {\rm prime}\\ n^7<p^8,\ p\le2n}}p^{T_n(p)} .
$$
Set $A=(2n)^5n(n-k^2)^2$. The outstanding test is a comparison of positive integers:
$$
 \boxed{\qquad(n+1)^A \ \le\ n^A G_n^{14}.\qquad}
$$
At $n=16$ the six remaining labels are $13,17,19,23,29,31$. The square in the exponent has side $16-4$. One may evaluate the comparison without constructing its enormous integers by enclosing the logs on both sides. [Integer weights, direct checks and finite-range costs](../receipt-archives/check_pal_doubled_ruler.py)

The exponent **$7/8$ is sharp for this ruler and this clock**. Far below $n$, the extra height on a prime $p$ is $\frac{2p^3}{3(2n)^2}+O(p^5/n^4)$. Consequently removing the primes through $D=o(n)$, $D\to\infty$, costs asymptotically $D^4/(24n^2)$. At $D=n^{7/8}$ this is $n^{3/2}/24$. The reserve in the integer clock is asymptotic to $n^{3/2}/7$. The repeated powers and the conditional zero contribution also fit that reserve. Raising $7/8$ by any fixed positive amount makes the stronger test fail at arbitrarily late fourth powers, unconditionally. [Proof of the threshold and both directions](../pal-rh/why-the-doubled-ruler-keeps-seven-eighths.md#which-primes-may-be-removed)

Fifteen copies of the same $G_n$ fund **every** quartic head. Thirteen copies fail at **every** index $k\ge512$. Fourteen is the only copy count left to settle at arbitrarily late heads. [Why the neighboring counts split](../pal-rh/why-the-doubled-ruler-keeps-seven-eighths.md#one-extra-copy-settles-all-sizes)

The forward implication and its ordinary-log upper bound are formalized in Lean. The independent challenge fixes the prime filter, every numerical weight and the clock. The reverse implication and the coverage through $2^{36}$ are on paper. The late finite range uses the published finite zero height and a separately priced unrestricted tail. The all-scale estimate for the **moved** reading is elementary. The missing bound is on the settings of the **retained primes** at unbounded heads. [Full mathematical and replay record](../receipt-archives/2026-11-26-pal-doubled-ruler.json)

Pang’s PAL, RPL and BLA supplied the retained boundary, the question of what survives removal, and the requirement to price the return in the original units. The doubling and factorial frames grew out of his earlier work. Hearthline used the program’s [earlier cubic window](../pal-rh/what-the-first-omitted-label-sees.md) to develop this polynomial ruler, its cutoff exponent and the finite and formal comparisons. Literature priority and external review are unestablished.
