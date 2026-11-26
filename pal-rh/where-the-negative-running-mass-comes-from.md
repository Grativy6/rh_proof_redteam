# Where the negative running mass comes from

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). The [integer sign test](../proofs/the-integer-that-turns-at-forty-four.md) needs negative mass to outweigh positive mass at late heads. A part of this negative contribution can be identified unconditionally, using a fraction of each actual square-pass row and a cofactor range tending to infinity.

Write $m(d)=\mu(d)\mathbf1_{(d,6)=1}$ and $M_0(y)=\sum_{d\le y}m(d)$. For smooth $v=2^i3^j$ the full physical count is $M_a(t)=\sum_{v^2\le t}vM_0(t/v^2)$. The row $v$ is determined by the valuations at 2 and 3 of each occupied physical label. Spending a fraction of a row thus spends that same fraction of each of its original signed marks exactly once.

## A counted square-root weight

For $z\ge1$ set $k(z)=\lfloor z\rfloor/\sqrt z-\tfrac12\sum_{n\le z}n^{-1/2}$ and set it to zero for $z<1$. At an integer $n$, write $c_n=k(n)$. Then
$$
 c_{n+1}-c_n=\frac{1}{2\sqrt{n+1}(\sqrt{n+1}+\sqrt n)^2}.
$$
So $c_n$ increases to a finite $c$. Within its unit cell, $k(z)\le c_n$. The positive lower bound $1/\sqrt2-1/2$ and the estimate $0\le c-k(z)\ll1/\sqrt z$ follow from the same floor formula and the summable increments. If $\eta$ denotes the alternating zeta series, then $\eta(1/2)=\lim_n[H_{2n}^{(1/2)}-\sqrt2 H_n^{(1/2)}]=2(\sqrt2-1)c$, where $H_n^{(1/2)}=\sum_{r\le n}1/\sqrt r$. In particular $c=-\zeta(1/2)/2$.

Choose a cutoff $K\ge1$. On a row with $y=t/v^2$ spend the fraction $k(K/y)/c$ if $1\le y\le K$, and zero otherwise. It is always in $[0,1]$. For a fixed cofactor argument $y$, the unspent fraction is $O(\sqrt{y/K})$ as $K$ grows.

Let $N(x)$ count the positive 2,3-smooth integers through $x$. The elementary identity $\sum_{r\le x}M_0(x/r)=N(x)$ follows by grouping divisors. Multiply the two parts of $k(K/y)$ by $M_0(y)y^{-3/2}$ and integrate. Changing variable $x=ry$ in each finite sum gives
$$
 D(K)=\int_1^K M_0(y)k(K/y)\frac{dy}{y^{3/2}}
     =\frac1{\sqrt K}\int_1^K\frac{N(x)}x\,dx
      -\frac12\int_1^K\frac{N(x)}{x^{3/2}}\,dx
     =\sum_{\substack{w\le K\\w\ {\rm smooth}}}
       \left[\frac{1+\log(K/w)}{\sqrt K}-\frac1{\sqrt w}\right].
$$
Since $N(x)=O(\log^2(2x))$, the first integral term tends to zero. Interchanging the positive smooth counts in the second yields
$$
 D(K)\longrightarrow-\frac1{(1-2^{-1/2})(1-3^{-1/2})}.
$$
The minus sign and the constant are forced by ordinary divisor arithmetic.

## Transfer the integral to the same physical rows

Let $L=\log t$, $h=\log4$, $\ell=\log9$. Define on $[0,\log K]$
$$
 G_K(z)=e^{-z/2}M_0(e^z)k(K/e^z)/c
$$
and zero elsewhere. The retained physical sum divided by $\sqrt t$ is exactly $\sum_{i,j\ge0}G_K(L-ih-j\ell)$. For fixed $K$, the limit after division by $L$ is $D(K)/(c h\ell)$, as in the [smooth-ray period mean](../proofs/what-a-positive-reference-must-lose.md).

The cutoff can actually grow at every head. Here are details of a rate using only integer separation. The normalized step function $M_0(e^z)e^{-z/2}$ has supremum and total variation $O(\sqrt K)$ on this interval. Its jumps have total size at most $\sum_{n\le K}n^{-1/2}$ and its derivative between jumps has integral $O(\sqrt K)$. The floor expression for $k$ also has variation $O(\sqrt K)$, from its jumps and its monotone pieces. Consequently $\|G_K\|_\infty=O(\sqrt K)$ and its total variation, including the two endpoints, is $O(K)$.

For $m$ consecutive visits of the rotation $\ell/h=\log3/\log2$, interval discrepancies as proportions are $O(1/\log(2+m))$, uniformly in the starting phase. For an elementary proof take $Q=\lfloor\sqrt m\rfloor$. Pigeonholing fractional parts gives reduced integers $p,q$, $1\le q\le Q$, with $|q\ell/h-p|\le1/Q$. The distinct integers $3^q,2^p$ differ by at least one. For these approximants this gives $|q\ell/h-p|\gg3^{-q}$, so $q\gg\log(2+Q)$. In each consecutive batch of $q$ visits the points differ by at most $1/Q$ from a translated equally spaced grid. The incomplete batch costs at most $q/m$. This proves the discrepancy bound. Integration by parts bounds the corresponding error for a function of bounded variation by its variation times the discrepancy, up to an absolute constant.

Periodize $G_K$ with period $h$. Its variation on one period is bounded by the full variation before periodization. The complete rows in $j$ number $L/\ell+O(1+\log K)$. The incomplete rows contribute at most $O(\sqrt K(1+\log K)^2)$ before division by $L$. It follows uniformly for $\log K=o(L)$ that
$$
 \frac{1}{L}\sum_{i,j\ge0}G_K(L-ih-j\ell)
 =\frac{D(K)}{ch\ell}
 +O\left(\frac{K}{\log(2+L)}
        +\frac{\sqrt K(1+\log K)^2}{L}\right).
$$
For example take $K(t)=\max(10^6,\sqrt{\log(3+\log t)})$ at large $t$. This proves the genuine all-head limit
$$
 \boxed{\displaystyle
 \frac{\sum_v v M_0(t/v^2)\, k(K(t)v^2/t)/c\ \mathbf1_{v^2\le t}}
      {\sqrt t\log t}
 \ \longrightarrow\ -\frac{1}{c(1-2^{-1/2})(1-3^{-1/2})\log4\log9}
 =-3.6320505\ldots .}
$$
The absolute value is half of the real double-pole coefficient of the [one-head primitive](../proofs/one-quantity-at-each-fourth-power.md). The proof establishes this contribution in a selected portion of the actual stream. It leaves the remainder capable of either sign.

## What the cutoff captures at finite heads

| Physical head | True total integer $M_a(t)$ | Signed portion with $K=10^6$ |
| ---: | ---: | ---: |
| $10^{12}$ | −77,683,177 | −71,858,999 to −71,858,996 |
| $2\cdot10^{12}$ | −116,644,406 | −106,074,013 to −106,074,009 |
| $10^{13}$ | −274,138,671 | −249,938,485 to −249,938,478 |

At ten trillion the displayed portion accounts for more than 91.17% of the magnitude of the signed total. The finite portions use ordinary rough arguments only through one million. They do not use the published high-argument Mertens bound. At $K=10^6$ the integral $D(K)$ is between −7.1967287 and −7.1967286; the limiting coefficient with *this cutoff held fixed* is between −3.2357647 and −3.2357645. The stronger −3.63205 coefficient uses $K(t)\to\infty$. [Rational square-root and logarithm enclosures](../receipt-archives/check_pal_rise_direction.py) · [Complete record](../receipt-archives/2026-11-25-pal-running-mass.json)

A remaining sufficient target is to keep the unspent signed contribution below $(3.63205-\epsilon)\sqrt t\log t$ for some fixed $\epsilon>0$ at all late heads. That would keep the full running mass negative. The proof above supplies its negative allowance and identifies exactly which physical fractions have already been used.
