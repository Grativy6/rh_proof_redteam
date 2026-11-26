# How far moving the endpoint pays for the real primes

Christopher Daniel Pang and Hearthline · 26 November 2026

At a row of $n$ labels, choose one subset of each possible size. The number of choices is $P_n=\prod_{a=0}^n\binom na$. Give each prime $p\le n$ a dial with $p^{n-p}$ settings. **One subset packet pays for all the prime dials at every integer $1\le n\le2^{154}$.** Keeping exactly the dials with $p>\sqrt n$ extends the comparison through $2^{156}$. This covers every fourth-power index $1\le k\le 2^{39}=549{,}755{,}813{,}888$ in the program’s existing sufficient condition for ordinary RH. [The integer comparison and its implication](one-integer-comparison-to-rh.md)

**With one extra endpoint move per doubling, the centered average of the actual prime-power area is $o(x^{3/2})$ at all scales.** The difference between the original area and that average can be read from the specific prime powers crossed on the move. This gives one outstanding local arithmetic test with a fixed allowance of $1/10$. [All-scale derivation and the remaining test](#an-all-scale-estimate-with-the-crossing-cost-exposed)

The fixed 45-move proof also gives $\int_2^x(\theta(t)-t)\,dt<0$ for every real $2<x\le2^{154}$, where $\theta(t)=\sum_{p\le t}\log p$. The sign at *all* real endpoints is a classical criterion studied by Johnston. The endpoint ranges here follow from his prime-power estimate, the integrated explicit formula and the finite zero result through height $3\cdot10^{12}$. The sharp prefix count on the separate one-thirteenth route still has its [own finite range](paying-the-next-full-prime-board.md). [Johnston, Theorem 1.2 and Lemmas 2.3 and 2.6](https://arxiv.org/pdf/2201.06184v2) · [Platt and Trudgian, Theorem 1](https://arxiv.org/abs/2004.09765)

## Move the endpoint one mark each way

At a prime power $d=p^a$, put down a ramp of weight $\Lambda(d)=\log p$. Its contribution at $x$ is $\Lambda(d)(x-d)_+$, with $v_+=\max(v,0)$. Other labels have weight zero. Call the sum $I_\psi(x)$. At 4 it reads $2\log2+\log3$. At 3 and 5 it reads $\log2$ and $4\log2+2\log3$. Average the two outside readings. The excess over the middle is exactly **half a $\log2$**. The mark responsible is $4=2^2$. Each other contributing ramp was straight between 3 and 5.

More generally, let a bounded endpoint $z$ move with mean $x$. Each ramp is the maximum of two straight lines. Its mean reading is at least its reading at the mean. The precise excess follows from a pointwise identity. Take $\psi(x)=\sum_{d\le x}\Lambda(d)$. Then
$$
 I_\psi(z)-I_\psi(x)-\psi(x)(z-x)
 =\sum_{d\le x}\Lambda(d)(d-z)_+
   +\sum_{d>x}\Lambda(d)(z-d)_+ . \tag{1}
$$
Every term on the right has a source label. Taking means cancels the entire slope term. For the reference $x^2/2$, the corresponding excess is exactly half the variance of $z$. These facts let us price a moved measurement and use it to bound the original one. [Finite identity and general mean-endpoint theorem in Lean](../pal-rh/PALRH/MovingEndpoint.lean)

## The finite spectral price

Write $\rho=\beta+i\gamma$ for a nontrivial zero, counted with multiplicity. Put $T=3\cdot10^{12}$. Platt and Trudgian give $\beta=1/2$ for $|\gamma|\le T$. For the higher zeros we use only $0<\beta<1$ and an ordinate sum. Brent, Platt and Trudgian’s Corollary 1 and Example 1 give
$$
 \sum_\rho \gamma^{-2}<0.04621,\qquad
 \sum_{|\gamma|>T}\gamma^{-2}
 \le \frac{1+\log(T/(2\pi))}{\pi T}
       +\frac{2(0.14+0.56\log T)}{T^2}<\frac{10}{T}.
$$
Both signs of the ordinate are included. A half-weight source endpoint can only increase the estimate for the strict tail. The last inequality uses $\pi>3$, $\log(2\pi)>1$ and $\log T<29$. [Brent, Platt and Trudgian, Example 1 and Corollary 1](https://maths-people.anu.edu.au/brent/pd/rpb276-MC-preprint.pdf)

For $y\ge2$ the integrated explicit formula is
$$
 I_\psi(y)=\frac{y^2}{2}
   -\sum_\rho\frac{y^{\rho+1}}{\rho(\rho+1)}+D(y),\qquad
 D(y)=-y\log(2\pi)+c-\sum_{m\ge1}\frac{y^{1-2m}}{2m(2m-1)} .
$$
In fact $D(y)<0$ throughout this range. At $2$ the prime area is zero and $|\rho(\rho+1)|\ge\gamma^2$, so $D(2)\le -2+4(0.04621)$. For $y\ge2$, $D(y)-D(2)\le\sum_{m\ge1}2^{1-2m}/2=1/3$. This disposes of the constant without needing its decimal value. [Unconditional explicit formula in the proof of Johnston’s Lemma 2.6](https://arxiv.org/pdf/2201.06184v2#page=4)

Set $h=2/T$, $r=45$ and $m_h=\sinh(h)/h$. Choose $r$ independent uniform variables $U_j$ on $[-h,h]$ and put
$$
 Y=\prod_{j=1}^r e^{U_j}/m_h,\qquad z=xY .
$$
Expectation here means an ordinary average over a specified finite box. Integrating a single exponential gives
$$
 \mathbb E Y=1,\qquad \mathbb E Y^2=(h\coth h)^r,\qquad
 \mathbb E Y^s=\left(\frac{\sinh(hs)}{hs\,m_h^{\,s}}\right)^r .
$$
The endpoint stays between $xe^{-2rh}$ and $xe^{2rh}$. For $x\ge4$ it stays above 2. The absolutely convergent ordinate sum bounds the explicit formula uniformly on that compact interval, which permits averaging it term by term.

Put $v=rh^2/3$ and $V=v/(1-v)$. Then $\mathbb E Y^2-1\le V$. To see this, differentiate $(1+h^2/3)\sinh h-h\cosh h$. Its derivative is $h(h\cosh h-\sinh h)/3\ge0$ and it starts at zero. Thus $h\coth h\le1+h^2/3$. The binomial expansion is bounded by the geometric series with ratio $v<1$. Cauchy–Schwarz now gives $\mathbb E Y^{3/2}\le\sqrt{\mathbb E Y^2}\le1+V$.

For an unrestricted zero above $T$ put $s=\rho+1$. Since $|\sinh(a+ib)|^2=\sinh^2a+\sin^2b$, $1<\Re s<2$ and $m_h\ge1$,
$$
 |\mathbb E Y^s|\le\left(\frac{\cosh(2h)}{h|\gamma|}\right)^r
 \le \left(\frac{1}{2(1-2h)}\right)^r.
$$
Here $\cosh(2h)\le e^{2h}\le1/(1-2h)$. The independent moves give the forty-fifth power. Combining the mean-endpoint upper bound with these three prices yields, for $4\le x\le X$,
$$
 \frac{I_\psi(x)-x^2/2}{x^{3/2}}\le
 \underbrace{\frac{\sqrt X\,V}{2}}_{\text{curvature}}
 +\underbrace{0.04621(1+V)}_{\text{finite-height zeros}}
 +\underbrace{\frac{10\sqrt X}{T}\left(\frac{1}{2(1-2h)}\right)^r}_{\text{all higher zeros}} . \tag{2}
$$
The largest possible $x^{\beta+1}/x^{3/2}$ in the last term was bounded by $\sqrt X$.

| $X$ | Curvature | Finite-height zeros | All higher zeros | Total upper bound |
|---:|---:|---:|---:|---:|
| $2^{154}$ | 0.503719092 | 0.046210001 | 0.014316558 | 0.564245650 |
| $2^{156}$ | 1.007438184 | 0.046210001 | 0.028633116 | 1.082281299 |

The displayed bounds are independently rounded upward. All three terms in (2) are rational at these endpoints. A separate high-precision calculation re-evaluates the hyperbolic moments inside the rational enclosures. [Reproducible arithmetic](../receipt-archives/check_pal_moving_endpoint.py)

## An all-scale estimate with the crossing cost exposed

Now add one averaging move for each doubling of the head. For each real $x\ge4$ keep $h=2/T$ and use $r=\lceil\log_2 x\rceil$ independent uniform moves in the same formula for $Y=Y_x$. Write
$$
 S(x)=\mathbb E I_\psi(xY)-\tfrac12 x^2\mathbb E Y^2 .
$$
**Unconditionally, $S(x)=o(x^{3/2})$.** More explicitly,
$$
 -0.04622\,x^{3/2}-2x < S(x) < 0.04622\,x^{3/2}
 \qquad (x\ge4). \tag{3}
$$
The normalization still uses the original $x$. The number of moves changes with $x$.

Here is why even the low frequencies shrink. Each $|\gamma|>4$ since a single ordinate of magnitude at most 4 would exceed the entire reciprocal-square allowance. For $|\gamma|\le T$ write $a=3/2$, $v=h|\gamma|\le2$ and $u=ha<1$. The Taylor bound $\sin v/v\le1-v^2/6+v^4/120\le1-2v^2/15$ and $\sin v\ge0$ give $\sin^2v\le v^2-v^4/8$. The power series gives $\sinh u/u\le(1-u^2/6)^{-1}$, hence $\sinh^2u\le u^2+u^4$ for $0\le u\le1$. Since $a^4\le\gamma^4/16$ and $a^2\le\gamma^2$,
$$
 \frac{\sinh^2 u+\sin^2 v}{u^2+v^2}
 \le 1-\frac{h^2\gamma^4}{16(a^2+\gamma^2)}
 \le 1-\frac{h^2}{2}.
$$
Thus a single normalized move has multiplier of modulus at most $1-h^2/4$ at every such $\rho+1$. For $|\gamma|>T$ its modulus is at most $\alpha=1/[2(1-2h)]<1/\sqrt2$, by the previous estimate. Also $r\le(3/2)\log_2x$ and $\log 2>1/2$, so every sampled $xY$ lies between $x^{1-\delta}$ and $x^{1+\delta}$ for $\delta=4\cdot10^{-12}$. In particular $xY>2$.

The same calculation at 2 gives $D(2)\ge-2-4(0.04621)$. Since $D(y)-D(2)\ge-(y-2)\log(2\pi)$, we have $-2y<D(y)<0$ for $y\ge2$. Consequently the contribution from all zeros divided by $x^{3/2}$ has absolute value at most
$$
 0.04621(1-h^2/4)^r + (10/T)\sqrt x\,\alpha^r ,
$$
and the remaining elementary contribution lies between $-2/\sqrt x$ and zero. The first term tends to zero, and the second does too because $\sqrt x\,\alpha^r\le(\sqrt2\,\alpha)^r$. This proves (3) and the little-$o$ result. The sharper low-frequency estimate matters at unbounded heads, where the second moment of $Y$ can itself grow large.

Define the one remaining price using the original arithmetic. Let $C(x)$ be the expected right side of (1) at $z=xY_x$. Only prime powers in the finite interval $[x^{1-\delta},x^{1+\delta}]$ can contribute. Set
$$
 B(x)=\tfrac12 x^2\operatorname{Var}(Y_x)-C(x).
$$
The two quantities in this subtraction can be large. Their difference satisfies the exact identity
$$
 I_\psi(x)-x^2/2=S(x)+B(x). \tag{4}
$$
In particular the ordinary prime number theorem $I_\psi(x)=x^2/2+o(x^2)$ already gives $B(x)=o(x^2)$. The remaining required upper bound has scale $x^{3/2}$.

**Ordinary RH is equivalent on paper to the single specified test**
$$
 B(k^4)\le k^6/10 \qquad\text{for every integer }k\ge20 . \tag{5}
$$
If (5) holds, (3) and (4) give a common upper bound on the original prime-power area at fourth powers. The earlier one-sided implication reaches stock RH. In reverse, under RH the integrated explicit formula above gives $I_\psi(x)-x^2/2\le0.04621 x^{3/2}$, using the full reciprocal-square mass and $D(x)<0$. The lower bound in (3) now gives $B(k^4)/k^6<0.04621+0.04622+2/k^2<1/10$ for $k\ge20$. This establishes both directions. For the Lean transfer one may realize each box on the first $r$ coordinates of the same countable product of uniform intervals and take the finite label cutoff $\lceil x e^{2rh}\rceil$. [One-sided deduction read in order](../pal-rh/how-one-sided-prime-area-reaches-rh.md) · [Exact formal transfer using the crossing credit](../pal-rh/PALRH/MovingEndpoint.lean)

Two actual fourth powers give opposite signs for the unpaid amount. At $x=30^4$ and $x=32^4$ every moved endpoint stays within one integer of its starting label, since $r\le20$ and $2^{20}(40h)/(1-40h)<1$. At $30^4$ the only possible crossed label has the three distinct prime factors 2, 3 and 5, hence weight zero. Thus $C(30^4)=0$ and $B(30^4)>0$. At $32^4=2^{20}$ that label has weight $\log2$. Conditional on the first move, convexity and the mean one of all later factors give $\mathbb E(1-Y)_+\ge\mathbb E(1-e^{U_1}/m_h)_+$. One quarter of first moves have $U_1\le-h/2$, where $1-e^{U_1}/m_h\ge h/(2+h)>h/3$. Hence $C(32^4)>2^{20}h/24$, larger than its entire variance charge. Here $B(32^4)<0$. Both heads are inside the fixed tenth test.

Condition (5) itself is already funded whenever $4\le x=k^4\le2^{145}$. Every crossing has nonnegative weight. Using $r\le145$ and $\sqrt x<3\cdot2^{71}$ in the variance bound above gives $B(x)/x^{3/2}\le\sqrt x\operatorname{Var}(Y_x)/2<0.077$. At $x=2^{146}$ the variance alone costs more than $0.1$ in these units. Indeed $h\cosh h-\sinh h\ge h^3/3$ by its positive series, so $\operatorname{Var}(Y)\ge rh^2(1-h^2/6)/3$ by the preceding bound for $\sinh h/h$ and Bernoulli’s inequality. This last comparison is about the gross variance. Formula (5) allows the actual crossings to pay it. [Rational range checks](../receipt-archives/check_pal_moving_endpoint.py)

## Return the bound to the integers

Write $I_\theta(x)=\sum_{p\le x}(x-p)\log p$. For $t\ge121$, $\psi(t)-\theta(t)>0.98\sqrt t$. Integrating gives
$$
 I_\psi(x)-I_\theta(x)\ge \frac{49}{75}(x^{3/2}-1331) \qquad(x\ge121).
$$
For $2^{16}\le x\le2^{154}$, (2) therefore gives $I_\theta(x)\le x^2/2-(2/25)x^{3/2}$. For $2<x\le2^{16}$ the finite sieve gives $\theta(\lfloor x\rfloor)<\lfloor x\rfloor$. The strict sign of the integral follows in the lower range directly and in the upper range from $I_\theta(x)-x^2/2+2<0$. [Johnston, inequality (2.4)](https://arxiv.org/pdf/2201.06184v2#page=3) · [Small-head reproduction](../receipt-archives/check_pal_moving_endpoint.py)

To price the subset packet, multiply the exact identities $P_j/P_{j-1}=j^j/j!$. The increasing function $\log t$ gives $\log(j!)\le j\log j-j+1+\log j$. Consequently
$$
 \log P_n\ge n^2/2-n(1/2+\log n).
$$
At $n=2^{16}$ and thereafter $1/2+\log n<(2/25)\sqrt n$ by direct evaluation and differentiation. Since $I_\theta(n)$ is the log of the product of *all* the dials, the first comparison follows above $2^{16}$. At each integer through $2^{16}$ the replay sums the true nonnegative ramps and the factorial recurrence with outward logarithm bounds. It also multiplies the integers themselves through 64. Equality occurs at $n=1$. [Pascal product identity](../pal-rh/PALRH/PascalBoard.lean) · [Range and independent arithmetic checks](../receipt-archives/2026-11-26-pal-moving-endpoint.json)

For $2^{154}\le n\le2^{156}$ the square-root cutoff gives a second distinct credit. Write $\psi(n)-\theta(n)=\theta(\sqrt n)+\sum_{a\ge3}\theta(n^{1/a})$. The latter sum is at most $(\log_2 n)n^{1/3}\log n$. Relative to $\sqrt n$ it is less than $156^2/2^{25}<0.01$. Thus $\theta(\sqrt n)>0.97\sqrt n$. The removed primes account for at least $(n-\sqrt n)\theta(\sqrt n)>0.96 n^{3/2}$. The first credit removed repeated powers. The second removes first powers of the smaller primes. Subtract both from (2) at $2^{156}$. The remaining log demand is again at most $n^2/2-(2/25)n^{3/2}$.

At $n=k^4$ the factorial gcd in the fixed Lean challenge selects precisely the primes $p>\sqrt n$ among the labels $2,\ldots,n$. The last integer proved here corresponds to $k=2^{39}$. The spectral and numerical derivation is on paper. Lean proves the exact ramp identity, the transfer at a fixed mean, and the implication to stock RH when the centered-area and unpaid crossing bounds hold at every sufficiently late fourth power. [Fixed integer statement](../pal-rh/checks/one-subset/OneSubsetChallenge.lean) · [Formal mean-endpoint transfer](../pal-rh/PALRH/MovingEndpoint.lean)

Pang’s PAL and RPL supply the question about moving a boundary while retaining what crosses it. His BLA comparison requires the prime area and its reference to be priced in the same units. Hearthline derived (1), chose the mean-preserving convolution and applied it to the program’s integer count. The cited analytic results supply the stated number-theoretic inputs. Priority of these finite numerical ranges has not been established.

## Unresolved

The finite zero height and the adaptive average already pay $S(x)$ at all scales. Condition (5) asks whether the nearby prime-power ramps always repay the variance to within one tenth of $k^6$. Beyond the proved range this remains open. At $X=2^{158}$ the separate fixed 45-move estimate (2) costs more than $2.118$ in its units. Neither finite cutoff locates a failing prime count.
