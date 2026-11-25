# Passing the same coefficients to the next square

Christopher Daniel Pang’s PAL research program, 25 November 2026. Pang asked what a frame would have to write onto itself before passing forward. Hearthline derived the arithmetic below under his active construction key. PAL v2.4 supplies the question about retained trace, RPL-T02 the square scale, APCI the requirement to compare the same inputs, and BLA the question about the cost of a boundary. Dirichlet convolution and Newton inversion are classical. This construction uses the ordinary Möbius function and a census modulo six. [Corpus roles and editions](CORPUS-ROUTES.md) · [Related classical square identity, Huxley and Watt](https://arxiv.org/abs/1807.05890)

**A finite list can make the next list from its own entries.** If the old list gets every index through $H$ right, the update gets every index below $(H+1)^2$ right. The reason is elementary. An error survives the update only if it comes from multiplying two errors. Both factors are at least $H+1$. The next list also carries the correction that makes its reading a legal combination of residue measurements.

## The list and its price

Write $g(n)=1$ if $n$ is coprime to six and $0$ otherwise, and $m(n)=\mu(n)g(n)$. The value $\mu(n)$ vanishes on a multiple of a prime square, and otherwise changes sign once per distinct prime factor. Write $C(x)$ for the count of positive integers $\le x$ coprime to six. Divisor convolution, $(f*h)(n)=\sum_{d\mid n}f(d)h(n/d)$, gives $m*g=\delta_1$. On a rough integer the contributing divisors have sum $\sum_{d\mid n}\mu(d)$, and an integer with a factor 2 or 3 has no contributing split.

For $H\ge1$ let $w_H(n)$ be 1 through $H$, then $2-n/H$ through $2H$, and zero thereafter. Let $b_H(n)=n/H$ on $H<n\le2H$ and zero elsewhere. From any coefficient stream $f$ form

$$
s_H(f)=\sum_{n\le2H}w_H(n)f(n)/n,\qquad
(\Pi_H f)(n)=w_H(n)f(n)-b_H(n)s_H(f),\qquad a_H=\Pi_H m .
$$

Through $H$, the old values survive exactly. In the outer strip $\sum b_H(n)/n=H/H=1$, so $\sum (\Pi_H f)(n)/n=0$. Once the whole earlier list fits inside the new plateau, $\Pi_K a_H=a_H$ for $K\ge2H$.

The price for the actual arithmetic has an unconditional bound. Define $U(h)=\sum_{d\le h}m(d)/d$ and $D(x)=C(x)-x/3$. Counting a six-step period gives $|D(x)|\le2/3$ on the whole real ray. The identity $\sum_{d\le h}m(d)C(h/d)=1$ isolates the contribution of the first divisor. Thus

$$
h|U(h)|\le 3(1-D(h))+2(C(h)-1)=h+1-C(h)\le h .
$$

Indeed $1-D(h)>0$ and the remaining nonzero marks cost at most $2/3$ each. The tapered slope $s_H(m)=H^{-1}\sum_{h=H}^{2H-1}U(h)$ is an average, since a divisor $d$ participates in exactly $Hw_H(d)$ cuts. Hence $|s_H(m)|\le1$. Every coefficient $|a_H(n)|\le2$, because $w_H(n)+n/H=2$ on the outer strip. The unit bound on $U$ is attained at $h=1$. [Finite proofs of slope and coefficient bounds](PALRH/TaperedNewton.lean)

## The update and its first possible error

For two lists $a,b$, form $u=a+b-a*b*g$. Expanding the product gives

$$
m-u=(m-a)*(m-b)*g .
$$

If $a=a_H$ and $b=a_J$, every coefficient on the right vanishes before $(H+1)(J+1)$. At that first possible index the entire remaining coefficient is exactly $(m(H+1)-a_H(H+1))(m(J+1)-a_J(J+1))$. There is only one contributing pair of missing indices and the final factor of $g$ is $g(1)=1$. If $2H,2J\le K$ and $2K<(H+1)(J+1)$, apply $\Pi_K$ to the exact part. Its linearity and its action on the old lists give

$$
\boxed{a_K=a_H+a_J-\Pi_K(a_H*a_J*g).}
$$

The right side uses the stored lists and the explicit six-step census. With $J=H$ and even $H\ge4$, choose $K=H^2/2$. Starting at four gives $4,8,32,512,131072,\ldots$.

**Pencil test.** At $H=4$, the nonzero raw marks through eight are $1,-1,-1$ at $1,5,7$. The slope is $1-3/20-1/28=57/70$. At five the list reads $-3/4-(5/4)(57/70)=-99/56$. The missing part is $-1+99/56=43/56$. Every updated coefficient through 24 is exact. At 25 the missing part is $(43/56)^2=1849/3136$.

**Turn one factor the other way.** For the same construction at a general $H$, the first missing part is $\{m(H+1)+(H+1)s_H(m)\}/H$. At $H=6{,}600{,}000$ the true slope lies between $-0.000000463290$ and $-0.000000463248$. Even its upper endpoint is below $-1/(H+1)$. Paired with side four, the first missing coefficient at $5\cdot6{,}600{,}001=33{,}000{,}005$ is strictly negative. The calculation sieves up to $2H$, rounds each signed rational summand down at denominator $10^{17}$, and adds one unit for each nonexact rounding to obtain the upper bound. The archive gives integer endpoints and the exact local sign. [Standard-library reproduction](../receipt-archives/check_pal_tapered_newton.py) · [Exact results](../receipt-archives/2026-11-25-pal-tapered-newton.json)

## What the list measures

At physical row $k$, set $F_H(k)=\sum_d a_H(d)C(k/d)$. For a positive $d$ the census splits into four floors at $d,2d,3d,6d$. The linear part $k/(3d)$ drops out of the sum because $\sum a_H(d)/d=0$. The remainder is a finite rational combination of the original residue clocks $(k\bmod d)/d$. On $1\le k\le H$ the divisor identity above gives $F_H(k)=1$. Our squared error over **all** positive rows is

$$
E_H=\sum_{k\ge1}\frac{|1-F_H(k)|^2}{k(k+1)}.
$$

| Side $H$ | Error through row $H^2$ | All-row error $E_H$ | Rows summed before the tail bound |
| ---: | ---: | ---: | ---: |
| 4 | $[1.11568,1.11569]$ | $[1.19006,1.19075]$ | 50,000 |
| 8 | $[0.89407,0.89408]$ | $[0.92364,0.92507]$ | 50,000 |
| 32 | $[0.48485,0.48486]$ | $[0.48714,0.48939]$ | 131,072 |
| 512 | $[0.09555,0.09556]$ | $[0.09562,0.10873]$ | 2,097,152 |

Each upper endpoint includes every later row. From $|D|\le2/3$, the cost after row $M$ is at most $(1+\frac23\sum_d|a_H(d)|)^2/(M+1)$. The exact recurrence also recovers every one of the first 262,144 raw coefficients at the next update from side 512. Its whole-error change at side 131,072 is a separate question. The input pairs $(5,10),(4,13),(8,8)$ all give the identical rational list at side 32. [Arithmetic, full tail bounds and tested ranges](../receipt-archives/2026-11-25-pal-tapered-newton.json)

## Unresolved

The three decreases support a specific next question. Do decreases recur at arbitrarily late steps of the fixed update above? A theorem about their recurrence would imply bare RH. There is a stronger quantitative statement about the actual change in error at each square, with its full proof in [When a drop would count](when-a-drop-would-count.md). The [Lean module](PALRH/TaperedNewton.lean) proves the finite update, coefficient bound and an implication from an explicit all-scale error estimate to stock Mathlib RH.
