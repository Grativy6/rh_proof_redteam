# What the central mirror earns

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). Pang asked what makes the central line necessary once people have constructed the representation in which to draw it. PAL’s frame question and APCI’s same-observation comparison suggest a direct experiment. Keep the reflection. Change one arithmetic rule. Check where a cancellation actually lands.

## A four-line example

The mirror that keeps the height fixed sends $s$ to $1-\overline s$. The real polynomial $64(s-\tfrac12)^4+1$ respects that mirror. At $s=\tfrac34+\tfrac i4$, its fourth-power term is $(1+i)^4/4^4=-1/64$. The polynomial vanishes there and at the reflected point $\tfrac14+\tfrac i4$. Both are inside the critical strip.

In counting language, RH asks how large a sustained departure from the expected count can be. More precisely, weight each prime power $p^a\le x$ by $\log p$ and call their sum $\psi(x)$. The boundary is $\psi(x)-x=O_\epsilon(x^{1/2+\epsilon})$ for each $\epsilon>0$. Reflection explains why a departure associated to an off-center cancellation has a partner. Excluding the pair requires arithmetic information. [Bombieri’s statement and explicit formula](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf)

## Change the rule at five

For $a=4$ or 5, put $P_a(X)=1+aX+5X^2$ and $Z_a(s)=\zeta(s)P_a(5^{-s})$. Both Dirichlet series have nonnegative integer coefficients and an Euler product. At primes other than 5 the local factor is the ordinary geometric series. At 5 it is $P_a(X)/(1-X)$, $X=5^{-s}$. The completed function is
$$
 5^s\pi^{-s/2}\Gamma(s/2)Z_a(s).
$$
It has the same value at $s$ and $1-s$ because $P_a(X)=5X^2P_a(1/(5X))$ and the completed zeta factor already has that symmetry. The extra $5^s$ is part of the construction. The ordinary Riemann completion has conductor 1. These two completions have parameter 25 in the convention $q^{s/2}$. [Reflection formula](https://dlmf.nist.gov/25.4)

Scale $X$ to $Y=\sqrt5 X$. The extra factor becomes $Y^2+(a/\sqrt5)Y+1$. At $a=4$ both roots have modulus 1. At $a=5$ they are $-\varphi$ and $-\varphi^{-1}$, where $\varphi=(1+\sqrt5)/2$. They give the explicit locations
$$
 s=\frac12\ \pm\frac{\log\varphi}{\log5}
          +\frac{(2k+1)\pi i}{\log5},\qquad k\in\mathbb Z .
$$
Since $1<\varphi<\sqrt5$, both real parts lie strictly in the strip. The golden ratio here comes directly from the quadratic at five. The squared length associated to its integer recurrence is
$$
 Q_a(x,y)=x^2-a x y+5y^2,\qquad Q_a(-5y,x-ay)=5Q_a(x,y).
$$
At four, $Q_4=(x-2y)^2+y^2$. At five, $Q_5(2,1)=-1$. The same transport still satisfies the identity after the form loses positive definiteness. That is the exact step at which the length stops forcing the eigenvalues to have modulus $\sqrt5$. For ordinary zeta the logarithmic local coefficient, after multiplication by its exponent $k$, is 1 at every $5^k$. For this altered factor it is $1-\alpha^k-\beta^k$, where $\alpha,\beta$ solve $u^2+a u+5=0$. At five the pair has unequal sizes $\sqrt5\,\varphi$ and $\sqrt5/\varphi$. Repeated visits reveal the discrepancy. The Lean file uses the same completion divided by the constant $\sqrt5$, so its multiplier is $Y+Y^{-1}+a/\sqrt5$. [Formal reflection, explicit point and length calculation](../pal-rh/PALRH/CentralMirror.lean)

## Keep the prime values and the pole residue too

One may fix the scale of the completion, the pole residue, the values on **every prime**, and an arbitrarily long initial list of integer coefficients across two models. Fix $r\ge3$, $m=2r+1$, $p=5$. Compare the following multipliers of $\zeta(s)$ at $X=p^{-s}$.
$$
 P(X)=1-X^m+p^mX^{2m},\qquad
 R(X)=1-X^r+p^{m-r}X^m-p^{m-r}X^{2m-r}+p^mX^{2m}.
$$
Both satisfy $U(X)=p^mX^{2m}U(1/(pX))$. Both give $U(1/p)=1$. Hence the two Dirichlet series have residue 1 at $s=1$ and the identical completion $p^{ms}\pi^{-s/2}\Gamma(s/2)$ times the respective series. At all ordinary primes the Dirichlet coefficient is 1. Nothing is assumed about the locations of the zeros inherited from $\zeta$.

The coefficient at $n$ is the cumulative sum of the local polynomial coefficients through $e=v_p(n)$. For $P$, it is 1 for $e<m$, 0 for $m\le e<2m$, and $p^m$ thereafter. For $R$ those successive values are given below.

| Valuation $e$ | Coefficient |
| --- | ---: |
| $0\le e<r$ | $1$ |
| $r\le e<m$ | $0$ |
| $m\le e<2m-r$ | $p^{m-r}$ |
| $2m-r\le e<2m$ | $0$ |
| $e\ge2m$ | $p^m$ |

Thus all coefficients are nonnegative integers, and the first disagreement between the models occurs at $n=5^r$.

For $P$, the variable $Y=(\sqrt p X)^m$ gives $Y^2-p^{-m/2}Y+1$. Both roots have modulus 1, so **every added root** is on the central line. For $R$, suppose $|\sqrt p X|=1$ and put $z=\sqrt p X$. Dividing $R$ by $z^m$ gives
$$
 z^m+z^{-m}-p^{-r/2}(z^{m-r}+z^{-(m-r)})+\sqrt5 .
$$
Its real value is at least $\sqrt5-2-2\cdot5^{-3/2}>0$. The last strict inequality reduces to $23^2>500$. Hence **every added root** is off the central line. They all lie in the strip. For $|X|\ge1$, the leading term dominates all others since $5^m>2+2\cdot5^{m-r}$. Reciprocity then places every root strictly above modulus $1/5$ as well. This locates all $2m$ added roots per vertical period, counted with multiplicity. [Exact coefficient and residue replay](../receipt-archives/check_pal_central_mirror.py)

## What this tells the RH construction

Ordinary zeta specifies the weight 1 at every integer and fixes the local factor at every prime power. The two examples above show how to detect the burden of those additional specifications. A symmetry, an Euler product, and agreement on a finite arithmetic head can all coexist with an off-center pair. On the actual PAL branch the unresolved step is an estimate across genuinely distinct prime factors after the local rules have been fixed. [Current arithmetic target](../pal-rh/what-a-reflected-remainder-carries.md)
