# When two prime directions meet

Christopher Daniel Pang and Hearthline · 26 November 2026

At size $n$, let $x=\sqrt n$, let $D(n)=\sum_{r=1}^n\lfloor n/r\rfloor$, and choose the largest integer $h$ with $8h^3\le5D(n)$. Count the positive lattice pairs $(r,j)$ with $rj\le n$ and this is an integer instruction for how far to move the sieve. Set $c=\max(0,\lfloor x\rfloor-h)$. Define the critical record count and margin by
$$
 M(n)=(n!)^n\!\!\prod_{\substack{2\le m\le n\\\gcd(m,c!)=1}}m^{2(n-m)},
 \qquad J(n)=\log(B_n/M(n)),\qquad B_n=n^{n^2}.
$$
Once $n$ is large we have $(c+1)^3>n$. Every admitted label is then a prime above $c$ or a product $pq$ of two primes $c<p\le q$. The two factors of a composite are uniquely determined in this order. The two ways of approaching a product, $(p,q)$ and $(q,p)$, correspond to a single distance on the board. A square has one ordered representation. [Classification, uniqueness and finite triangle](PALRH/HorizonPairs.lean)

## The triangle and the coefficient

First let $H\sim C(n\log n)^{1/3}$ for fixed $C>0$, with cutoff $c=\lfloor x\rfloor-\lfloor H\rfloor$. The true primes newly admitted relative to $\lfloor x\rfloor$ cost $o(n^{3/2})$. Indeed there are $O(H+1)$ integer labels in this narrow range, each costing $O(n\log n)$, and $H\log n=o(\sqrt n)$.

Only semiprime labels can supply a larger extra charge. Write $p=x+Hu$ and $q=x+Hv$. Then
$$
 \frac{(n-pq)_+}{xH}=(-u-v-(H/x)uv)_+ .
$$
Both scaled offsets lie in $[-1-o(1),1+o(1)]$ when their product contributes. A prime within a fixed subinterval in these coordinates occurs with asymptotic density $H/\log x$ per unit length. This is the ordinary prime number theorem in short intervals, applied at $x+O(H)$ to lengths proportional to $H=x^{2/3+o(1)}$. Guth–Maynard’s Corollary 1.3 applies with a fixed positive margin in the exponent. Differences for endpoints and the vanishing boundary strips are controlled by enclosing them in fixed subintervals and then shrinking those intervals. Thus the two normalized counting measures on any fixed bounded box converge to ordinary area under products, by rectangular approximation. [Guth and Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552)

On this bounded box the positive parts converge uniformly to $(-u-v)_+$. The limiting integral over ordered pairs is
$$
\int_{-1}^1\int_{-1}^{-u}(-u-v)\,dv\,du=4/3 .
$$
Its discrete counterpart has $\sum_{j=0}^{t-1}(j+1)(t-j)=t(t+1)(t+2)/6$ stacked cells with $t=2h$. Passing from ordered pairs to distances halves the leading term. The diagonal correction is $O(xH^2)$, whereas the leading cost has order $xH^3/\log x$. Each distance carries $2(n-pq)$ dials of radix $pq$, with $\log(pq)\sim2\log x$. Multiplying the four factors gives
$$
 C_{\rm semi}(n)\sim
 2(xH)(2\log x)\frac{H^2}{\log^2x}\frac23
 = \frac{16}{3}\frac{\sqrt n\,H^3}{\log n}.
$$
This counts genuine composite labels admitted by the altered selector; the original board counts only prime labels. The arithmetic replay counts the diagonal once and the two off-diagonal orientations together, using prefix sums of $1,q,\log q,q\log q$. [Independent direct-gcd comparison and large heads](../receipt-archives/check_pal_horizon_pairs.py)

## Why the integer cut contains five eighths

The elementary hyperbola count gives $D(n)=n\log n+O(n)$ by harmonic-sum comparison. Thus our chosen $h^3\sim(5/8)n\log n$. The newly admitted semiprimes cost $(10/3+o(1))n^{3/2}$. There are two deterministic contributions to cancel.

1. The prime dials discarded through the original square-root cutoff cost $(2+o(1))n^{3/2}$, from $\theta(\sqrt n)\sim\sqrt n$.
2. The repeated-prime area $\Delta(x)=I_\psi(x)-I_\theta(x)$ is $(2/3+o(1))x^{3/2}$. Indeed $\psi(t)-\theta(t)=\theta(\sqrt t)+O(t^{1/3}\log t)\sim\sqrt t$ by splitting squares from higher powers, and integration gives $2/3$. The board area counts this twice.

Their sum is $2+4/3=10/3$. Matching $(16/3)C^3=10/3$ gives $C^3=5/8$. Therefore, with $G(n)$ the genuine all-prime margin,
$$
 \frac{J(n)}{n^{3/2}}=\frac{G(n)}{n^{3/2}}-\frac43+o(1),\qquad
 J(n)=-2\bigl(I_\psi(n)-n^2/2\bigr)+o(n^{3/2}).
$$
These identities require no global zero-location assumption.

## Both signs on the actual fourth powers

The prime-square residue and an independently located simple critical zero $\rho=1/2+i\gamma$ imply that $G(n)/n^{3/2}$ reaches both sides of $4/3$ in the limsup and liminf by at least $A=|2/[\rho(\rho+1)]|$. The earlier proof applies to ordinary integer heads. We now transfer the same two bounds to the fourth powers. [Actual zero and residue proof](fourth-power-boards-and-their-funded-intervals.md#where-the-middle-of-the-band-comes-from)

Let $a=k^4$, $b=(k+1)^4$ and $w=b-a\asymp a^{3/4}$. The same short-interval theorem gives $\theta(a+t)-\theta(a)=t+o(w)$ uniformly on $0\le t\le w$. First use fixed values of $t/w$, then bracket the remaining points by a finite regular partition and monotonicity. Passing from prime counts to logarithmic weights on $[a,a+w]$ changes each weight from $\log a$ by $O(w/a)$. Integrating,
$$
 (a+t)^2-2I_\theta(a+t)=a^2-2I_\theta(a)+2(a-\theta(a))t+o(w^2)
$$
uniformly. The factorial correction $nH_n=O(n\log n)$ is $o(a^{3/2})$. Hence $G$ differs from the linear interpolation of its two endpoint readings by $o(a^{3/2})$, since $w^2=O(a^{3/2})$. Any eventual finite upper bound on the normalized quartic endpoints then holds in the limsup for intervening integer heads. To see this, the two interpolation weights are positive and the endpoint values of $n^{3/2}$ divided by $(a+t)^{3/2}$ approach one uniformly. The lower bound transfers in the same way. [Short-interval input](https://arxiv.org/pdf/2405.20552)

Consequently $\limsup_k J(k^4)/k^6\ge A$ and $\liminf_k J(k^4)/k^6\le-A$. At $14.13472<\gamma<14.13474$, direct interval arithmetic gives $A>(\log2)/70$. Infinitely many critical boards overflow by more than $k^6/70$ bits, and infinitely many have more than that many bits of surplus. Removing the whole allowance from the test would impose a false promise.

## An integer inequality equivalent to RH

For all sufficiently large integers $k$, consider the claim
$$
\boxed{\ M(k^4)^{15}\ \le\ B_{k^4}^{15}\,2^{2k^6}\ }.
$$
This one-sided universal claim is equivalent to RH. The exponent expresses a total overflow allowance of $2k^6/15$ bits. In fact RH also gives the inequality in the reverse direction with the same allowance on the other side.

Under RH the integrated explicit formula gives $\limsup_n |I_\psi(n)-n^2/2|/n^{3/2}\le T$, where $T=2+\gamma_E-\log(4\pi)$. On the line $|\rho(1+\rho)|\ge1/4+\gamma^2$, and the sum of the reciprocals of $1/4+\gamma^2$ is $T$ by the completed product. The remaining ordinary explicit-formula terms are $O(n)$. Our critical cancellation gives $\limsup |J(n)|/n^{3/2}\le2T<2\log2/15$. The replay encloses $T$ on the needed side of this last strict inequality. [Product constant and proof](what-the-least-cut-measures.md#a-power-saving-has-a-precise-meaning) · [Explicit formula](https://arxiv.org/pdf/2201.06184)

Conversely every prime larger than $\sqrt n$ is admitted by the critical frame. If its records fit with the proposed allowance at all sufficiently late fourth powers, the prime-only records above $\sqrt n$ fit with the same allowance. Reintroducing all smaller prime distances costs $O(n^{3/2})$ more bits. The one-sided prime-area estimate and fourth-power argument give RH. [One-sided deduction](fourth-power-boards-and-their-funded-intervals.md#why-fourth-powers-reach-every-intermediate-size)

At root 20 the measured log margin divided by $n^{3/2}$ lies between 0.25962170 and 0.25962171. At root 24 it lies between −0.65354315 and −0.65354314. These are finite observations. The formal sources establish the finite survivor classification, uniqueness of the pair, triangle identity and two size-256 capacity outcomes. The asymptotic cost, recurring signs and allowance equivalence above are paper results. [Replay ranges and formal scope](../receipt-archives/2026-11-26-pal-horizon-cut.json)
