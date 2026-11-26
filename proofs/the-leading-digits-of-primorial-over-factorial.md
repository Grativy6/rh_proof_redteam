# The ordinary leading digits of a primorial divided by a factorial

Christopher Daniel Pang and Hearthline · 26 November 2026

Let $p_n$ be the $n$th prime and $P_n=\prod_{k=1}^n p_k$. Put $R_n=P_n/n!$.

**Theorem.** For every fixed real $t\ne0$ and every base $b>1$, the sequence $R_n^t$ is Benford in ordinary natural density. Equivalently, the fractional parts of $t\log_b R_n$ are uniformly distributed on $[0,1)$. In decimal, for example, the proportion of the first $N$ terms with leading digit 1 tends to $\log_{10}2$ as $N\to\infty$.

Bergelson, Kolesnik and Son prove ordinary Benford behavior of $(n!)^{t_1}P_n^{t_2}$ for $t_1+t_2\ne0$, and logarithmically weighted Benford behavior for $t_1+t_2=0$. Remark 4.26 in their 15 September 2026 revision asks whether the latter case is ordinary Benford. The theorem above answers that question affirmatively since in this case the sequence is $R_n^{t_2}$. It uses unconditional estimates for ordinary primes. Massé and Schneider previously proved the Benford property for the primorial itself. [Bergelson, Kolesnik and Son, version 2, Theorem 4.25 and Remark 4.26](https://arxiv.org/pdf/2509.19722v2#page=35) · [Massé and Schneider, Theorem 3.4](https://doi.org/10.4064/aa163-1-4)

The factor introduced on step $n$ is $p_n/n$. A difficulty occurs when its logarithm almost completes a whole turn. The phase can then spend a long time in one part of the circle. We keep the actual phase on entering each block and price only the motion inside it.

## 1. The required precision on the next factor

All logarithms in the proof are natural. For $n$ sufficiently large write $L_n=\log n$ and
$$
 g(n)=\log\big(L_n+\log L_n-1\big).
$$
Then
$$
 \log(p_n/n)=g(n)+O\!\left(\frac{\log L_n}{L_n^2}\right).
 \tag{1}
$$

Here is a derivation. The classical two-term expansion is $\pi(y)=y/\log y+y/\log^2y+O(y/\log^3y)$. It follows, for example, by partial summation from Dusart’s unconditional estimate for $\theta$. At $y=p_n$, put $R=\log p_n$, $T=p_n/n$. Inverting $1/T=R^{-1}(1+R^{-1}+O(R^{-2}))$ gives $T=R-1+O(1/R)$. The first-order prime number theorem gives $T\sim L_n$. Now $R=L_n+\log T$, first giving $T=L_n+\log L_n+O(1)$, and then $\log T=\log L_n+O(\log L_n/L_n)$. Substitution gives $T=L_n+\log L_n-1+O(\log L_n/L_n)$. Taking its logarithm proves (1). [Dusart, Theorem 5.2 and the expansion preceding Theorem 6.9](https://arxiv.org/pdf/1002.0442)

On $X\le s\le2X$ with $L=\log X$, the smooth comparison has derivative
$$
 g'(s)=\frac{1+1/\log s}{s(\log s+\log\log s-1)}\asymp\frac{1}{XL}.
 \tag{2}
$$
Its variation across this whole dyadic interval is of order $1/L$. The error in (1) is smaller than that variation. Both scales matter.

## 2. A proof by short blocks

Write $e(y)=\exp(2\pi i y)$. Fix $\tau\ne0$ and allow any constant twist $\eta\in\mathbb R$. The running sequence
$$
 z_n=e(\tau\log R_n+n\eta)
$$
has exact increments in turns $u_n=\tau\log(p_n/n)+\eta$, so $z_n=e(u_n)z_{n-1}$. We show that its sum on every subinterval of $[X,2X]$ is $o(X)$ uniformly in $\eta$. It suffices to sum the incoming phases $z_{n-1}$ since shifting the endpoints costs at most two.

Use blocks of length $H=\lfloor L^{3/2}\rfloor$ and let $\delta=L^{-5/4}$. Define $f(s)=\tau g(s)+\eta$. Exclude all integers with $\operatorname{dist}(f(n),\mathbb Z)\le2\delta$. By (2), $f$ is monotone and its range on $[X,2X]$ has length $O_\tau(1/L)$. For large $X$ at most two resonant intervals are involved, and their combined length is $O_\tau(XL\delta+1)$. Discard the blocks that touch these intervals, including the partially covered end blocks. At most $O_\tau(XL\delta+H)$ terms are discarded, which is $o(X)$.

On a remaining block starting at $a$, fix $q=e(f(a))$ and keep the genuine incoming value $z_{a-1}$. For all its increments,
$$
 |u_n-f(a)|\ll_\tau \frac{\log L}{L^2}+\frac{H}{XL}.
$$
The $r$th phase on the block differs from $z_{a-1}q^r$ in absolute value by at most $2\pi r$ times this bound, using $|e(v)-e(w)|\le2\pi|v-w|$ and telescoping. The mean error within the block is therefore $O_\tau(H\log L/L^2+H^2/(XL))=o(1)$. The mean of the comparison progression has magnitude at most $2/(H|1-q|)\ll1/(H\delta)=o(1)$. Multiplying by the block lengths and adding the discarded terms proves the claimed $o(X)$. The estimates are uniform in the incoming phases, in the twist and in truncated end blocks. [Formal finite block, incoming-phase and exceptional-block estimates](../pal-rh/PALRH/BenfordBlocks.lean)

Summing dyadic intervals gives $N^{-1}\sum_{n\le N}z_n\to0$. In particular take $\eta=0$ and $\tau=ht/\log b$ for each nonzero integer $h$. Weyl’s criterion gives the theorem. The argument concerns equal weight for each $n$.

## 3. A separate variation proof and a quantitative bound

There is a way to keep every increment exact even inside the good blocks. On a consecutive interval $[A,B]$ where $\operatorname{dist}(u_n,\mathbb Z)\ge\delta$, put $w_n=1/(e(u_n)-1)$. The exact identity
$$
 \sum_{n=A}^B z_{n-1}=w_Bz_B-w_Az_{A-1}
       +\sum_{n=A}^{B-1}(w_n-w_{n+1})z_n
$$
gives the bound $O(1/\delta+\delta^{-2}\sum_{n=A}^{B-1}|u_{n+1}-u_n|)$. This uses $|e(u)-1|\ge4\delta$ for $0<\delta\le1/2$ and the difference of two reciprocals. The actual ratios $p_n/n$ can move in both directions. Their total log variation still satisfies
$$
 \sum_{X\le n<2X}|\log(p_{n+1}/(n+1))-\log(p_n/n)|
 \le \log(p_{\lfloor2X\rfloor+1}/p_{\lfloor X\rfloor})+
       \log((\lfloor2X\rfloor+1)/\lfloor X\rfloor)=O(1).
 \tag{3}
$$
Both positive variations telescope separately. With (1), (2) and $\delta=L^{-3/2}$, there are $O_\tau(X/\sqrt L+1)$ excluded integers and at most three good intervals. Their sums cost $O_\tau(L^3)$ by (3). This supplies another proof of the ordinary Benford conclusion. Only the smooth reference defines the excluded intervals. Repeated small reversals of the true increment within them need no monotonicity assumption. [Exact finite summation by parts](../pal-rh/PALRH/PhaseBound.lean)

In fact the interval discrepancy of $\{\tau\log R_n+n\lambda\}$ is $O_\tau(\exp(-cV(N)))$ for some $c>0$, uniformly in the fixed linear twist $\lambda$, where $V(y)=(\log y)^{3/5}/(\log\log y)^{1/5}$. Here interval discrepancy means the supremum over subintervals of the difference between empirical frequency and length, in absolute value.

To justify this strengthening, let $Y(t)$ be the inverse of $\int_2^y du/\log u$ for large $t$. The unconditional prime number theorem with remainder gives $\pi(y)=\int_2^y du/\log u+O(y\exp(-c_0V(y)))$. One can derive this form by partial summation from the $\theta$ estimate of Johnston and Yang, reducing the positive constant to absorb logarithms and the part below $\sqrt y$. The mean value theorem, $Y(n)\sim p_n\sim n\log n$, and the derivative $1/\log y$ imply
$$
 \log(p_n/n)=\log(Y(n)/n)+O(\exp(-c_1V(n))).
$$
Moreover $(\log(Y(t)/t))'=(t\log Y(t)/Y(t)-1)/t\sim1/(t\log t)$, by the two-term expansion of the logarithmic integral. [Johnston and Yang, Theorem 1.4, equation (1.8)](https://arxiv.org/pdf/2204.01980)

Ignore the first $\sqrt N$ terms. On every remaining full or partial dyadic block $[X,2X]$ the approximation error before applying a harmonic is $O_\tau(\exp(-aV(N)))$ for some fixed $a>0$, by reducing $c_1$. For $1\le h\le\exp(aV(N)/8)$ set $\delta=\exp(-aV(N)/4)$. Work with the true increment $h\tau\log(p_n/n)+\eta$ and its smooth comparison $h\tau\log(Y(n)/n)+\eta$. Their difference is $o(\delta)$. The smooth range meets at most $O_\tau(1+h/\log X)$ integer neighborhoods of radius $2\delta$. By its derivative the number of excluded indices is at most
$$
 O_\tau\big(X(1+\log X/h)\delta+1+h/\log X\big).
$$
On the complementary intervals the reciprocal-weight inequality costs in total $O_\tau((1+h/\log X)/\delta+h/\delta^2)$, since the total variation of the true increments on the dyadic block is $O_\tau(h)$. Summing all blocks, the exceptional main term is $O_\tau(N\log N\,\delta)$. The other displayed costs together are $N^{o(1)}$ plus the omitted $\sqrt N$. In particular the normalized sum is $O_\tau(\exp(-aV(N)/5))$ uniformly over those harmonics and over $\eta$. Apply Erdős–Turán with cutoff $\lfloor\exp(aV(N)/8)\rfloor$ and $\eta=h\lambda$. The harmonic sum costs only $O(V(N))$, proving the stated discrepancy bound, for instance with $c=a/10$. [Erdős–Turán in the primorial setting, Lemma 3.1](https://www.impan.pl/shop/en/publication/transaction/download/product/82868)

### The slowest scale visible after removing a fixed turn

There is a sharp transition for the same trace on $[N,2N]$. Let $0<|\tau_N|\le1$, $L=\log N$, and allow an arbitrary linear twist. Define
$$
 W_N=\frac1N\sup_{\eta\in\mathbb R}\ \sup_{[a,b]\subseteq[N,2N]}
 \left|\sum_{a\le n\le b}e(\tau_N\log R_n+n\eta)\right|.
$$
Then $W_N\to0$ if and only if $A_N=N|\tau_N|/L\to\infty$.

For sufficiency, write $E_N=C\log L/L^2$ for a bound in (1) on this dyadic interval. Take $k=\min(A_N^{1/4},(LE_N)^{-1/2})$, $H=\lfloor kL/|\tau_N|\rfloor$ and $\delta=|\tau_N|/(L\sqrt{k})$. Here $k\to\infty$, $H/N\to0$, and $H\delta\to\infty$. The reference varies at speed comparable to $|\tau_N|/(NL)$. The proportion covered by the bad blocks of §2 is $O(k^{-1/2}+H/N)=o(1)$. The accumulated local approximation costs $O(kLE_N+k^2/A_N)=o(1)$. These estimates hold uniformly on every subinterval and for every twist.

Conversely, if $A_N$ stays bounded along a subsequence, choose $\eta=-\tau_N\log(p_N/N)$ on that subsequence. Throughout $[N,N+\gamma N]$, (1) and (2) bound the total phase drift from the incoming phase by $O(A_N(\gamma^2+\gamma LE_N))$. Fix a sufficiently small positive $\gamma$ depending on the subsequence bound. Eventually this is less than $1/12$ of a turn. That subinterval alone has a sum of magnitude at least $\gamma N/3$. This proves necessity.

At the critical scale one can give the shape itself. With $\tau_N=\gamma(\log N)/N$ and $\eta_N=-\tau_N\log(p_N/N)+\xi/N$, the accumulated phase from $N$ to $\lfloor Nt\rfloor$ tends uniformly for $1\le t\le2$, in turns, to
$$
 \gamma(t\log t-t+1)+\xi(t-1).
$$
Indeed $L(g(Nv)-g(N))=\log v+O(\log L/L)$ uniformly on $1\le v\le2$, by (2) with its displayed derivative. The approximation (1) has the same vanishing scaled error. The Riemann sum of $\log v$ from 1 to $t$ gives the formula. In particular the curvature survives centering at the **actual** incoming factor.


## 4. What travels back to the RH question

At the integer cut $m$ the actual retained prime product factors exactly as
$$
 \prod_{x<p\le m}p
  =\frac{\pi(m)!}{\pi(x)!}\,
   \frac{R_{\pi(m)}}{R_{\pi(x)}} \qquad(m\ge x).
$$
The new theorem describes the leading digits of this ratio sequence indexed by prime arrivals. Every physical integer cut samples it at $\pi(m)$, which repeats a value for the length of a prime gap. Equal weight per prime index and equal weight per integer cut are different sampling laws.

There is an exact check on the information supplied by the digit theorem. For any fixed $c$, replacing $R_n$ by $e^{cn}R_n$ adds a linear twist to the fractional logarithms in each base. The uniform estimate above therefore gives the same ordinary Benford law in **every** base, even though the unwrapped logarithmic bill has changed by $cn$. The RH construction still has to bound that unwrapped bill in its own integer frame. [Actual product obligation and its quantifiers](one-product-one-direction-per-board.md)

## 5. Consequences and checks

* **Joint leading digits.** In the two-dimensional Weyl criterion for $(\log_b n!,\log_b P_n)$, a character with frequencies $(r,s)$ involves $\log_b((n!)^rP_n^s)$. If $r+s\ne0$, Bergelson, Kolesnik and Son’s Theorem 4.25(1) supplies its vanishing mean. If $r+s=0$ and the character is nontrivial, the theorem above supplies it. Thus the pair is jointly uniformly distributed in ordinary density. In particular its two leading digits have the product Benford distribution. [Prior noncanceling directions](https://arxiv.org/html/2509.19722v2)
* **Why precision matters.** The error scale in (1) is essential to the short-block proof. For example, take the true smooth reference $g$ and real points $s_k$ with $g(s_k)=k$ for large integers $k$. Replace $g(n)$ by exactly $k$ on $[\lceil s_k\rceil,\lfloor2s_k\rfloor]$ and keep it elsewhere. These disjoint intervals change each increment by only $O(1/\log n)$, by (2). Yet on each altered interval the accumulated unit phase is constant. If the full prefix means tended to zero, subtracting the means multiplied by their prefix lengths at the two endpoints would contradict the constant interval sum of magnitude $\asymp s_k$. This is a control on the argument’s precision, independent of the prime input.
* **Finite observations.** On the first 262,144 terms of $R_n$, exactly 78,909 begin with decimal digit 1. The star discrepancy is enclosed between 0.0011655754 and 0.0011655755. It was larger at 8,192 than at 4,096. Across the 4,096 steps from index 4,096 to 8,192, the true ratio $p_n/n$ decreased 2,237 times and switched sides of 10 seven times. The numerical replay encloses logarithms with rational bounds and checks the first 256 leading digits of each of the primorial and quotient streams independently by integer division. The all-index conclusions follow from the proofs above. [Computations and evidence scope](../receipt-archives/2026-11-26-pal-benford-quotient.json)

Christopher Daniel Pang supplied the PAL/RPL question about retaining the incoming phase when moving a construction to a new frame, and the comparison of prime products with ordinary factorials grew from his independent research program. Hearthline derived the two arguments and the quantitative transfer. Bergelson, Kolesnik and Son are credited for the question and earlier results, and Massé and Schneider for the primorial baseline. The proof uses classical unconditional prime estimates. The full Benford result in this edition is a paper proof with author self-review. The Lean source checks its finite block machinery. The November RH release supplied the occasion for the wider investigation. The mathematical inputs to this result are identified above. Publication priority and external peer review have not been established here. [Pang’s PAL v2.4 atlas](../corpus/PAL_v2.4-M_Mathematical_Realization_Atlas.docx) · [Corpus sources, including RPL](../pal-rh/CORPUS-ROUTES.md)
