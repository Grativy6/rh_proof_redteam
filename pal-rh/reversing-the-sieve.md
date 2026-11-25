# Turning the prime sieve both ways

Christopher Daniel Pang and Hearthline · 25 November 2026

**We can isolate the first tick with the ordinary prime sieve at a proved vanishing error. The sieve uses a reversed reading. Reusing it as a finite forward fit would change the mathematical interface.** We tried two explicit legal replacements and located their error. The [next construction](close-clocks.md) generates the sieve's signed event on named bands using legal measurements alone.

## The exact source and the missing transfer

Set $Q=B!$ and $\sigma_B(k)=[\gcd(k,Q)=1]$. At positive $k\le B$, $\sigma_B$ agrees with $e(k)=[k=1]$. On every other positive row its absolute error is at most one. Thus $\|e-\sigma_B\|^2\le1/(B+1)$, unconditionally.

Form the finite legal signal and its opposite orientation
$$
S_Q(k)=\sum_{d\mid Q}\mu(d)b_d(k),\qquad
R_Q(k)=\sum_{d\mid Q}\mu(d)b_d(-k).
$$
Here $b_d(-k)$ means the fraction of a turn in the same $d$-frame with the orientation reversed; the reset remains zero. The identity $b_d(k)+b_d(-k)=1-[d\mid k]$, followed by Möbius inversion, gives
$$
S_Q(k)+R_Q(k)=-\sigma_B(k)\qquad (B\ge2).
$$
A rule that approximates the particular reflected $R_Q$ by legal fits to growing precision while $1/(B+1)$ goes to zero suffices for RH. Conversely, first-tick approximation supplies this repair by subtraction. All three claims have [Lean proofs](PALRH/Sieve.lean).

There is a genuine constraint here. For $B\ge3$, $\sigma_B$ is never an exact finite forward fit. If it were, choose an even common period $L$ of its moduli divisible by $Q$ and by 6. The forward frame law would require $\sigma_B(2)+\sigma_B(L-3)=\sigma_B(L-1)$. The readings are respectively 0, 0 and 1. This counterexample concerns exact finite representation. The closure question allows weighted error.

## First attempt — keep the forward signal

Let $\rho=\sum_{d\mid Q}\mu(d)/d=\prod_{\ell\mid Q}(1-1/\ell)$ and $A(k)=\sum_{m=1}^k\sigma_B(m)$. Dividing one row at a time gives the exact identity
$$
-S_Q(k)=A(k)-k\rho .
$$
For $1\le k\le B$ the error of $-S_Q$ against the constant target 1 is exactly $k\rho$. Hence these first $B$ rows alone cost at least $B\rho^2/2$. The product $\rho$ tends to zero, so the reading at **each fixed row** tends to one. The squared error fails to do so.

Here is an elementary bound sufficient to see the failure. Except for 2, 3 and 5, prime factors of $Q$ lie in the eight unit classes modulo 30. In the block $30j+1,\ldots,30j+30$, $j\ge1$, each contributes at most $1/(30j)$ to $\log(1/\rho)$, since $\log(p/(p-1))\le1/(p-1)$. The first block costs a constant. Thus $\rho\ge cB^{-4/15}$ for an absolute $c>0$ by the ordinary harmonic integral bound. For $\rho\to0$, the finite Euler products $1/\rho$ dominate $\sum_{n\le B}1/n$ by unique factorization. These bounds prove that the head cost diverges without assuming any zero-free region.

## Second attempt — put any weight on the very next prime

Let $p$ be the least prime greater than $B$. Choose an arbitrary real coefficient $c'$ and set $F=-S_Q+c'b_p$ and $u=c'/p$. Up to $p-1$ the error is $k(\rho-u)$. If $|\rho-u|\ge\rho/4$, the prefix costs at least $p\rho^2/64$. Otherwise, at $k=p+s$ with $0\le s\le p\rho/4$, the residual is
$$
1-F(p+s)=p\rho+s(\rho-u)-(A(p+s)-1).
$$
The count on the right is at most $s+1$. Thus the residual is at least $p\rho/2$ once $p\rho\ge8$. There are at least $p\rho/4$ such rows and each weighs at least $1/(4p^2)$. The combined squared error costs at least $p\rho^3/64$ for **every** $c'$. The bound above makes this grow at least as a positive constant times $B^{1/5}$. The failure covers this frozen parent and the whole real coefficient axis on the next single prime.

## Third attempt — repay the linear drift using two complete adjacent sieves

Eliminate the linear terms by combining the old and next sieve fits with coefficients $-(p-1)$ and $p$ on the fits $-S_Q$ and $-S_{pQ}$ respectively. Since $p$ is fresh, the result is the legal signal
$$
F(k)=A(k)-p\,A(\lfloor k/p\rfloor).
$$
Indeed survivors removed by the new prime are exactly $p$ times old survivors, and $\rho_{pQ}=(1-1/p)\rho_Q$. Equivalently the fit is $p\rho_Q b_p-S_Q+pD_pS_Q$, so the construction uses only earned dilations, forward readings and rational coefficients.

This fits every positive row below $p$ perfectly. At $p$ it reads $2-p$. The weighted squared error from this single moving row tends to one. Worse, at $p+s$ for $0\le s\le p/4$ the residual is at least $p-s-1$, since $A(p+s)\le s+2$ and $A(1)=1$. For $p\ge5$ those rows alone cost at least $p/64$. The Lean result proves a slightly more general uniform floor of $1/6$ for its legal count repair at every integer scale $p\ge2$, including its perfect prefix. The divergent lower bound and the arbitrary-single-prime calculation above are paper proofs.

## Unresolved

Repair the reflected signal in weighted mean while allowing more than the single reset to share the cost. A nearby pair of forward quotient clocks can read the *actual* signed sieve increment without changing the allowed linear space. Its responsive bands and their exact costs are the next input; how all remaining bands repay the full error is open.
