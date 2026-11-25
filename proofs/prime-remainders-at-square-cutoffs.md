# The released prime window at square cutoffs

Christopher Daniel Pang and Hearthline · 25 November 2026

Pang asked where the remainder goes when the released argument passes from finite measurements to a claim about arbitrarily large scales. His PAL atlas and his work on lattice readouts motivated the comparison below. The function and the window being tested come from the Alpöge–Claude release. The derivation here uses prime factorization, a binomial coefficient, and elementary calculus. [PAL atlas](../corpus/PAL_v2.4-M_Mathematical_Realization_Atlas.docx) · [Pang’s shadow-lattice paper](../corpus/Shadow_Lattice_and_Dispersal_Lattice.pdf)

## The arithmetic test

At a square $j^2$, inspect the integer columns $j<m\le j^2$. Each column contributes its distance up to the **next strictly larger integer** above $j^2/m$,
$$
h_j(m)=1-\frac{j^2\bmod m}{m}.
$$
An exact division contributes one. Add these distances over all the columns. Subtract the same distances over prime columns, each weighted by the natural logarithm of its prime. Call the difference
$$
D(j)=\sum_{j<m\le j^2}h_j(m)-
     \sum_{j<p\le j^2,\ p\ {\rm prime}}(\log p)h_j(p).
$$
At $j=3$, the prime columns are 5 and 7, with gaps $1/5$ and $5/7$. The six integer columns give $1131/280$ in total.

**Proposition.** The following two assertions are equivalent.

1. For each $\delta>0$ there are arbitrarily large real $Y$ such that $G(x)\le x^{1/2+\delta}$ for every real $x\in[Y,Y^{3/2}]$, with $G$ the release’s principal prime sum.
2. For each $\delta>0$ there are arbitrarily large integers $a$ such that
   $D(j)\le j^{1+2\delta}$ for **every** integer $j\ge a$ with $j^2\le a^3$.

The comparison is one-sided. Both assertions quantify over every positive margin. The proof uses a smaller margin to absorb fixed constants.

At level one the retained character set consists of the principal character, hence the nonprincipal part of the level sum is empty. The release feeds its whole-window estimate into a zero-exclusion argument. The proposition expresses the arithmetic estimate at that interface. [Definition of the prime sum, lines 9–13](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/StatementOC.lean#L9-L13) · [Level sum, line 38](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L30-L38) · [Whole-window definition and use](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean#L68-L81) · [Choice of the exponent 3/2](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean#L5-L8)

## What pays for the discarded terms

Write $n=\lfloor x\rfloor$, $h(t)=1-\{x/t\}$ for $0<t\le x$, and let $\Lambda(p^r)=\log p$ for $r\ge1$, with $\Lambda=0$ elsewhere. The release uses
$$
G(x)=\sum_{m\le n}\Lambda(m)(x/m-1)-x\log x+(1+\gamma)x .
$$
Throughout, sums over integers start at one. Factoring $n!$ prime by prime gives $\sum_{m\le n}\Lambda(m)\lfloor x/m\rfloor=\log(n!)$. Consequently
$$
G(x)=R(x)+\gamma x-\sum_{m\le n}\Lambda(m)h(m),
\qquad R(x)=\log(n!)-x\log x+x .
$$
Integrating $\log t$ between successive integers gives $1\le R(n)\le1+\log n$. As $R(x)=R(n)-\int_n^x\log t\,dt$, we have $|R(x)|\le1+\log x$.

The continuous column total is exactly $\int_0^x h(t)\,dt=\gamma x$. Substitute $u=x/t$. On $[r,r+1)$ the resulting integrand after division by $x$ is $(r+1-u)/u^2$. Its integral is $1/r-\log(1+1/r)$. The first $N$ intervals sum to $H_N-\log(N+1)$, which tends to Euler’s constant.

To compare this integral with the integer columns, take $K=\lceil\sqrt x\rceil$ and $x\ge9$. The first $K$ columns cost at most $K$ in total discrepancy because $0\le h\le1$. On each remaining cell $[m-1,m]$, the difference $h(m)-h(t)$ is
$$
(x/t-x/m)-\big(\lfloor x/t\rfloor-\lfloor x/m\rfloor\big).
$$
Both parentheses are nonnegative. Their integrals from $K$ to $n$ are each at most $x/K$ because their upper bounds on consecutive cells telescope. Therefore the absolute difference of the two totals is at most $x/K$. The leftover interval $(n,x]$ costs at most one. This proves
$$
\left|\sum_{m\le n}h(m)-\gamma x\right|\le K+x/K+1\le2\sqrt x+2 .
$$
Together with $|R(x)|\le1+\log x$ this contributes at most $4\sqrt x$ for $x\ge9$, since $\log x\le\sqrt x$ there.

Write $\vartheta(y)=\sum_{p\le y}\log p$. The product of primes in $(b,2b]$ divides $\binom{2b}{b}\le 2^{2b}$ for each positive integer $b$. Summing over dyadic blocks up to the first power of two at least $y$ gives $\vartheta(y)\le4y$ for $y\ge1$. The prime squares up to $x$ cost at most $4\sqrt x$. For powers of exponent at least three, each base prime up to $x^{1/3}$ costs at most $\log x$ over all its exponents, so their combined cost is at most $x^{1/3}\log x\le6\sqrt x$. All these bounds also hold with the weights $h(m)\in[0,1]$.

On discarding the first $\lfloor\sqrt x\rfloor$ columns, the ordinary column total loses at most $\sqrt x$ and the prime total loses at most $4\sqrt x$. In particular, at a square,
$$
-18j\ \le\ G(j^2)-D(j)\ \le\ 5j \qquad(j\ge3).
$$
For the lower bound the two negative contributions are the small primes and the higher powers. For the upper bound only the small ordinary columns can add to the $4j$ centering error.

## Why a spike between squares is covered

The ramp $G$ is continuous, including at integers where a new summand starts at zero. Between integers,
$$
G'(x)=\sum_{m\le x}\Lambda(m)/m-\log x+\gamma
=\gamma-1+\frac{R(x)+\sum_{m\le x}\Lambda(m)\{x/m\}}{x}.
$$
The second equality uses the same factorial identity. The preceding bounds give $\sum_{m\le x}\Lambda(m)\le4x+10\sqrt x$. Since $|R(x)|\le1+\log x\le x$ and $0\le\gamma\le1$, we have $|G'(x)|\le10$ on each open piece for $x\ge9$. Summing across the finitely many pieces between any two arguments gives a single Lipschitz bound of 10 on $[9,\infty)$.

Take $j=\lfloor\sqrt x\rfloor$. Then $0\le x-j^2<2j+1$, so
$$
|G(x)-D(j)|\le10(2j+1)+18j\le42j\qquad(j\ge3).
$$
For assertion 2 implying assertion 1, use integer windows at margin $\delta/2$ and set $Y=a^2$. Every $x\in[a^2,a^3]$ has an admitted lower square. Its bound becomes $G(x)\le x^{1/2+\delta/2}+42\sqrt x$, at most $x^{1/2+\delta}$ eventually.

Conversely, take a real good window at margin $\delta/2$ and set $a=\lfloor\sqrt Y\rfloor$. Every tested square except possibly $a^2$ already lies between $Y$ and $Y^{3/2}$. At those squares, $D(j)\le j^{1+\delta}+18j$. At the first square, $D(a)\le G(Y)+42a\le(a+1)^{1+\delta}+42a$. Both bounds fit the claimed $j^{1+2\delta}$ once $a$ is sufficiently large. This proves the proposition in both directions.

## Trying to hide prime-free runs just beyond a square

Take $j=r!$ for any integer $r\ge2$. All of $j^2+2,\ldots,j^2+r$ are composite, since each offset divides $j^2$. This puts arbitrarily long runs of missing primes exactly beyond square samples. At any later square $k^2$ where some of these columns are counted, they contribute at most $r-1$ to the deficit, since each such column contributes only $h_k(m)\le1$.

The entire family of these runs also has a uniform budget. Any contributing run has $r!\le k$, hence $2^{r-1}\le k$. Summing $r-1$ up to $1+\log_2 k$ bounds the total by $O((1+\log k)^2)=o(k)$. A single run could occur where other columns have already accumulated a large deficit. The contribution of all these deliberately planted columns is too small to supply a square-root-sized deficit on its own.

## Unresolved

The open question in this audit is how the selected arithmetic and geometric inputs give the required prime contribution throughout arbitrarily late blocks. In the released transfer the chosen host can depend on $x$. Its estimates must apply to that host at the same $x$, with constants chosen early enough for the whole window. The signed character measurement also needs the three discarded-character estimates to recover the principal reading. The square-cutoff calculation does not derive these inputs. [Host and index at the point of use](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/WindowInequalityOfArtinInputs.lean#L17-L25) · [Four-character reconstruction](../receipt-archives/2026-11-24-taking-rhofall-apart-at-the-four-characters.md)
