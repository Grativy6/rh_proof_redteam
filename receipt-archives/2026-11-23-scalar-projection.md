# A positive scalar pairing that the projection sends to zero

**23 November 2026.** For one admitted source we give two integral tests of the required degrees. Both satisfy even the unrelaxed incoming link conditions. The first pairing is strictly positive before projection and **exactly zero afterwards**, for every choice of the two diagonal corrections that the construction permits. The second pairing has valuation **41524 both before and after**. The incoming test that the proof needs must have valuation below **41565**. The positive scalar that disappears has valuation **at least 81024**. The input, the lost scalar, the surviving witness and the numerical distinction between them can all be checked without Lean. [Incoming test and promised scalar precision](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CollapseExponent.lean#L81-L101) · [Operator used in the proof](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/OmegaValue.lean#L108-L119)

## One source and two tests

Write $[a,b]=a_1b_2-a_2b_1$ and $u(a)=a_1+a_2$. Set $p=P=79$, $M=N=79000$ and $c=1000$. The two-segment chain is the one in the [frame derivative calculation](2026-11-23-frame-derivative.md). All letters are vectors. The ordinary letters are $x$ of degree $M$ in segment zero and $z,z'$ of degrees $N+1,1$ in segment one. The only frame of positive degree is $t$ at index one of segment zero, of degree $d=M+PN+1$. All frame powers are $P$. The pairing weights on the true side are one. Use the same local field, with $v_p(p)=1$.

Each segment has one chain containing all its entries. Set the chain thresholds to $0,N+1$, the active link thresholds to $M,1$, and both slacks to $54001$. The second chain sees $z,z'$ and the power copies from segment zero. Its projection cutoff is $79001-54001=25000$. The other cut is negative. Since $2(N+2)/P+52c<54001$, the slack suffices. We have $e_P<20$, $D_m+D_l<80$, and $\kappa<42$, whence $4(D_m+D_l+3\kappa)<824<c$. Legendre's formula gives $n_0=41524$. These inequalities use the local released constants with $C_0=1$. [Membership and budgets](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/Lemma5aAt.lean#L246-L294) · [Internal constants](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/LiftBoundOfHypotheses.lean#L257-L268) · [Constants supplied by the release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments.lean#L14-L26)

In the model $L,T$ both specialize to $t$, and $W_i$ specializes to $t_i^P$. Put $S=z_1t_2^P-z_2t_1^P$. Use the true input $F$ and the model tests $Y,Z$ below.
$$
\begin{aligned}
 F &= [x,t]^M t_2 S^N [z,z'],\\
 Y &= [x,T]^M L_2 [z,W]^N [z,z'],\\
 Z &= [x,T]^M L_2\, u(z)^N u(W)^N [z,z'].
\end{aligned}
$$
The digit parts of $F$ contain $[z,W]^N[z,z']$ and have minimum second-chain weight at least $N+1$. The true links see $[x,t]^M$ and $[z,z']$ respectively. Thus $F$ meets `XX`. Both model tests satisfy `Good`. The low exponent is one, the extra degree is $M$, and their true link counterparts and model links satisfy the specified thresholds by the indicated determinants. In particular $\phi Y=F$. The normalized source is $F_0=p^{-41524}F$, as checked below. [Copies, digits and links](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/Lemma5aAt.lean#L221-L257) · [Allowed exponents and true pairing](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CollapseExponent.lean#L17-L36)

## Why the corrected operator kills $Z$

On each multidegree, let $\Pi$ be the Fock-orthogonal projection to the chain cutoff and $D_+,D_-$ the diagonal multipliers in the release. Its operator is $\Omega=D_-\Pi D_+$. The chain has no low-digit letters, so each multiplier lowers its minimum weight by at most $12c=12000$. Diagonal multipliers are self-adjoint for the bilinear Fock pairing. [Projection and orthogonality](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/LiftBoundOfHypotheses.lean#L163-L179) · [Permitted diagonal corrections and projection](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CollapseExponent.lean#L103-L121) · [Order of the three operations](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/OmegaValue.lean#L108-L119)

The test $Z$ pairs to zero with every model polynomial of minimum second-chain weight at least two. To see this, use the same change of coordinates on $z,z',W$ taking $u(a)$ to a multiple of the first coordinate. The matrix with rows $(1,1)$ and $(1,-1)$ is orthogonal up to the scalar 2, so it preserves Fock orthogonality in each multidegree. Each monomial of the transformed $Z$ uses the second coordinate of the chain exactly once, in $[z,z']$. A polynomial of minimum weight two has no such monomial in any basis.

Consequently, for every $H$ in the range of $\Pi$, the weight of $D_+H$ is at least $25000-12000=13000$. Thus $\langle H,D_+Z\rangle=0$ and $\Pi D_+Z=0$. The Fock pairing on this weight subspace has a rational Gram matrix. Positivity over the reals gives a nonzero Gram determinant, which stays nonzero after extending scalars. It follows that $\Omega Z=0$ for all the allowed corrections.

For $Y$, the starting weight is $79001$. Consequently $D_+Y$ still lies above the cutoff and $\Pi D_+Y=D_+Y$. On its support the product of the two multipliers is congruent to one modulo $p^c$. The paired scalar for $Y$ therefore only requires a diagonal calculation, made below. [Unit congruences](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CollapseExponent.lean#L103-L109)

## The values before projection

For any two polynomials $A(t),B(t)$ homogeneous of degree $D$ in $t$, expansion in $x$ gives
$$
 \langle [x,t]^M A,[x,t]^M B\rangle
 = M!\frac{(D+M+1)!}{(D+1)!}\langle A,B\rangle .
$$
For a monomial of exponents $a,b$ in $t$, its norm multiplier is $(M!)^2\sum_i\binom{a+i}{i}\binom{b+M-i}{M-i}=(M!)^2\binom{D+M+1}{M}$. Distinct monomials stay orthogonal after summing over $x$. The same calculation for $[z,z']$ supplies $N+2$. Take $D=PN+1$ and write $C=(N+2)M!(D+M+1)!/(D+1)!$. Put $b_j=(Pj)!/j!$. The true pairings before source normalization are
$$
\begin{aligned}
 B(F,\phi Z)&=C(N!)^2\sum_{k=0}^N(-1)^k\binom Nk b_k b_{N-k}\big(P(N-k)+1\big),\\
 B(F,\phi Y)&=C(N!)^2\sum_{k=0}^N b_k b_{N-k}\big(P(N-k)+1\big).
\end{aligned}
$$
This follows by matching the exponents of $z$ and $t$ in the binomial expansions. [Definition of the factorial pairing](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/ObjPol.lean#L56-L62)

**The first number is strictly positive.** Since $N$ is even, symmetry replaces $P(N-k)+1$ by the constant $1+PN/2$ in its sum. The numbers $b_j$ are moments of a positive, nonconstant real variable $U$. For an explicit one, take $P^P$ times the product of independent gamma variables of shapes $i/P$, scale one, for $1\le i<P$. Integration by parts gives moment $(i/P)_j=(i/P)(i/P+1)\cdots(i/P+j-1)$. Multiplying these rising factorials gives $\mathbb E U^j=(Pj)!/j!$ directly. If $V$ is an independent copy, the alternating binomial sum is $\mathbb E(V-U)^N>0$. This establishes nonvanishing over the rationals. A small instance with $P=5,N=2,M=1$ has unnormalized pairing $4492800000$.

**The first number is very divisible by 79.** For $P=p$, write $b_j=(p!)^j g_j$. Then
$$
 g_j=\prod_{t=0}^{j-1} R(t),\qquad
 R(t)=\prod_{i=1}^{p-1}(1+pt/i).
$$
The coefficient of $t^m$ in $R$ is divisible by $p^m$ in $\mathbb Z_p$. In expanding $g_j$ modulo $p^a$, terms of total positive degree $b<a$ involve $s\le b$ distinct positions. The sum over $0\le t_1<\cdots<t_s<j$ of $\prod t_i^{m_i}$ is a rational polynomial in $j$ of degree at most $b+s\le2b$ because each successive finite sum raises degree by at most one. The expansion of $g_k g_{N-k}$ at total cost $b<a$ obeys the same degree bound in $k$. Take $a=N/2$. Its alternating binomial sum is zero for every retained term because its degree is less than $N$. The discarded terms are divisible by $p^a$ on every integer input. This proves the lower bound $v_p(\sum_k(-1)^k\binom Nk g_k g_{N-k})\ge39500$.

For $Y$, each $g_k$ is one modulo $p$. After extracting $(p!)^N$, the unsigned sum is congruent to $N+1=1\bmod p$. Finally $v_p(C(N!)^2(p!)^N)=83048=2n_0$. This follows from $v_p((pN)!)=N+v_p(N!)$ and the fact that $D+1,d+1,N+1,N+2$ are units. Thus the raw values have valuation at least $2n_0+39500$ for $Z$ and exactly $2n_0$ for $Y$.

## Source normalization and the surviving value

Index a term of $F$ by $i$ choices of $x_2$ in $[x,t]^M$, $k$ choices of $z_2$ in $S^N$, and $\epsilon=0,1$ for the $z$ coordinate in the last determinant. These indices give different true monomials. If $e_{ik\epsilon}$ denotes the coefficient valuation plus half the valuation of the monomial factorial, then
$$
 2(e_{ik\epsilon}-n_0)=
 v_p\binom Mi+2v_p\binom Nk-v_p\binom{N+1}{k+\epsilon}
 -v_p\binom d{i+pk}.
$$
Here $\binom{N+1}{k+\epsilon}$ has valuation at most $v_p\binom Nk$, since $N+1$ is a unit. Also $d!/(M!(pN)!1!)$ is a unit, with factorial valuations $81024=1012+80012$. Count choices of $i+pk$ positions in blocks of sizes $M,pN,1$, with $i,pk,0$ taken from the respective blocks. Equivalently, multiply the multinomial $d!/(M!(pN)!1!)$ by $\binom Mi\binom{pN}{pk}$ and first choose the union of the selected positions. The resulting integer is divisible by $\binom d{i+pk}$. Since $v_p\binom{pN}{pk}=v_p\binom Nk$, the right side of the displayed formula is nonnegative. At $i=k=\epsilon=0$ it is zero. This proves $v_{\rm BB}(F)=n_0$.

Each term in the self-pairing of $F_0$ with $\phi Y=F$ consequently has valuation at least $n_0$. Each monomial of $Y$ maps to a different such monomial. Multiplying its contribution by a scalar congruent to one modulo $p^c$ changes the sum by a number of valuation at least $n_0+c$. This proves $v_p B(F_0,\phi\Omega Y)=41524$ for every permitted pair of diagonal corrections. Independently $Y$ itself, with remainder zero, satisfies the final local witness bounds. Its true image has balanced valuation $n_0$, its chain and link weights meet the cuts, and its pairing attains $n_0$. [Outer witness and remainder requirements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/Lemma5aAt.lean#L298-L309)

## Unresolved

The projection discards an actual positive scalar even when the test meets both incoming link thresholds. Its valuation before projection exceeds the detection budget by more than 39000. A different explicit test meets the budget and survives on the same source. This prunes exact preservation of every nonzero pairing as a possible objection to the scalar estimate. The comparison that remains is whether the global lattice actually supplies enough independent tests *within* the required valuation budget when the local estimates are assembled. No identification with the globally selected local data is assumed here. [Local detection and error budgets](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CollapseExponent.lean#L81-L101) · [Exact arithmetic checker](check_scalar_projection.py)
