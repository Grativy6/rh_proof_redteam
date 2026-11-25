# Two rows halve the Bernoulli conductor cutoff

**25 November 2026.** Christopher Daniel Pang’s PAL and APCI question asks which arithmetic operation actually preserves an observable difference. Hearthline followed that question from the [order-17 boundary](the-order-seventeen-class-at-conductor-64.md) to the general odd-conductor input in the November release. Alpöge and Claude supply the Bernoulli-unit lemma under audit and its use to exclude residual Galois classes. They prove their stated cutoff by a shift with two boundary terms. The two-row identity below gives a smaller sufficient cutoff. No claim of first publication in the number-theory literature is made. [PAL atlas](../corpus/PAL_v2.4-M_Mathematical_Realization_Atlas.docx) · [APCI](../corpus/APCI_Declared_Interface_v1.0.0.docx) · [Released statement](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/UnramifiedCocycleIsCoboundaryOfBernoulliUnit.lean#L14-L26)

[Proof collection](README.md) · [Dated derivation](../receipt-archives/2026-11-25-two-rows-halve-the-bernoulli-conductor-cutoff.md) · [Exact row calculation](../receipt-archives/check_two_row_bernoulli_identity.py)

Let $\ell$ be an odd prime, $Q=\ell^d\equiv1\bmod4$, $e=v_2(Q-1)$, $S=2^e$ and $N=2^n$. Take a primitive Dirichlet character $\phi$ of odd conductor $f$ and order dividing $Q-1$, and a primitive character $\xi$ of conductor $N$ with $\phi(-1)\xi(-1)=-1$. Fix any embedding of their values in the algebraic closure of $\mathbf Q_\ell$.

**Theorem.** The generalized Bernoulli number $B_{1,\phi\xi}$ is an $\ell$-adic unit whenever
$$
                              2N\ \ge\ f S^2 .
$$
The release assumes $N\ge f S^2$. Both assertions include $\ell\mid f$. The uniform condition $4N\ge fS^2$ already fails at $\ell=17,d=1,f=1,N=64$. Thus one entire dyadic layer can be removed from this particular sufficient condition. A second entire layer cannot be removed uniformly. Other conditions in the release’s choice of auxiliary conductor have their own purposes. [Bernoulli input to vanishing](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/ChrInvNeg.lean#L197-L209) · [Other conductor requirements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DataEx.lean#L201-L207)

## The signed coefficients and their two observable rows

For $0<a<N$ odd define
$$
 C(a)=\sum_{k=0}^{f-1}\operatorname{sgn}\big(2(a+kN)-fN\big)\,\phi(a+kN).
$$
Write $\zeta=\xi(5)$. It has order $N/4$. Group the defining numerator $\sum_{x=1}^{fN}x\phi(x)\xi(x)$ by $x\bmod N$. Pair opposite residues and then translate by $fN/2$. Oddness in the first pairing and the sign change of $\xi$ in the second give
$$
 B_{1,\phi\xi}=\sum_{j=0}^{N/8-1} C(5^j\bmod N)\,\zeta^j .
$$
In particular $C(a+N/2\bmod N)=-C(a)$. This computation proves integrality before reduction even if the original denominator $fN$ is divisible by $\ell$. Reduce the coefficients to $\mathbf F_Q$ and keep the same notation for their reductions. The reduction of $\zeta$ retains its order, a power of two. [Derivation with the original integer sums](the-order-seventeen-class-at-conductor-64.md) · [Normalization in the release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/LemmaX.lean#L32-L46)

First suppose $h=N/S$ is a multiple of $S$. Set $K=N/(4S)$. The degree of $\zeta$ over $\mathbf F_Q$ is $K$, by $v_2(Q^j-1)=e+v_2(j)$ for $j>0$. Its minimal polynomial is $X^K-\beta$, with $\beta=\zeta^K$ of order $S$. A zero Bernoulli value would force all $K$ coefficients in the basis $1,\zeta,\ldots,\zeta^{K-1}$ to vanish.

Choose $c$ odd with $5^K=1+hc\bmod N$. Such $c$ exists because $v_2(5^K-1)=2+v_2(K)$. For any $a\equiv1\bmod4$ with $0<a<h$, consider the row
$$
 R_a=\sum_{i=0}^{S/2-1}C(a5^{Ki}\bmod N)\,\beta^i .
$$
Every such $a$ is a power of 5 modulo $N$. Changing the starting exponent by a multiple of $K$ rotates one basis row and multiplies it by a power of $\beta$. Wrapping past $S/2$ changes both signs. Consequently if $B_{1,\phi\xi}=0\bmod\ell$, every $R_a$ is zero.

Let $\gamma=\beta^{(ac)^{-1}\bmod S}$. Since $h^2$ is divisible by $N$, the least residue of $a5^{Ki}$ is $a+h(ac i\bmod S)$. Extend the row to a full cycle of length $S$ and substitute the definition of $C$. Writing an argument as $a+hu$ with $0\le u<fS$, its sign changes exactly at $u=fS/2$. The two half-cycles give identical contributions since translation by $fS/2$ preserves $\phi(a+hu)$ and negates $\gamma^u$. The lower half consists of $S/2$ complete blocks of length $f$. A geometric sum now gives
$$
 R_a=-\frac{2}{1-\gamma^f}\,P_a(\gamma),
 \qquad P_a(\gamma)=\sum_{b=0}^{f-1}\phi(a+hb)\gamma^b.
$$
Here $1-\gamma^f\ne0$ since $f$ is odd and $\gamma$ has order $S$.

## The two representatives that leave a unit

Suppose $h>Sf/2$ and $S\mid h$. Choose the sign $\varepsilon\in\{1,-1\}$ for which $Sf/2+\varepsilon\equiv1\bmod4$. Take
$$
                 a=Sf/2+\varepsilon,\qquad a'=h-Sf/2+\varepsilon .
$$
Both lie strictly between 0 and $h$. To check the close case, $S\mid h$ and $f$ odd give $h-Sf/2\ge S/2\ge2$. The two representatives agree modulo $S$, so they use the same $\gamma$. Modulo $f$ they satisfy $a'=a+h$ and $a=\varepsilon$. Shifting the short sum by one term gives
$$
 \gamma P_{a'}(\gamma)-P_a(\gamma)=(\gamma^f-1)\phi(a).
$$
Substitution leaves the whole certificate
$$
                       \boxed{\gamma R_{a'}-R_a=2\phi(\varepsilon).}
$$
The right side is nonzero in odd characteristic. The two rows cannot both vanish. This also works at $f=1$ in the linear range, when the two rows can be rotations of each other.

For $f>1$, the asserted bound $2N\ge fS^2$ implies $h>Sf/2$ and $S\mid h$. Equality would force the odd number $f$ to be a power of two. For $f=1$ only $h=S/2$, or $n=2e-1$, remains. At that boundary the term $h^2\binom i2$ contributes a half-turn. Its signs are $1,1,-1,-1$ periodically. The [boundary calculation](the-order-seventeen-class-at-conductor-64.md) decomposes these signs into the two fourth-root frequencies. The resulting row is $-2(1-I\lambda)/(1-\lambda^2)$ with $I$ of order four and $\lambda$ of order $S\ge8$, hence is nonzero. At $e=2,n=3$ the signed sum is $-1$. This finishes the proof.

The [integer replay](../receipt-archives/check_two_row_bernoulli_identity.py) assigns an independent formal weight to each residue modulo $f$. It verifies the boxed identity by forming the two original rows, multiplying the second by $\gamma$ and comparing every coefficient in $\mathbf Z[X]/(X^{S/2}+1)$. It checks 1,365 instances with odd $f$ from 1 through 129, $e$ from 2 through 8, and three linear-range layers for each pair. The proof above covers all inputs.

For example take $\ell=f=5$, $Q=5$, $N=64$ and the quartic character with $\phi(2)=i$. Then $\xi$ is even, $h=16$, $S=4$, $a=9$, $a'=5$ and $\gamma=\beta^3$. The certificate is $-2$ even though the original Bernoulli denominator is $320$ and one row starts at a multiple of 5. The replay compares the original numerator in $\mathbf Z[i]$ with the signed coefficients and checks both reductions of $i$ modulo 5. At this conductor the release’s inequality would require $N\ge80$.

## What the release’s own shift earns

At its original cutoff set $s=fS\le h$. One can reconstruct the release’s argument without the new choice of representatives. Put $A(u)=\sum_{x\equiv u\bmod N,\,0\le x<fN}x\phi(x)$. Translating by $f$ gives
$$
 \frac{A(u)-A(u-f)}{fN}=\frac{\sum_{a\bmod f}\phi(a)}{N}
                       -\mathbf1_{u<f}\phi(u)
$$
for the least residue $u$. Subtracting $A(0)/(fN)$ as a constant from $A(u)/(fN)$ gives an integral function $g(u)$, since the $f$-step visits every residue modulo $N$ and the displayed differences are integral. The constant drops out of the nontrivial $\xi$ sum. The reduction of $g$ takes values in $\mathbf F_Q$. Iterate the difference $S$ times. The result is a constant minus $\mathbf1_{u<s}\phi(u)$. [Partial sums in the release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/LxPartial.lean#L15-L25) · [Reduction of the actual shift](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/LemmaX.lean#L264-L292)

If the weighted sum were zero, multiplying the argument by any unit $y$ and taking the field trace to $\mathbf F_Q$ would give $\sum_{x\in D}\xi(x)g(xy)=0$ for $D=\{x:\xi(x)^S=1\}$. Indeed the trace of $\zeta^j$ is zero unless $K\mid j$, when it is $K\zeta^j$. The multiplier $K$ is invertible in characteristic $\ell$. Every $x\in D$ is congruent to $1$ or $-1$ modulo $h$. Compare $y=1$ and $y=1-s$. In the first residue class multiplication by $1-s$ sends $x$ to $x-s$, in the second to $x+s$. Because $s\le h$, the only boundary terms are at $x=1,-1$. Together they contribute $-2$, using $\phi(-1)\xi(-1)=-1$. The constant contributions cancel in pairs under $x\mapsto x(1+N/2)$, which preserves the residue modulo $h$ and reverses $\xi(x)$. The supposed zero difference would be $-2$ in odd characteristic. This checks why the stated cutoff works **in the release’s argument itself**. The smaller cutoff above uses representatives nearer the middle of a cycle. [The two comparisons](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/LxCore.lean#L91-L109) · [Boundary terms](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/LxCore.lean#L135-L151) · [Last cancellation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/LxCore.lean#L190-L220)

At the first counterexample to the next whole-layer reduction, $X^8+1$ selects the primitive sixteenth roots and the **degree-seven** detecting polynomial vanishes at $X=11\bmod17$. Its norm is $2^7\cdot17$. The associated class-group eigenvalue is 14 and the class is locally zero at 17. The failure is both an exact arithmetic counterexample to the weaker uniform conductor bound and an illustration of what the published cutoff prevents. The general Bernoulli-unit step earns its original claim. [The field, class and complete Case II application](the-order-seventeen-class-at-conductor-64.md)
