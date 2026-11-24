# A strict class gains one digit after base change

**24 November 2026.** The original twist-296 Selmer class has order 577 over $\mathbb Q$. We found a real cyclic field of degree 577 in which the same class becomes divisible by 577. Every place over 577 still has completion $\mathbb Q_{577}$. The upstairs strict group is cyclic of **exact order $577^2$**. Galois conjugation moves the new lift by its original order-577 class. Corestriction excludes this mechanism on every power-of-two zeta host for an odd coefficient prime.

## A tame character with three measured values

Use $p=577$, the original finite conductor-256 character, and its lower coefficient $\xi_j=\psi^{-1}\varepsilon^{-j}$ with residual character $\chi=z^{-1}$ for $j\equiv296\bmod576$. Strict means unramified away from $p$ and locally zero above $p$, with the specified coefficient action. The group over $\mathbb Q$ for the divisible coefficient has order $p$ at every positive twist in this progression. Denote the normalized residual generator by $y$. [Exact order downstairs](2026-11-24-the-last-577th-power-digit.md)

At $q_1=2309,q_2=3463,q_3=20773$, let $\rho_i$ be the rational order-$p$ Dirichlet character written additively using the least primitive roots $2,3,2$. Set
$$ c=290\rho_1+150\rho_2+554\rho_3,\qquad A=\mathbb Q^{\ker c} .$$
All three coefficients are nonzero, so the conductor is exactly $2309\cdot3463\cdot20773=166102299791$. The field is totally real since $p$ is odd. The three characters on arithmetic Frobenius at 577 have values $575,32,334$ respectively. Their indicated combination vanishes. This proves complete splitting at the coefficient prime.

For a lift modulo $p^2$, change the coefficient temporarily to $\xi_j(1-pc)$. The following matrix gives the change in the two strict obstruction readings and the value at the coefficient prime. The first two rows are the independently computed point-unit residues.
$$
\begin{pmatrix}
426&97&234\\
35&522&245\\
575&32&334
\end{pmatrix}
\begin{pmatrix}290\\150\\554\end{pmatrix}
=\begin{pmatrix}-2\\-273\\0\end{pmatrix}\pmod{577},\qquad \det=73 .
$$
Using only the first two primes instead gives coefficients $481,374$ and Frobenius value 43 at 577. The third prime is what makes the coefficient completions agree with the original ones. [Computation of the first two rows](2026-11-24-two-small-primes-read-the-actual-point-units.md)

## Why this gives an actual lift

For the scalar lower problem, the dual classes are the two virtual units of the base field with character $\chi$. In the older Jacobi normalization the basis was $u=e_-^{523}R^{376}$ and $v=e_-^{251}R^{251}$. At the two old auxiliary primes the dual Frobenius matrix is invertible. A strict lift allowing last-digit tame errors there always exists, and its two tame errors are uniquely measured by the two dual classes. For the actual generator $y$, their pairings on $u,v$ are $231(261+37(j+1),202(j+1))$. Converting bases with $R_0=Re_-^{95}$ gives
$$\mathbf O_j=(2,\ 273+190(j-296))$$
on $R,R_0$. [Original obstruction primes, normalizations and weights](2026-11-24-two-independent-obstruction-primes.md#actual-tame-inertia-at-the-lift-from-p-to-p2)

For clarity, the signs of the tame additions can also be derived with the same two old auxiliary primes. Over $k[\epsilon]/\epsilon^2$ lift $y$ with coefficient $\chi(1+\epsilon\rho_i)$, strict at $p$, allowing the two last-digit errors. The old dual Frobenius matrix again removes the obstruction by Poitou–Tate. At $q_i$ the residual coefficient is unramified with $\chi(q_i)\ne1=q_i\bmod p$, so both the unramified and tame pieces of local $H^1$ vanish. The local lift can be made a coboundary. Over the tame coefficient field the resulting two-step group has commutator $[\sigma,\tau]=1$ in the last additive coordinate, since its multiplication contains $\rho_i(g)y(h)$.

Apply the central Artin product of the [point-unit calculation](2026-11-24-two-small-primes-read-the-actual-point-units.md#a-jacobi-carry-gives-the-first-common-value). It reads $[T:\mathbb Q]e_{q_i}(b)$ on a base input $b$. Directly, the strictness at $p$ leaves only minus the two tame errors paired with the Frobenius exponents of $b$ at the old primes, summed over their conjugates. The order-$p$ group kills $p$th powers. Thus the error pairing for the *positive* coefficient perturbation is $-e_{q_i}(b)$. Changing the integral coefficient by $1-p\sum k_i\rho_i$ adds $+\sum k_i e_{q_i}(b)$ to $\mathbf O_j$. This superposition is literal modulo $p^2$. Choose representatives with the same residual $y$ and subtract $p$ times the indicated first-order correction cochains. Their cocycle and local coboundary identities add in that last digit.

At $j=296$ the displayed matrix cancels both errors. Invertibility of the old dual matrix then gives zero tame translation at both former auxiliary primes and an actual lift $Y$ of $y$ for the modified coefficient. The new tame primes only ramify the temporary coefficient. The class is locally a coboundary there. Restrict to $G_A$. The coefficient is now the original $\xi_{296}\bmod p^2$, and $p[Y|_{G_A}]=[y|_{G_A}]\ne0$ in the divisible coefficient. Restriction is injective on the downstairs residual class by inflation–restriction, since the nontrivial residual character still has no invariants over $A$. If $\gamma$ denotes a generator with $c(\gamma)=1$, its action with the original coefficient is
$$\gamma[Y|_{G_A}]=(1+p)[Y|_{G_A}].$$
The action with the modified coefficient made the class invariant. Restoring the original action exposes the nonzero difference $[y|_{G_A}]$.

## Exact size over this field

In the residual coefficient the invariant upstairs strict classes are exactly the downstairs line. Global invariants of the coefficient over $A$ vanish, so inflation–restriction identifies invariant global classes. Local strictness descends at the split prime $p$. At the ramified $q_i$ the unramified and tame local $H^1$ groups both vanish, and at all other finite primes inertia is unchanged by this unramified base change. The same invariant-class argument works for the divisible coefficient.

If there were any second residual direction upstairs, nilpotence of $\gamma-1$ and the one-dimensional invariant line would give a class $s$ with $(\gamma-1)s=y|_{G_A}$. Then $y|_{G_A}+\epsilon s$ would be invariant for the coefficient $\chi(1-\epsilon c)$ and descend, with the strict local conditions, to a dual-number lift downstairs. Its obstruction is the nonzero vector $(-2,-273)$ up to the sign of the chosen generator. This contradicts the two measured residue rows. Thus the residual strict group has dimension exactly one. It gives the full $p$-torsion of the divisible-coefficient strict group. The coefficient sequence is injective on local $H^1$ at $p$ because there are no local invariants. Away from $p$ the inertia-invariant subgroup of the divisible coefficient is either zero or divisible, which preserves the unramified condition.

A $p$-primary abelian group with one-dimensional $p$-torsion is cyclic or Prüfer. In the Prüfer case the order-$p$ Galois group would act trivially, contrary to the finite invariant group. On a cyclic group of order $p^n$, $n\ge2$, an automorphism of order dividing $p$ fixes at least $p^{n-1}$ elements. There are only $p$ invariants here. This proves the upper bound $p^2$ independently of the existence check.

There is an exact twist cutoff within the original progression. If a class of order $p^2$ exists, normalize its multiple to $y|_{G_A}$. Its Galois action is $1+pa c$ for some $a\ne0$ modulo $p$. Twisting back descends it just as above, hence $\mathbf O_j+a(-2,-273)=0$. The first coordinate forces $a=1$, and the second forces $j\equiv296\bmod p$. Conversely these congruences give the lift. The strict group over $A$ therefore has order $p^2$ for $j\equiv296\bmod p(p-1)$ and order $p$ at every other positive $j\equiv296\bmod(p-1)$.

## What this removes from the RH audit

For a finite extension of degree $n$ prime to $p$, suppose $p^k w$ equals the restriction of an original strict $p$-primary class $x$. Corestriction sends strict classes to strict classes and gives $p^k\operatorname{cor}(w)=nx$. Since $n$ is invertible on this group, $x$ was already divisible by $p^k$ downstairs. This works for every odd coefficient prime on the actual trivial-character zeta hosts, whose degrees are powers of two. The conclusion controls the divisibility of the specified restricted class. [Actual host and coefficient comparison](2026-11-24-a-class-inside-the-zeta-windows.md#check-the-group-upstairs)

The example identifies the missing datum in an unrestricted descent argument. The lift can move by the original class under Galois conjugation. In the release the good datum requires the finite-character order to be prime to the coefficient prime. At the marked endpoint the argument starts with a representation already defined over $\mathbb Q$ and restricts it to the linked field to compare characteristic polynomials. Our temporarily ramified coefficient and the noninvariant upstairs class do not supply a failed instance of either statement. [Good-datum hypotheses](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/Counts.lean#L9-L22) · [Restriction of the given representation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CurveDVRSpecialization/FinEndOfFinPt.lean#L22-L39)

## Reproduce

The [finite replay](boundary-577/central_unit_residues.py) recovers both coefficient combinations, checks the relaxed Jacobi multiplier separately, and runs the exact-size criterion across all 577 weight residues in one period.

## Unresolved

At the original fixed weight and level the unknown rank-three quadratic corrections remain. The [two tame inertia tests](2026-11-24-two-tame-inertia-tests-on-the-marked-point.md) put these corrections in a specific basis without changing the original success condition.
