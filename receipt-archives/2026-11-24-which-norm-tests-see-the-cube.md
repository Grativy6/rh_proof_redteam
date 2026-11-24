# Which norm tests see the cube at 577?

**24 November 2026.** On the original fixed conductor-256 input, the mixed first-order field has **three independent failures of the Hasse norm principle**. Every subextension of degree at most $577^3$ over its residual splitting field satisfies that principle. Thus testing all cyclic, bicyclic and rank-three quotients would certify every everywhere-local norm while missing a group of order $577^3$ globally. Among the $111034152581$ subextensions of degree $577^4$, exactly **333507** can detect a failure. We identify them and use one for the [ordinary cube test](2026-11-24-four-norm-kernels-for-the-two-quadratics.md). This calculation uses the original class at twist 296 throughout.

## The first-order fields and their local groups

Set $p=577$, $k=\mathbb F_p$, $F=L_y\mathbb Q(\sqrt{-7})$ and $M_0=M\mathbb Q(\sqrt{-7})$ as in the [affine class-field computation](2026-11-24-the-affine-resolvent-and-its-class-groups.md). Write $C=aC_U+bC_V$ for the two genuine, globally normalized odd cocycles. Over $F$ the residual action is trivial, so $C$ is an abelian character with values in polynomials. Denote its first-order field by $B_C$. Here a mixed direction means $a,b\in k^\times$. The polynomial basis is $B_i=T^i$, $0\le i\le4$, with the previously specified character twist and matrix normalization.

At one place above $p$ two units give $35aT^3$ and $387bT^4$. At its translates their spans become the spans of $(T-t)^3,(T-t)^4$ for $t\in k$. The complement acts by scalars on the two lines at the original place. These are the full local images. Their tame characters are nontrivial and distinct, so the displayed ramified lines exhaust the local tangent classes and leave no extra unramified component. Away from $p$, $B_C/F$ is unramified and each decomposition group is cyclic. By finite differences the global image $W$ is the whole space of cubics for pure $U$, or of quartics if $b\ne0$. The two pure extensions taken together have image the direct sum of the four- and five-dimensional spaces. The two local generators separately span each direct summand under translation. [Local Artin inputs](2026-11-24-four-local-units-at-577.md) · [Global images](2026-11-24-three-global-quadratic-readings.md#read-the-quadratic-residue-without-knowing-the-global-primitive)

In particular the compositum of the two pure first-order fields is everywhere unramified and split above $p$ over the subfield obtained from $F$ by adjoining just the two **top** cyclic extensions. It has degree $p^7$ there. Indeed the top coefficients have independent local readings at every place above $p$, and their kernel in the joint nine-dimensional image has dimension seven. These top fields come from the two original circular units. Separately, pure $U$ gives an unramified, $p$-split extension of degree $p^3$ over its top field over $F$, and pure $V$ one of degree $p^4$. This locates the first-order characters still present after the explicit top radicals have been adjoined.

## A global obstruction computable from all decomposition places

For an abelian extension $B/F$ with group $W$, write
$$\mathcal K(B/F)=\{x\in F^\times:x\text{ is a norm at every completion}\}/N_{B/F}B^\times.$$
Tate's class-field calculation identifies this group with $\bigwedge^2 W/\sum_v\bigwedge^2 D_v$, with the local wedges included in the global wedge. In the class-formation sequence the kernel of the local norm test is the cokernel of the maps from local Schur multipliers to the global one. For abelian groups these multipliers and maps are their exterior squares and inclusions. A cyclic unramified local group has zero exterior square. The criterion also applies to every quotient $W/R$ with the local groups projected to that quotient. [Razar, §§4–5, Theorem 3 and Lemma 4](https://www.numdam.org/article/CM_1977__35_3_281_0.pdf#page=12)

| Actual extension over $F$ | $\dim W$ | Dimension supplied by local wedges | $\dim_k\mathcal K$ |
| --- | ---: | ---: | ---: |
| Pure $U$ | 4 | 0 | 6 |
| Pure $V$ | 5 | 0 | 10 |
| Mixed, $ab\ne0$ | 5 | 7 | 3 |
| Both pure fields jointly | 9 | 8 | 28 |

For a mixed direction the local wedges are multiples of $(T-t)^3\wedge(T-t)^4$. The vector has polynomial degree six in $t$. Its seven coefficients are nonzero and supported in different total degrees of the two basis positions. The Vandermonde matrix on $k$ consequently gives rank seven. For the joint field the two factors lie in different direct summands, and their tensor polynomial has all eight degrees zero through seven. This gives rank eight. The [finite replay](boundary-577/first_order_norms.py) also computes the ranks directly using all 577 translates.

## The obstruction the global bracket measures

In the mixed case the bracket $\beta:\bigwedge^2 W\to E_{\mathrm{Lie}}=k[T]_{\le2}$ vanishes on all the displayed local wedges. It is onto by the explicit matrix brackets, so it identifies the three-dimensional quotient above with the even Lie space. There is an arithmetic way to read a norm obstruction with that same choice of even coordinates. Let $N/F$ be the canonical relaxed lift modulo $\delta^3$. Its abelianization field is $B_C$, its central commutator group has the three even coordinates, and every local decomposition group of $N/F$ is abelian. At $p$ this last assertion follows because the local first-order matrices commute and second-order terms are central over $F$.

Given an everywhere-local norm $x$ from $B_C$, multiply its local Artin symbols in $N/F$ over all places of $F$. Each lies in the central subgroup and is independent of the choice of place above it. A global norm from $B_C$ gives product one by local norm functoriality and global reciprocity for the abelian extension $N/B_C$. The resulting map $\Psi_N:\mathcal K(B_C/F)\to E_{\mathrm{Lie}}$ is surjective. For each prescribed central element, choose a prime of $F$ with that Frobenius in $N$ and trivial Frobenius in a ray class field of $F$ of sufficiently large modulus at $p$. These prescriptions agree on the intersection, since every abelian subfield of $N/F$ lies in $B_C$. A ray-principal generator is a local norm from $B_C$ everywhere and has the specified product of local symbols. This proves surjectivity without an assumption about global unit norms. Comparing the two group orders gives an isomorphism in the mixed case. Its commutator on the abelian quotient is precisely the exterior bracket, with the fixed matrix convention. The nonzero defect classes can also be represented by totally positive elements of the real field $L_y$ since one may multiply a representing element by its complex conjugate and use that this doubles an even class in odd characteristic.

Three actual central words give independent labels for the norm-defect cosets. Take the commutator of the first measured unit with the second conjugated by $\gamma^s$, where $y(\gamma)=1$ and $s=1,2,3$. With $a=b=1$ their rows on $A_0,A_1,A_2$ are
$$\begin{pmatrix}467&357&330\\548&548&166\\322&407&85\end{pmatrix},\qquad\det=40\bmod577.$$
Indeed bracket $35T^3$ with $387(T-s)^4$. The coefficients before multiplication by $35\cdot387$ are $s^4/8,s^3/4,-3s^2/8$. These words label definite global obstruction classes by the isomorphism. The Chebotarev argument proves the existence of principal representatives. Their explicit field elements have yet to be calculated.

## Why every three-generator quotient misses it

Test a functional $\lambda=(u,v,w)$ on $E_{\mathrm{Lie}}$ in the indicated even basis. In $16\lambda\beta$ the nonzero upper-triangular entries, in positions $03,04,12,13,14,23$, are
$$-2u,\ -8v,\ u,\ v,\ -2w,\ w.$$
The vector of signed four-by-four Pfaffians is the coefficient vector of
$$-2(w-2vT+uT^2)^2.$$
It is nonzero for every nonzero functional. The alternating form has rank four and the displayed square spans its radical. For a quotient $W/R$, the dual of its norm-defect space consists precisely of the combinations $\lambda\beta$ with $R$ in their radicals. Every alternating form on a space of dimension at most three has rank at most two. This proves the assertion about **all** proper quotients of those ranks. It also shows that a one-dimensional $R$ detects an obstruction exactly when it is the square of a quadratic in the above coordinates. Squaring is injective on projective quadratic polynomials in odd characteristic, so exactly $p^2+p+1$ lines qualify. Each corresponding degree-$p^4$ extension has a single $C_p$ norm obstruction. The program checks the Pfaffians in every projective direction over the actual residue field. The polynomial identity supplies the calculation over extensions too.

In particular, for the functional $A_0^*$, $R=kB_4$. For $A_1^*$ it is $kB_2$, and for $A_2^*$ it is $kB_0$. The $\lambda$ coordinate of $\Psi_N(x)$ vanishes exactly when $x$ is a global norm from $B_C^R$, for any $x$ already known to be a local norm from $B_C$. One can see this without identifying duality signs. First kill $\ker\lambda$ in the central subgroup of $\operatorname{Gal}(N/F)$. The inverse image of $R$ is now central, and the truncated congruence group over $F$ has exponent $p$, by its two-step matrix law. Quotient by a complement to the remaining center in that inverse image. The resulting central extension over $B_C^R$ has commutator $k$ and abelian local groups. Its Artin-product map is onto by the same ray-prime argument, and the norm defect of $B_C^R/F$ has order $p$. On our element $x$ its Artin product is exactly $\lambda\Psi_N(x)$. Only the field $B_C^R$ is needed to state the norm test.

## Unresolved

This determines the global information which the smaller norm tests lose, and the exact four-dimensional first-order quotients which can recover it. The [four-field criterion](2026-11-24-four-norm-kernels-for-the-two-quadratics.md) singles out the elements whose norm status would decide the original cube question. Existence of other non-norms in these fields does not determine their answers.
