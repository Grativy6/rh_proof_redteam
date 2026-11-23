# The rank-four count needs a second lattice class

**23 November 2026.** The released argument uses a Hermitian genus mass in the dimension count. We tested whether following only the class of its standard lattice could still produce the number in the proof. Over $E=\mathbb Q(\sqrt3,i)$, the standard class contributes **$1/48$** to the ratio of the rank-four and rank-three masses. A second class contributes **$3/40$**, or **$18/23$ of the total**. We constructed a lattice in that class, counted its automorphisms and evaluated the release's Euler factors. The total on both sides is **$23/240$**. [Mass in the two dimension factors](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CmQuadraticFormEqAlternatingForm.lean#L18-L26) · [Released numerical expression](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/HermitianLattices/StatementMass.lean#L30-L48) · [Hypotheses of the ratio](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/HermitianLattices/StatementMass.lean#L67-L76)

## Field, ranks and evidence

Set $F=\mathbb Q(\sqrt3)$, $E=F(i)=\mathbb Q(\zeta_{12})$, and write $O=\mathbb Z[i,\omega]$ with $\omega^2+\omega+1=0$. Conjugation fixes $F$. The discriminants are $d_F=12$ and $d_E=144$. For instance $\mathbb Q(i)$ and $\mathbb Q(\omega)$ have coprime discriminants $-4,-3$, and their product basis gives discriminant $(-4)^2(-3)^2$. Hence $E/F$ is unramified at all finite places. It satisfies the release's condition on conjugation at every residue prime. At an inert prime conjugation acts nontrivially on the residue field, and at a split pair the Chinese remainder theorem separates the two residues. Use $h(x,y)=\sum\bar x_j y_j$ and $L_m=O^m$. Both statements tested, $m=3,4$, are inside the quantified range of the mass theorem. This field and these ranks are an arithmetic test of that theorem. The proof's asymptotic family has additional host and rank requirements.

The standard genus has **one class in rank three and two in rank four**. For the completeness of these lists we used Markus Kirschmer's classification, `8.3, pp. 133 and 138, in the rows for $\mathbb Q(\sqrt3)(i)$ with empty genus symbol. His electronic tables identify the standard form and the identity basis in entries `Result3CN1[9]` and `Result4CN2[12]`. The classification uses mass methods. The construction and the finite neighbor counts below give separate checks on the existence of the second class and the two automorphism orders. [Classification, `8.3](https://www.math.uni-bielefeld.de/~mkirschm/papers/herm.pdf#page=133) · [Author's tables and notation](https://www.math.uni-bielefeld.de/~mkirschm/forms/#hermitian)

The only vectors of norm one in $L_m$ are roots of unity on individual coordinate axes. For any nonzero $a\in O$, the two positive conjugates of $a\bar a$ have product a positive integer. Their sum is at least two. A vector of norm one therefore has a single nonzero coordinate, with all its conjugates of absolute value one. The roots of unity are $\mu_{12}$. Thus $|\operatorname{Aut}(L_m)|=12^m m!$ and the rank-three mass is $1/10368$.

## A neighbor with no unit vector

Let $\pi=1+i$, $P=(\pi)$, $v=(1,1,1,1+2\omega)$, and use the convention $v^*x=\sum\bar v_j x_j$. The residue field is $\mathbb F_4$, the ideal $P$ is fixed by conjugation, $v^*v=6$, and $\pi\bar\pi=2$. Define
$$
 K=\{x\in O^4:v^*x\in P\},\qquad
 w=3e_1-v/\pi,\qquad L^\sharp=K+Ow .
$$
This really is in the genus used by the release. Away from $P$ the lattice is $O^4$ after localization. At $P$ the rational map $g=I+(i-1)vv^*/6$ is unitary. It acts by $i$ on $v$ and fixes the orthogonal complement. Its coefficient has valuation $-1$ at $P$, and $v^*gx=i\,v^*x$, so it preserves $K_P$ in both directions. Since $3ge_1=w$ and 3 is a unit at $P$, $g(O^4)_P=L^\sharp_P$. This also proves self-duality. [The actual genus test](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/HermitianLattices/StatementLat.lean#L57-L81)

Every integral vector of $L^\sharp$ belongs to $K$, which excludes every norm-one coordinate vector. For a nonintegral $x\in L^\sharp$, all four coordinates of $\pi x$ are nonzero modulo $P$, since $v\bmod P=(1,1,1,1)$. Thus $\operatorname{Tr}_{F/\mathbb Q}h(x,x)\ge4$. A norm-one vector would have trace two. This distinguishes $L^\sharp$ from $L_4$ by hand.

## Counting the automorphisms from both ends

Use self-dual $P$-neighbors whose intersection has index $|O/P|$ in each lattice. At $L_4$ their possible lines in $\mathbb F_4^4$ are isotropic for the reduced form. Each nonzero residue has norm one in $\mathbb F_2$, so the support of a line has size two or four. There are $27=3^4/3$ full-support lines. Each gives two neighbors. Indeed the intersection is the inverse image of the orthogonal hyperplane. For the line of $v$, the possible extensions different from $L_4$ are generated modulo $K$ by $v/\pi+b e_1$, $b\bmod P\in\mathbb F_4$. Integrality of the norm imposes $b+\bar b=0$ in $\mathbb F_4$. This leaves two choices. The diagonal unitary map multiplying coordinate one by $i$ interchanges them, since $(i-1)/\pi$ has nonzero residue and $e_1\notin K$. Monomial unitary maps act transitively on full-support lines. Both lifts have the isometry type of $L^\sharp$. A two-coordinate line leaves an unused coordinate unit in the intersection. Thus exactly **54** neighbors of $L_4$ have type $L^\sharp$.

Conversely, a standard neighbor of $L^\sharp$ contains norm-one vectors $y/\pi$ with $y\in L^\sharp$ of norm two. Each such $y$ is primitive at $P$. Its neighbor is unique, with intersection $\{x\in L^\sharp:h(y,x)\in P\}$ and additional generator $y/\pi$. The following count also gives an integer-only way to reproduce the comparison.

| Shape of $y$ | Count |
| --- | ---: |
| Integral with one nonzero coordinate, a root of unity times $\pi$ | 48 |
| Integral with two root-of-unity coordinates of the same residue | 288 |
| Nonintegral with all four coordinates of $\pi y$ roots of unity | 384 |

The trace bound exhausts the possible shapes. In the last row, write the four numerators as $\xi i^{e_j}$ with the same $\xi\in\mu_3$. Membership is equivalent to $\sum e_j$ odd. This follows by reducing $v^*(\pi y-b\pi w)$ modulo $\pi^2$, with $b\equiv-\xi\bmod P$ and $v_j\equiv1\bmod\pi^2$. Exactly half of the $3\cdot4^4$ tuples remain.

The 720 vectors give **15** neighbors, each with 48 norm-one vectors. The [integer checker](check_hermitian_mass.py) groups two vectors $y,y'$ precisely when they span the same residue line of $L^\sharp/PL^\sharp$ and $h(y,y')\in2O$. Indeed this is the condition $y'/\pi\in K_y+O(y/\pi)$ for the intersection $K_y$ just described. The distinct occupied residue lines all have 48 vectors, and all pairs on each line satisfy the last congruence. Norm-one vectors in an integral positive lattice are mutually orthogonal or differ by a root of unity. Cauchy–Schwarz bounds every conjugate of their inner product by one, and a nonzero inner product must attain equality everywhere. Consequently 48 vectors give four mutually orthogonal unit axes and an orthonormal basis of the self-dual lattice. This identifies each of the 15 neighbors as standard.

Counting rational isometries carrying one lattice to a neighbor of the other, and then inverting those isometries, gives
$$
 54\,|\operatorname{Aut}(L^\sharp)|=15\,|\operatorname{Aut}(L_4)|.
$$
It follows that $|\operatorname{Aut}(L^\sharp)|=138240$ and $|\operatorname{Aut}(L_4)|=497664$. These agree with the two entries on p. 138 of the classification. In units of the rank-three mass their contributions are $10368/138240=3/40$ and $10368/497664=1/48$.

## Number supplied by the release

Here $f=2$ and $v_{\rm inv}=\sqrt3$. For $m=4$ the release's Euler product is $\zeta_F(4)=\zeta(4)L(4,\chi_{12})$. Each split conjugate pair contributes two square roots; at an inert prime the square root of its absolute norm is the residue cardinality downstairs. The primitive character $\chi_{12}$ is positive at $1,11$ and negative at $5,7$ modulo 12. For $B_4(x)=x^4-2x^3+x^2-1/30$ one finds
$$
 \sum_{a=1}^{12}\chi_{12}(a)B_4(a/12)=-23/216 .
$$
The fourth Fourier series of $B_4$ and the Gauss sum $\sqrt{12}$ give $L(4,\chi_{12})=23\pi^4/(648\sqrt{12})$. With $\zeta(4)=\pi^4/90$, the released ratio evaluates to
$$
 12^{7/2}\left(\frac{6}{(2\pi)^4}\right)^2\zeta(4)L(4,\chi_{12})
 =\frac{23}{240}=\frac1{48}+\frac3{40}.
$$
[Archimedean factor and split and inert Euler factors](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/HermitianLattices/StatementMass.lean#L25-L42)

The first live ratio $m=3$ gives $1/36$. The relative quadratic character has product $L(3,\chi_{-4})L(3,\chi_{-3})$. This follows either from the four Dirichlet factors of the biquadratic field or directly from the Euler factors. The two values are $\pi^3/32$ and $4\pi^3/(81\sqrt3)$, obtained from the sine series of $B_3$ at $1/4,1/3$. Multiplying by $12^{5/2}(2!/(2\pi)^3)^2$ gives $1/36$.

There is a short independent check of the binary denominator. Every lattice in the genus of $O^2$ is self-dual and has Euclidean covolume $9$ in its two complex embeddings of each coordinate. The covolume of one copy of $O$ is $\sqrt{144}/4=3$, and conjugate determinant valuations in the genus cancel. For a lattice in eight real dimensions of shortest length $\lambda$, integrating $\max(1-2\|x\|^2/\lambda^2,0)$ over a fundamental cell with all its lattice translates gives $\lambda^8\le 2^4\cdot5\cdot9/(\pi^4/24)<4^4$. Indeed the sum of translates at each point is at most one by the pairwise squared-distance identity. The squared length is $\operatorname{Tr}_{F/\mathbb Q}h(x,x)$, a positive even integer. A shortest vector has trace two, hence $h(x,x)=1$ since $1+b\sqrt3$ is totally positive for integral $b$ only when $b=0$. Split off that unit vector. The complement is a self-dual Hermitian line in a rational unit line. Its fractional ideal $I$ has $I\bar I=O$, so $I=A/\bar A$ for an ideal $A$. Minkowski's ideal-class bound is $(4!/4^4)(4/\pi)^2\sqrt{144}<2$, so $A$ is principal. This gives a norm-one generator for the complement. The binary mass is therefore $1/(12^2\,2!)=1/288$, and $(1/10368)/(1/288)=1/36$.

## Unresolved

The explicit second class carries most of the rank-four mass. The release defines its mass using representatives of **every** class in the genus and weights each by its own automorphism count. The class-number comparison uses that same sum after inserting the finite level index. These facts account for the missing $3/40$ in the single-class calculation. The remaining comparison for an indefinite row is between its adelic quotient volume, with the specified Haar normalization, and the positive definite standard mass of the same rank. [Requirement on representatives](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/ThetaLiftIndependence/Statement.lean#L139-L146) · [Definition of mass](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/HermitianLattices/StatementMass.lean#L11-L23) · [Use of the sum in the framed count](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MassSelfDualLatticeFirstSpaceEq.lean#L102-L135) · [Volume in an indefinite signature](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/GL5/DiscreteSeriesOfFormalDegree.lean#L55-L84)
