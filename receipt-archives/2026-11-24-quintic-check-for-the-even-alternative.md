# The totally real quintic alternative can be exhausted on paper and in integers

**24 November 2026.** In identifying the global residue of the four level-571 lifts there is an even projective possibility which Serre’s odd modularity theorem does not address. It would give a totally real quintic field with Galois closure group $S_5$. We enumerate all possible defining polynomials within proved bounds. Exactly **69** survive the local, real-root and discriminant tests. Each has a simple integral root of a degree-six resolvent, so **none** can have group $S_5$. This is a finite exclusion of a competing residual representation, independent of the RH proof. The [preceding Galois argument](2026-11-24-global-residual-character-at-571.md) explains why these fields exhaust the relevant even alternative.

Run `python -B receipt-archives/hecke-571/hunt_quintics.py` from the repository root. It uses only the Python standard library. Giving an existing directory as a final argument also writes the complete lists of coefficient tuples. [Exhaustive search](hecke-571/hunt_quintics.py) · [Rational interval and resolvent certificate](hecke-571/pentagons.py)

## The field discriminants are forced

Write $q=571$. In the even case the projective extension of $G_\mathbb Q$ is totally real, unramified outside $5,q$, and contains a four-cycle in tame inertia at 5. Its permutation-sign field is consequently $\mathbb Q(\sqrt5)$. It is real, unramified at 2 and ramified at 5. Neither $q$ nor $5q$ is $1\bmod4$, so a positive fundamental discriminant involving $q$ would also ramify at 2. Inertia at $q$ is a nontrivial *even* involution, hence a double transposition. It contributes two to the quintic discriminant exponent there.

If inertia at 5 is tame, its four-cycle contributes three in the degree-five permutation action. If it is wild, it contains a five-cycle and the tame quotient has order four. The group is then the affine normalizer of order 20. Its wild subgroup has order five and one last positive lower break $b$. The upper break is $b/4$. Over the unramified quadratic $K_5$ the residual arithmetic representation, after a cyclotomic twist, is a 5-torsion subquotient of a crystalline representation with weights in $[0,2]$. A quotient modulo a ramified coefficient uniformizer is still killed by 5. Abrashkin’s theorem with $N=1$, $a=2$ and $p=5$ bounds its upper break by $1/2$. Unramified base change leaves positive upper groups unchanged, as does the tame scalar twist. Hence $b\le2$. In the permutation representation the wild subgroup is transitive, so its contribution in the conductor formula is $b(5/20)(5-1)=b$. The full exponent $4+b$ is odd since the sign field ramifies at 5. This forces $b=1$. [Abrashkin, *Ramification estimate for Fontaine–Laffaille Galois modules*, main theorem](https://arxiv.org/pdf/1405.3861#page=7)

Thus the only absolute discriminants are
$$5^3q^2=40\,755\,125,\qquad 5^5q^2=1\,018\,878\,125.$$
There are also three small Frobenius tests. At split 2 and ramified-in-$K$ 7 the measured adjoint has order four. In the even projective extension over $\mathbb Q$, 7 is unramified and its residue degree in $K$ is one. At inert 3 the reading over $K$ gives eigenvalues $1,-1,-1$. In $\mathrm{PGL}_2(\mathbb F_5)\simeq S_5$ this has order two, since the group has no element of order ten. Rational Frobenius at 3 therefore has order four. A permutation of order four on five letters has type $(4,1)$.

For a competing $S_4$ image the same sign-field argument disposes of the even case directly. In its $S_3$ quotient by the normal Klein four, inertia at $q$ disappears. At 5 a four-cycle maps to a transposition and no wild 5-group can occur. The resulting cyclic cubic extension of $\mathbb Q(\sqrt5)$ is everywhere unramified. Its class number is one by the quadratic Minkowski bound, excluding this case.

## Bounds on every generator we need to consider

Project the Minkowski lattice of the ring of integers onto the hyperplane perpendicular to $(1,1,1,1,1)$. Its four-dimensional covolume is $\sqrt{D/5}$. The shortest-vector bound with $\gamma_4=\sqrt2$ gives a nonrational integer $\alpha$ whose squared projected length is at most $\sqrt2(D/5)^{1/4}$. Translate by an integer and change its sign to make the coefficient of $X^4$ in its minimal polynomial $0,1$ or $2$. The polynomial has degree five because the field degree is prime. Its five real roots $r_i$ satisfy
$$S_2=\sum r_i^2\le \sqrt2(D/5)^{1/4}+(\operatorname{Tr}\alpha)^2/5.$$
We use the generous integer ceilings 77 and 170 for the two discriminants. This gives $0<S_2=a_1^2-2a_2$ and
$$ |a_k|^2\le {5\choose k}^2(S_2/5)^k.$$
The last inequality is Cauchy–Schwarz on the elementary symmetric sum followed by Maclaurin’s inequality on the five squares. The code rounds all coefficient bounds using integer square roots. [Voight’s statement and use of the Hunter bound](https://antsmath.org/ANTSVIII/files/voight.pdf)

At $q$, all reductions of the polynomial must have the shape
$$(X^2+A X+B)^2(X+C)\pmod q.$$
The two conjugate pairs exchanged by inertia can reduce to a quadratic irreducible over the residue field, and all the displayed factors may collide. For each $a_1,a_2,A$, comparison gives $C=a_1-2A$ and $B=(a_2-A^2-2AC)/2\bmod q$. This specifies residues for the remaining three coefficients. The search takes **all** integer lifts within their bounds.

Tame inertia at 5 requires $(X-a)^4(X-b)$ modulo 5, allowing $a=b$. Wild inertia is transitive and requires $(X-a)^5$, so $5$ divides the first four nonleading coefficients. At each of $2,3,7$ a four-cycle need not yield an irreducible quartic in the reduction of this particular generator. Its four entries can form one irreducible quartic orbit, a doubled irreducible quadratic orbit or a quadrupled linear factor. The remaining fixed point gives a linear factor, including possible coincidence. This allows primes dividing the index of the power basis.

| 5-exponent | Bounded tuples after the ramified congruences and nonzero constant | Also passing all three Frobenius sieves | Positive real trace matrix and polynomial discriminant $D$ times a nonzero square |
| ---: | ---: | ---: | ---: |
| 3 | 15,178 | 488 | 11 |
| 5 | 1,282,714 | 36,004 | 58 |

Newton sums form the $5\times5$ power-trace matrix. A genuine totally real generator with five distinct roots gives a positive definite matrix, and its determinant is the polynomial discriminant. Fraction-free elimination tests positivity and the determinant exactly.

## A small resolvent excludes every survivor

Label the five distinct real roots $r_0,\ldots,r_4$. For each unoriented pentagon on the labelled roots let $P$ be its five edges in the complete graph. Its complementary five edges form the pentagram. Assign the unordered pair the value
$$u_P=\left(\sum_{\{i,j\}\in P}r_ir_j-
                \sum_{\{i,j\}\notin P}r_ir_j\right)^2.$$
There are six such pairs. The product $\prod_P(T-u_P)$ has integer coefficients since its coefficients are symmetric algebraic integers. $S_5$ acts transitively on the six pairs. A simple rational root fixes one pair under Galois. Its setwise stabilizer has order $120/6=20$. In particular a simple rational root is incompatible with $S_5$.

The checker locates all five real roots in $[-15,15]$ by sign changes or exact equality and bisects with rational arithmetic. For each candidate integer $n$ it checks that exactly one of the six rational enclosures contains $n$ and that the product of the six upper bounds for $|n-u_P|$ is less than one. The product is the absolute value of an integer, hence zero. The separate enclosures certify simplicity with no floating-point root decisions. This succeeded for all 11 and all 58 polynomials. Across the two lists the certified integer roots range from 320 through 32,000.

The [separate PARI/GP check](hecke-571/quintic_fields.gp), run on version 2.15.4, gave group order 20 for all 69 irreducible polynomials. After requiring the actual field discriminant and identifying isomorphic fields, its reduced representatives were $X^5-20X^3-5X^2+85X+78$ and $X^5-25X^3+125X-58$ respectively. The order-20 fields really can imitate the small Frobenius pattern. The rational resolvent test excludes the order-120 alternative even without these PARI identifications.

## Unresolved

This closes the even projective case under the inertia and crystalline hypotheses established in the [global comparison](2026-11-24-global-residual-character-at-571.md). It supplies no conclusion about RH or about unrelated quintic fields with different ramification.
