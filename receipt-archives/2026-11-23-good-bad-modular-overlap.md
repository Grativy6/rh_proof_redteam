# The shape of the good/bad overlap at a host prime

**23 November 2026 · Hearthline, under Christopher D. Pang’s continuing audit.** At either host prime $p=q$ or $p=d$, a subspace of the actual row forms admits a calculation of the entire first reduction of its good and bad lattices. Although its bad fraction tends to zero, the proportion of *its bad directions* also appearing in its good reduction tends to one. Two examples over $\mathbb Q(\zeta_7)$ show that the number of bad labels and the total index together do not determine the depths of those congruences. This refines the [spectral denominator calculation](2026-11-23-good-type-spectral-denominator.md), using its hypotheses and occupied globally good tuple. The conclusion here is about a saturated subspace of the actual type lattice. Its proportion within the whole row space has not been determined.

## A cyclic product inside the type lattice

Fix $\lambda\mid p$ in the outer number field and work over its local ring $O$. Write the normalized valuation as $v(p)=1$ and let $e_\lambda$ be the absolute ramification index. At each of the qualifying places in the preceding calculation, fix a Sylow $p$-slice of the even determinant twists having $1\le b_i\le H_{g_k}$ forbidden shifts. The other host prime supplies such a slice. Write $n_i=p^{a_i}$ for the order of the local Sylow group, so $a_i=v_p(g_k-1)\ge1$. Choose a good starting point in each slice. All other labels stay fixed. On the resulting group of shifts $\Theta=\prod_i C_{n_i}$ the good indicator is exactly the product of the one-coordinate good indicators. Both the number of selected places and $H_{g_k}$ grow at most polynomially in the window scale, while $p$ eventually exceeds every such polynomial. [Source and proof of the mixed slices](2026-11-23-good-type-spectral-denominator.md)

The component samples span a full integral lattice in their own subspace. Choose a vector $v$ in the starting joint label and type space which is an eigenvector for the central $p$-subgroup of the type group. This subgroup commutes with the prescribed unipotent character and all label projectors. Its eigenvalues are roots of unity in the coefficient field. Take $v$ primitive at $\lambda$ in the ambient type lattice. The central scalars move the determinant coordinates $z\in\widehat\Theta$ transitively because the $r$-th power map on $p$-power roots is bijective for $p>r$ and a scalar matrix $cI_r$ has determinant $c^r$. Its action on $v$ is by a unit. Thus the component pieces $v_z=D_zv$ are all primitive, since the level moves preserve the lattice and at least one piece is primitive. The $D_z$ have disjoint supports and preserve the lattice. It follows that in $U=\sum_z L v_z$, the intersection with the ambient type lattice is **exactly** $M=\bigoplus_z O v_z$. Applying $D_z$ tests the coefficient of each $v_z$. The character twist vectors are the Fourier basis $\sum_z\theta(z)v_z$. These statements are unchanged by inverting the character convention. [Transport of the group action](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/IndefiniteReal/ThPinsR.lean#L127-L134) · [Type condition and lattice](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/IndefiniteReal/GramCEqTranspose.lean#L74-L97) · [Integral component decomposition](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspFormsSupLatticeSplitOverComponents.lean#L36-L59) · [Roots of unity in the arithmetic field](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Foundations/RootOfUnityEightQMemCoeffGaloisSubfield.lean#L279-L286)

In particular $U$ is stable under the released good projector. A good/bad decomposition of an element of $M$ in the full row lattice must agree with its two characteristic-zero projections, which lie in $U$. Thus the congruence module computed in $M$ injects into the congruence module of the full integral lattice.

## One finite cyclic coordinate

In each selected coordinate $1\le b\le n/2$ and $b<p$ on sufficiently large windows. For a factor of order $n=p^a$ let $\zeta$ be a primitive $n$-th root. In the sample basis use the group ring $M_1=O[T]/(T^n-1)$. Its field-valued spectral coordinates are evaluation at the $n$-th roots, up to inversion of the labeling. For the bad index set $B$ of size $b$ and its complement $G$, put
$$
 f_B(T)=\prod_{j\in B}(T-\zeta^j),\qquad
 f_G(T)=\prod_{j\in G}(T-\zeta^j).
$$
The saturated good sublattice is $(f_B)M_1$ and the saturated bad sublattice is $(f_G)M_1$. This follows by monic division over $O$. In the residue field $k$ write $u=T-1$. Then $M_1\otimes k=k[u]/(u^n)$ and the respective images are $(u^b)$ and $(u^{n-b})$. For $2b\le n$, **every bad direction in this coordinate is also a good direction after reduction**.

The finite quotient by the sum of these two lattices is $O[T]/(f_B,f_G)$. Present it by multiplication by $f_G$ on the free module $O[T]/(f_B)$ of rank $b$. Its normalized length, meaning ordinary module length divided by $e_\lambda$, is exactly
$$
 \sum_{i\in B,\,j\in G} v(\zeta^i-\zeta^j)
 =ba-\sum_{\substack{i,j\in B\\i\ne j}}v(\zeta^i-\zeta^j).
$$
The first identity is the determinant of the multiplication operator. The second follows from $(T^n-1)'(\zeta^i)=n(\zeta^i)^{-1}$. Each internal difference in the last sum has valuation $1/\varphi(p^c)\le1/(p-1)$ for some $c\ge1$. Thus $b(a-(b-1)/(p-1))$ and $ba$ are lower and upper bounds for the normalized length.

There is also a bound on **each** of the $b$ nonunit elementary divisors. If its exponent in uniformizer units is $h$, then
$$
       a-\frac{2(b-1)}{p-1}\ \le\ h/e_\lambda\ \le\ a .
$$
For the lower bound, evaluate the remainder of $f_G$ modulo $f_B$ by Lagrange interpolation at the bad roots. At $\zeta^i$, its value is $n(\zeta^i)^{-1}/f'_B(\zeta^i)$. The interpolation denominator contributes another $f'_B(\zeta^i)$, and all numerator-polynomial coefficients are integral. Each entry of the multiplication matrix therefore has valuation at least $a-2(b-1)/(p-1)$, also after monic reduction. For the upper bound, multiplying the Fourier projector by $n$ makes it integral. The largest elementary divisor has normalized exponent exactly $a$ when $0<b<p$, since the diagonal entry of the good projector is $(n-b)/n$ with unit numerator. Outside this single-coordinate argument the diagonal of the larger group can hide the prime, as the [order-506 example](2026-11-23-good-type-spectral-denominator.md) illustrates.

## All the selected places together

Put $G_i=n_i-b_i$ and $N=\prod_i n_i$. The saturated good lattice in the block is the tensor product of the individual saturated good lattices. Each is a direct summand as an $O$-module and the tensor product has exactly the required field span. Reducing modulo $\lambda$ gives the ideal $(\prod_i u_i^{b_i})$ inside $k[u_i]/(u_i^{n_i})$. The bad reduction contains $\sum_i(u_i^{G_i})$, obtained by choosing the bad submodule in just that coordinate. Its dimension is $N-\prod_iG_i$, the full characteristic-zero bad rank, so this describes the bad reduction exactly. Consequently
$$
 \dim_k(M_{\rm good}\bmod\lambda\ \cap\ M_{\rm bad}\bmod\lambda)
   = \prod_i(n_i-b_i)-\prod_i(n_i-2b_i).
$$
Both images in this formula are taken inside the same reduced ambient lattice $M/\lambda M$. Both images inject into the reduction of the full row lattice because $M$ is saturated there.

Write $S=\sum_i b_i/n_i$. It tends to zero on the selected blocks since $n_i\ge p$ and $\sum_i b_i$ is polynomially bounded. For large windows, elementary inclusion-exclusion bounds the bad fraction between $S-S^2/2$ and $S$, and the intersection fraction is at least $S-2S^2$, all measured relative to $N$. The fraction of the bad reduction lying in the good reduction is consequently at least $1-2S$ and tends to one.

For more than the first reduction, let $T_M=M/(M_{\rm good}+M_{\rm bad})$. Its $\pi^j$-torsion identifies with the intersection of the two images modulo $\pi^jM$. Given a torsion class represented by $x$, write $\pi^j x=y_++y_-$ and take $y_+\bmod\pi^jM$. Conversely any common class gives such a pair and a representative $x$. Saturation verifies injectivity. The isomorphism $T_M\simeq PM/M_{\rm good}$ expresses both lattices on the right as tensor products and lets us compute all the elementary divisors. In a single coordinate the inclusion into $P_iM_i$ has $G_i-b_i$ unit factors and $b_i$ nonunit factors described above. Taking tensor products of local Smith bases multiplies the diagonal factors. For a nonempty subset $J$ of places, this produces
$$
 \prod_{i\in J}b_i\prod_{i\notin J}(n_i-2b_i)
$$
entries whose normalized exponents lie between $\sum_{i\in J}(a_i-2(b_i-1)/(p-1))$ and $\sum_{i\in J}a_i$. These are counts of entries with the indicated provenance even when some exponent intervals overlap. The deepest collision has normalized depth exactly $\sum_i a_i$.

## Equal total lengths, different depths

| Order and bad exponents | Elementary-divisor exponents in units of $1-\zeta_n$ | Total |
| --- | --- | ---: |
| $5$, $\{0,1\}$ | $2,4$ | 6 |
| $7$, $\{0,1,2\}$ | $2,4,6$ | 12 |
| $7$, $\{0,1,3\}$ | $3,3,6$ | 12 |
| $25$, $\{0,5,10\}$ | $20,30,40$ | 90 |

The trace Gram matrix also gives a second calculation of the exponents. In $R=O[T]/(f_B)$ write $\theta$ for the class of $T$. The trace dual is $R^\vee=f'_B(\theta)^{-1}R$. Indeed, for a polynomial $Q$ of degree less than $b$, the trace of $Q(\theta)/f'_B(\theta)$ is the coefficient of $T^{b-1}$ in $Q$, by Lagrange interpolation. The pairing which takes the coefficient of $T^{b-1}$ in a product modulo $f_B$ is unimodular on the power basis, as seen by reversing its columns. Since $\theta$ is a unit and $f_G(\theta)f'_B(\theta)=n\theta^{-1}$, the congruence quotient is $R/nR^\vee$. If the local trace Gram exponents are $s_j$, its exponents are $a e_\lambda-s_j$ in reverse order.

At order 7 even the pairwise valuations between distinct bad roots agree in the two examples. One can see what changes by writing $H=(\sum_{j\in B}\zeta_7^{(a+b)j})_{0\le a,b<3}$ for the trace Gram matrix of $O[T]/(f_B)$. Its determinant has valuation 6, by the squared Vandermonde formula. The leading coefficient of its first nontrivial two-by-two minor is proportional to $\sum_{i<j}(i-j)^2$, which is $6$ for the first set and $14$ for the second. The latter disappears in characteristic 7. The table is checked directly on the multiplication matrix by the valuations of **all** minors. Two copies of the order-5 example have common reduction of dimension 8 and total uniformizer length 36. [Exact cyclotomic calculation](check_good_bad_congruence_block.py)

## Where the proof uses the residue

The covolume inequality uses a bound on the total index. The index calculation permits precisely the modular overlap exhibited here. Another part of the release defines an analogous quotient `MtUp/MtLow` inside an integral Hecke module. Its value is measured on point eigenspaces there. The later lattice adoption identifies a range with the **already selected good space**, and the zero formula at untwisted places is an empty sum over twisted locations. An equality between its local length and the present full row congruence module would require an additional comparison. [Index map in the good/bad cut](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean#L250-L288) · [Rank-weighted use](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MajAtAddRight.lean#L126-L142) · [Local Hecke lattices and their measured quotient](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean#L197-L225) · [Range at lattice adoption](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LatticeFamilyAdoptionSecondAltAlt.lean#L130-L151) · [Zero formula at untwisted places](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaJEqZeroOfUntwisted.lean#L9-L14)

## Unresolved

This determines the modular shape of a saturated block at each host prime under the same large-window rank inputs as the preceding receipt. The contribution of other blocks, and the constraints imposed when a good-row form is sent through the subsequent theta and Hecke maps, have not been computed. In particular the near-total overlap in this block gives no direct bound on the fraction of the *whole* bad space that overlaps at $p$.

Hearthline derived and self-reviewed the cyclic and tensor calculations. The [standalone verifier](check_good_bad_congruence_block.py) computes over integer cyclotomic power bases and uses no numerical approximation.
