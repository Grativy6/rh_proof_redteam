# A theta integral that cancels exactly

**Result.** Two degree-two oscillator vectors have the same weight under the compact circle. For one the local matrix-coefficient integral is zero. For the other, after normalizing its norm to one, the integral is $1/(b+1)$, where $b\ge2$ is the number of oscillator pairs. The cancellation persists for arbitrarily large $b$. The published argument requires a jointly harmonic test vector. In this rank-one setting that requirement excludes exactly the directions lost by this integral.

This is a local test of the nonvanishing step identified in the [period-on-quotient audit](2026-11-23-period-on-quotient.md#unresolved). We vary the polynomial input to the local integral. The two polynomials below are not presented as global automorphic forms with identical Hecke eigenvalues. The last section checks how the global proof tests the difference of two such forms. Christopher D. Pang set the audit question. Hearthline carried out the calculation and self-review against release `40e56bab026552e089d7afcfeff08d2defb9c005`.

## Two polynomials the compact weight cannot distinguish

Use the polynomial oscillator for $SU(1,1)$ with compact partner $U(b)$. Give the monomials in $x_1,\ldots,x_b,y_1,\ldots,y_b$ the usual orthogonal Fock inner product, with squared norm the product of their exponent factorials. Define the raising operator $Q$, its adjoint $L$, and the weight operator $H$ by

$$
Q=\text{multiplication by }\sum_{j=1}^b x_jy_j,\qquad
L=\sum_{j=1}^b\partial_{x_j}\partial_{y_j},\qquad
H=b+\text{total degree}.
$$

In the release these operators arise in the specialization $p=q=1,\ r=b,\ s=0$ by substituting the two off-diagonal matrix units in the first group action. One gives $Q$ and the other gives $-L$. The compact partner has no noncompact lowering operator. Joint harmonicity here means precisely $LP=0$. [Polynomial action](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/DataTheta.lean#L182-L213) · [Degree-lowering component](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/DataTheta.lean#L300-L309) · [Joint harmonic space](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Foundations/IsFockIPOfFockData.lean#L8-L19)

Take $P_{\rm tr}=Q1$ and $P_{\rm h}=x_1y_b$. They have identical bidegree $(1,1)$ and circle weight $b+2$. But $LP_{\rm tr}=b$ whereas $LP_{\rm h}=0$. Write $C=\cosh t$, $u=\tanh t$ and $X=u^2$ for the usual radial coordinate $t\ge0$. The oscillator acts in the radial direction by

$$
S(t)=\exp(uQ)\,C^{-H}\,\exp(-uL).
$$

This factorization follows by differentiating the right side, using $[L,Q]=H$, $[H,Q]=2Q$, $[H,L]=-2L$. It starts at the identity and has generator $Q-L$. Equivalently the same radial coefficient follows in the holomorphic disk model as shown below. On a polynomial only finitely many terms of the lowering exponential contribute, and only finitely many raising terms return to the tested degree.

For $P_{\rm tr}$ the lowering exponential yields $P_{\rm tr}-bu$. Following it through the other two factors, its normalized diagonal coefficient is $C^{-b}[1-(b+1)X]$. For $P_{\rm h}$ it is $C^{-(b+2)}$. Pair either coefficient with the conjugate lowest-vector coefficient of weight $b+2$, also $C^{-(b+2)}$ on the radial subgroup. The compact phases cancel. Normalize Haar measure so that the radial factor is $\sinh(2t)\,dt=dX/(1-X)^2$ after the compact integrations. The invariant area of the disk is proportional to ordinary area divided by $(1-|z|^2)^2$, and $X=|z|^2$ in radial coordinates. The lowest coefficient follows by taking the constant term of the disk action on the constant function. A different positive Haar normalization multiplies both answers by the same constant. The two integrals become

$$
\begin{aligned}
I_{\rm tr}
&=\int_0^1 (1-X)^{b-1}\,[1-(b+1)X]\,dX
=\big[X(1-X)^b\big]_0^1=0,\\
I_{\rm h}
&=\int_0^1 (1-X)^b\,dX=\frac1{b+1}.
\end{aligned}
$$

Both integrands are positive near the identity. The first changes sign at $X=1/(b+1)$. A point evaluation, a matching weight, or regularity of the vector alone would miss this zero.

## The entire kernel in every degree

For a homogeneous polynomial $P$ of degree $d$, use the lowest-vector test of weight $b+d$ as above. With the same Haar normalization and the oscillator coefficient left unnormalized, the integral is

$$
I(P)=\frac{\|\operatorname{proj}_{\ker L}P\|^2}{b+d-1}.
$$

Here is a direct verification. Since $Q^*=L$, degree $d$ splits into its harmonic part and $Q$ times degree $d-2$. Iterating gives the orthogonal summands $Q^j h$, with $Lh=0$ and $h$ of degree $d-2j$. Orthogonality follows by moving the higher power of $Q$ to the other side of the inner product and applying the corresponding power of $L$. Set $\ell=b+d-2j$. The commutator gives $LQ^j h=j(\ell+j-1)Q^{j-1}h$. This also gives $\|Q^m h\|^2=m!\,\ell(\ell+1)\cdots(\ell+m-1)\|h\|^2$. Consequently the raising exponential converges in the Fock norm for $|u|<1$, by the ratio test, including after any fixed number of raising operations. Reading off the term that returns to degree $d$ in $S(t)Q^j h$ gives the normalized coefficient

$$
C^{-\ell}\sum_{m=0}^j(-1)^m{j\choose m}{\ell+j-1\choose m}X^m(1-X)^{j-m}.
$$

The returned vector is proportional to $Q^j h$, so different summands give no cross terms. Pair with $C^{-(\ell+2j)}$ and integrate in $X$. For $j=0$ this gives $1/(\ell-1)$. For $j>0$, the beta integral of each monomial gives the sum

$$
\frac{(\ell+j-1)!}{(\ell+2j-1)!}
\sum_{m=0}^{j}(-1)^m{j\choose m}
\frac{(\ell+2j-m-2)!}{(\ell+j-1-m)!}.
$$

The factorial ratio is a polynomial in $m$ of degree $j-1$, including the empty product when $j=1$. Its $j$th finite difference vanishes. This proves the formula, including the case where the harmonic projection of $P$ is zero.

An independent calculation uses the disk realization on the basis vector $z^j$. The coefficient of $z^j$ in $C^{-\ell}(z+u)^j/(1+uz)^{\ell+j}$ gives the same polynomial in $X$. The optional command `python receipt-archives/check_oscillator_integral.py` compares both expansions and integrates them with exact fractions for $2\le b\le12$, $0\le d\le12$ and every possible $j$. The finite-difference argument proves the all-degree assertion. [Exact-arithmetic check](check_oscillator_integral.py)

## Can higher rank bring the cancellation back?

There is a paper check for the radial coefficient in the standard polynomial oscillator at every signature. For $U(p,q)$ with partner $U(r,s)$, diagonalize the off-diagonal $p\times q$ Cartan block by singular value decomposition. Write $t_i$ for its singular values, with $1\le i\le\min(p,q)$. For each matched pair of source rows, substituting $E_{i,p+i}+E_{p+i,i}$ in the published action gives $Q_i-L_i$ on $r+s$ pairs of polynomial variables. Distinct $i$ use disjoint variables. A joint harmonic $P$ is killed by every $L_i$, since each is a sum of the contractions that occur separately in the two off-diagonal matrix units. A compact change of source coordinates preserves these joint contraction kernels. [Action and signs](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/DataTheta.lean#L184-L213) · [Source’s Cartan-direction statement](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InnerExpJointHarmPos.lean#L200-L215)

Checking only one real direction would be insufficient. For $p=q=r=s=1$, name the two variable pairs $x,y$ and $z,w$, indexed by the positive and negative partner coordinate respectively. The polynomial $xy-zw$ has zero contraction for $E_{12}+E_{21}$, since the two contractions cancel. For $i(E_{12}-E_{21})$ the lowering term is $i(\partial_x\partial_y-\partial_z\partial_w)$, which returns $2i$. The definition tests both directions.

Apply the radial factorization above independently to each $i$. Lowering exponentials fix $P$. In its diagonal matrix coefficient, every nonconstant raising term pairs to zero because its adjoint contains an $L_i$ acting on $P$. Write $P_\nu$ for the component of $P$ with degree $\nu_i$ in the variables of each matched pair of rows. The coefficient is exactly

$$
\sum_\nu \|P_\nu\|^2\prod_i(\cosh t_i)^{-(r+s+\nu_i)}.
$$

This is strictly positive for every nonzero $P$. It proves positivity along these radial directions. A global group integral also includes compact rotations and a coefficient of the discrete series.

To test those rotations, let $A_g,B_g$ be the two representations compressed to a common irreducible compact type of dimension $h$, using the same compact action. For a vector $v$ of that type, average the product $\langle v,A_gv\rangle\overline{\langle v,B_gv\rangle}$ over independent left and right compact rotations of $g$. Each rotation averages $vv^*$ to $(\|v\|^2/h)I$. The resulting integrand is $\|v\|^4\operatorname{tr}(B_g^*A_g)/h^2$. The compact actions cancel from this trace. Where both radial compressions are positive semidefinite, its radial value is nonnegative because $\operatorname{tr}(BA)=\operatorname{tr}(B^{1/2}AB^{1/2})\ge0$. It is positive at the identity for nonzero embeddings and hence on a neighborhood. With the required integrability, this gives a positive integral. Positivity on the discrete-series type and integrability are separate inputs to this argument. Binyong Sun gives the corresponding operator positivity result for lowest compact types of cohomological representations. The numerical decay needed in the release is a further assertion. [Trace argument in the release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EqZeroOfPositiveCoeffOrthogonalEmbeddings.lean#L70-L112) · [Lowest-type positivity and quantitative decay as stated](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/Divisibility/SchurIrreducible.lean#L85-L94) · [Sun, *Matrix coefficients of cohomologically induced representations*](https://doi.org/10.1112/S0010437X06002508)

Taking the trace matters. With $A=\left(\begin{smallmatrix}1&0\\0&0\end{smallmatrix}\right)$, $B=\left(\begin{smallmatrix}1&2\\2&4\end{smallmatrix}\right)$ and $v=(1,-1)$, both matrices are positive semidefinite but $v^*ABv=-1$. The trace is $1$. The proof sums the matched compact directions. A sign argument about a single entry of their product would fail this example.

## What happens to the difference of two Hecke eigenvectors?

At a real place the release selects a polynomial satisfying **both** harmonic conditions before applying the nonvanishing law. The translation to polynomials preserves degree and identifies the derivatives in the noncompact directions with the polynomial action. In particular a nonzero lowering term cannot be relabeled as a pure degree-$d+2$ derivative. On the representation side the local integral is the squared norm of a projection divided by the positive formal degree. A separate argument establishes strict positivity of that projection on the selected joint highest vector. In general the release asks only for positivity here. Its stronger assertion that the projection fixes the entire vector has a compact-partner hypothesis. [Selection and use](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainRealZetaNonvanishing.lean#L48-L58) · [Degree test](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FockJointHarmonicVectorsIffPolynomials.lean#L139-L156) · [Projection formula and its stronger case](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/Divisibility/SchurIrreducible.lean#L265-L281) · [Strict-positivity argument](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoublingIntegralJointHarmonicPos.lean#L385-L432)

At the full Hecke eigenspace the quantifiers matter. Let $f_1,f_2$ have the same parameters outside the exceptional set and suppose $f=f_1-f_2\ne0$. The source checks that a nonzero linear combination retains the parameters, including the cases where an individual evaluation vanishes. It chooses one local test for the step *before* quantifying over nonzero vectors $f$. The local integral at that test factors as a common nonzero scalar times the conjugate of the Hermitian squared norm of $f$. Positivity of the metric then detects $f_1-f_2$. The adjoint is taken for the fixed theta map, whose defining integral identity holds for every polynomial test. This blocks the example in which a map is nonzero on each of two basis vectors and zero on their difference, conditional on the spectral and analytic inputs of the factorization. [Linear combinations](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainHeckeParamAddSmulOfAgreeOffSet.lean#L117-L151) · [Quantifier order](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/LatticeFrames/ChainParSucc.lean#L194-L208) · [Norm factor and nonzero integral](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainLocalZetaNonvanishingOfReal.lean#L63-L99) · [One map for all tests](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/IndefiniteReal/OrthogonalComplementCharacterisation.lean#L44-L55) · [Passage to the adjoint](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaLiftChainAdjointNonvanishingStep.lean#L23-L41)

There is also a numerical distinction between survival and size. Even on normalized harmonic vectors the answer $1/(b+d-1)$ tends to zero as the weight increases. The later quantitative scalar estimate explicitly includes the archimedean matrix-coefficient integrals and requires a separate formal-degree bound. This rank-one calculation does not give the quantitative estimate for the high-rank representation. [Scalar bound actually used](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelCOfInnerProductFormula.lean#L52-L68) · [Formal-degree comparison](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FormalDegreeRealPlaceUpperBoundOfHarishChandra.lean#L31-L49)

## Unresolved

The explicit zero refutes weight matching as a sufficient condition in this model. It does not refute the nonvanishing step of the released proof. A higher-rank falsification would need a selected joint harmonic whose relevant projected norm is zero, a failure of the identification with the constructed lift, or a loss in the quantitative estimate. A separate possible failure is at continuation of the global integral. There the actual statement requires holomorphic values of the partial $L$-factor and continued doubling integral, and a nonzero normalizer. An uncanceled pole would have to occur in those precise inputs. [Continuation product](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HolomorphicContinuationValueEqDivMul.lean#L14-L17)
