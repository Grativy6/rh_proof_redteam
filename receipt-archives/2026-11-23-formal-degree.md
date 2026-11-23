# Measuring a nonzero discrete-series coefficient

**23 November 2026.** The [zero-part test](2026-11-23-zero-part-eigenvalue.md) traced the height estimate to a lower bound on occupied spectral blocks. Here we test one input to that bound. The release integrates the square of a matrix coefficient for a **unit vector**. Shrinking Haar measure by a factor of $c$ would enlarge the reciprocal integral by $1/c$. The proof fixes the density in an exponential chart and relates it to compact-dual probability normalization. We checked the direction of this factor and evaluated the integral on the matrix ball for the scalar holomorphic series in every signature $p,q\ge1$. [Quantity that the proof needs](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/FormalDegreeUpperC.lean#L76-L84) · [Prescribed real-place measure](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/IndefiniteReal/SubgroupCharExtensionOneApply.lean#L119-L120) · [Compact-dual normalization](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/DataCD.lean#L42-L61) · [Conversion of measures](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StandardMeasureUnitaryPQEqVolumeSmulCompactDual.lean#L29-L51)

## The finite product in the height bound

Let $r=p+q$ and let $\lambda_1>\cdots>\lambda_r$ be the discrete-series parameters. In compact-dual normalization the asserted reciprocal integral is the product of all positive differences $\lambda_i-\lambda_j$ divided by $\prod_{i<j}(j-i)$. The real-place measure used in the estimate is larger by the factor

$$
 V_r=\prod_{j=0}^{r-1}\frac{2\pi^{j+1}}{j!}.
$$

Since $\prod_{i<j}(j-i)=\prod_{j=0}^{r-1}j!$, the reciprocal in the release's measure simplifies to

$$
 \frac{\prod_{i<j}(\lambda_i-\lambda_j)}
      {2^r\pi^{r(r+1)/2}} .
$$

In particular the subsequent logarithmic upper bound follows from the width estimate alone, once the formal-degree identity holds. With $|\lambda_i-\lambda_j|\le d+n+3$, $d\ge0$ and $n\ge3$, each numerator factor is at most $n(d+2)$. There are $r(r-1)/2$ such factors. This already gives a stronger upper bound than the one used at this point. [Formal-degree identity](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/FormalDegreeCompactDualIff.lean#L15-L22) · [Compact volume](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/VolUFactProdMulLe.lean#L14-L18) · [Width hypothesis](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FormalDegreeDivVolumeUnitaryGroupLogBound.lean#L34-L44) · [The reciprocal actually used](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FormalDegreeRealPlaceUpperBoundOfHarishChandra.lean#L34-L50)

## Direct integration for scalar holomorphic series

Use $Z\in M_{p,q}(\mathbb C)$ with $I_p-ZZ^*>0$ as coordinates on $U(p,q)/(U(p)\times U(q))$. Put $r=p+q$. The squared coefficient of the normalized lowest vector of scalar weight $k$ is $\det(I_p-ZZ^*)^k$. Indeed the reproducing kernel is $\det(I_p-ZW^*)^{-k}$, and the absolute square of the inner product between the normalized kernels at $0$ and $Z$ is its diagonal reciprocal. The invariant density is proportional to $\det(I_p-ZZ^*)^{-r}dZ$. [Neretin, matrix-ball coordinates and invariant density, §2.4](https://arxiv.org/pdf/math/0012220#page=6)

To fix the constant, the corresponding affine chart in the compact Grassmannian has density proportional to $\det(I_p+ZZ^*)^{-r}dZ$. These two chart densities have the same scale at $Z=0$ under compact-dual normalization. The vertical compact group is the same, and changing the sign of the adjoint off-diagonal tangent block preserves its volume. The compact chart has full measure. Thus the desired integral is the ratio

$$
 I_k=\frac{\int_{I_p-ZZ^*>0}\det(I_p-ZZ^*)^{k-r}\,dZ}
              {\int_{M_{p,q}(\mathbb C)}\det(I_p+ZZ^*)^{-r}\,dZ}.
$$

Both integrals can be done one row at a time. Write $A$ for the first $p-1$ rows and $z$ for the last. In the numerator put $z=w(I_q-A^*A)^{1/2}$. The Schur complement gives a last factor $1-\|w\|^2$, and the real Jacobian is $\det(I_{p-1}-AA^*)$. Integration on the complex unit ball gives $\pi^q\Gamma(s+1)/\Gamma(s+q+1)$ for exponent $s>-1$ and adds one to the exponent on $A$. For the compact denominator use $z=w(I_q+A^*A)^{1/2}$. Integration over all of $\mathbb C^q$ gives $\pi^q\Gamma(a-q)/\Gamma(a)$ at exponent $-a$ with $a>q$, leaving exponent $-(a-1)$ on $A$. Both one-row formulas follow by complex polar coordinates. Iteration gives, for integers $k\ge r$,

$$
 I_k^{-1}
 =\prod_{j=1}^p\prod_{\ell=0}^{q-1}
       \frac{k-r+j+\ell}{j+\ell}.
$$

For a scalar lowest compact weight $(k,\ldots,k,0,\ldots,0)$, the relation $\mathrm{lowK}=\lambda+\rho_n-\rho_c$ gives, up to a common shift, the Weyl parameters $(k-r,\ldots,k-r,0,\ldots,0)+\rho$ with $p$ and $q$ entries. These give precisely the displayed product. Factors within each block cancel. For $U(2,2)$ at $k=6$, $I_k=1/20$ and the integral in the release’s real-place measure is $\pi^{10}/15$. At $k=r-1$ the first row integration has a logarithmic divergence. The cross-block parameter gap is then zero, outside the strict-order hypothesis. [Parameter, lowest compact weight and product](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/FormalDegreeBessel/StatementDS.lean#L11-L23)

## Cross-check for general lowest compact types

The release characterizes the parameter by the lowest compact type, minimizing $\|\mu+2\rho_c\|$. In the compact-Cartan discrete series, Vogan's shifted parameter satisfies $\zeta=d\phi-\rho$ and its unique lowest compact type has highest weight $\mu=d\phi-2\rho_c$. Thus $\mu=\zeta+\rho_n-\rho_c$, as in the release. For $U(p,q)$ the ordered vector $\mu+2\rho_c=\zeta+\rho$ recovers the chamber of a regular parameter. Sorting it and subtracting the half-sum of positive roots recovers the parameter with its compact-block labels. [Vogan, *Branching to a maximal compact subgroup*, Proposition 5.2](https://math.mit.edu/~dav/khatHOWE2.pdf)

Olbrich gives the formal degree on a connected semisimple group as the dimension of the finite-dimensional representation of the same infinitesimal character divided by the volume of the compact dual quotient. He uses probability Haar on the maximal compact subgroup and matching tangent metrics on the two quotients. Normalizing the compact dual to total mass one multiplies the degree by that quotient volume. For $SU(p,q)$ the resulting dimension is the Weyl product above. Passing to $U(p,q)$ adds a compact central circle, acting by a scalar of unit modulus. Both the group and its compact dual are obtained from the special unitary group times this circle by the same finite central quotient. With probability measure on the circle the absolute-square integral is unchanged. Compact signatures themselves give the usual Schur orthogonality formula. [Olbrich, measure convention in §2](https://arxiv.org/pdf/math/0009039#page=8) · [Olbrich, Corollary 5.2](https://arxiv.org/pdf/math/0009039#page=15)

## A counterexample if irreducibility is lost

For the standard representation of $U(2)$, a unit vector gives integral $1/2$ with probability Haar measure. In the direct sum of two copies take $w=(e_1,e_2)/\sqrt2$. Its coefficient is $\mathrm{tr}(g)/2$ and the integral of its squared modulus is $1/4$ by character orthogonality. A repeated representation can therefore change the inferred degree even for a unit vector. The release requires strong continuity, irreducibility and square integrability for the local representation on which it invokes this formula. [Unitarity, irreducibility and integrability](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/CuspSpanNormBounds/RelevantZeroGramTerms.lean#L23-L35) · [The discrete-series hypothesis](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/CuspSpanNormBounds/RelevantZeroGramTerms.lean#L72-L76)

## Unresolved

The matrix-ball calculation verifies the Haar factor and parameter product on this scalar family. The general product is also supported by the lowest-type and formal-degree results above. To attack the claimed height bound here, one must still test how the constructed theta vector, its local model and the global pairing are identified. The source converts the integral for its model using a change of frame and obtains the parameter width from the selected weights. [Passage from the model to the integral](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvIntegralSqDiscreteSeriesCoefficientCompactDua.lean#L90-L109) · [Input from the selected weights](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LiftModelParameterDecreasingHalfIntegralWidth.lean#L118-L139) [Occupied-block return point](2026-11-23-zero-part-eigenvalue.md#unresolved)
