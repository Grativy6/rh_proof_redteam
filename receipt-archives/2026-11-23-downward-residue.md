# Which theta lift has to survive?

**23 November 2026.** Prepared by Hearthline for Christopher D. Pang’s PAL audit of the 20 November Alpöge–Claude release. The [oscillator receipt](2026-11-23-oscillator-cancellation.md) checked an integral on the upward side. The argument about the full Hecke eigenspace has a second obligation on the downward side. We traced that obligation to a residue and tried to make the residue concentrate on a set the argument discards. The rank and change-of-variables tests below preserve the published inference under the hypotheses checked here.

## Two vectors with the same label

Give all spaces the same scalar Hecke action. Take $T:\mathbb C^2\to\mathbb C$, $T(u,v)=u+v$, with the usual inner products. Both basis vectors map to $1$. The positive operator $TT^*=2I$ controls every vector in the target. Yet $T(1,-1)=0$. Even an exact positive formula on the entire target leaves room for this cancellation in the source.

The release's `AForm` controls $TT^*$ and `UpInjW` concerns the adjoint on a specified target subspace. Its separate `LiftInj` says that if one source vector with Hecke label $s$ has nonzero image, every **good** vector of label $s$ in the kernel is zero. The constructor for surjectivity calls both proofs. Substituting $(1,-1)$ catches a false inference one could make while reading the argument. The source supplies an additional argument precisely there. [Adjoint formula](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/RealLowestKTypeCoeffSquareIntegrable.lean#L42-L44) · [Two injectivity statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/RealLowestKTypeCoeffSquareIntegrable.lean#L65-L77) · [Consumer of both proofs](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/PartialLFunctionOfPublished.lean#L18-L31)

The surviving vector identifies a string of local eigenvalues belonging to the label. For *each* nonzero vector with that label, `NonVan` must produce a nonzero integral with some theta test function. To reach the **fixed** map, the proof also has to show that its vanishing kills every such test on the good subspace. The real-place argument uses continuity in a Sobolev norm. The finite-place argument uses translates, subgroup averages and differences imposed by a level character. These are substantive inputs when two source vectors have the same label. [Transfer of the label](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HasStringOfLift.lean#L23-L49) · [Nonvanishing with a variable test](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ParamsEx.lean#L39-L54) · [Generation and the fixed map](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ParamsEx.lean#L74-L92) · [Real-place argument](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ThetaLiftGenerationAtRealPlaces.lean#L22-L33) · [Finite-place argument](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ThetaLiftGenerationFinitePlaces.lean#L87-L114)

## Where a nonzero residue is required

Write $r$ for the smaller rank. The doubled construction uses $t\ge r+5$, $n=r+t$, and an enlarged Hermitian space of rank $r+2t$. If every downward test vanishes on the vector under consideration, the regularized theta identity gives zero for the coefficient of $(s-t/2)^{-1}$ in a **paired** Eisenstein integral. The Euler-product expression for this same integral gives a nonzero coefficient. [Ranks and spaces](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/RepresentationTheoryGL/RegularisedSiegelWeil/ResidueVanishing/Rethread.lean#L19-L39) · [The pairing and its Euler product](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/RepresentationTheoryGL/RegularisedSiegelWeil/ResidueVanishing/Rethread.lean#L59-L82) · [The two coefficients at the same point](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/RepresentationTheoryGL/RegularisedSiegelWeil/ResidueVanishing/Rethread.lean#L89-L100)

Here is the pole calculation. Include the character twist in the residual factor $L_0^S$. Before shifting the variable by $1/2$, the product is

$$
 L_0^S(s)\prod_{j=0}^{t-1}
 \zeta_E^S\!\left(s+\frac{t-1}{2}-j\right).
$$

At $s_*=(t+1)/2$, the zeta arguments are $t,t-1,\ldots,1$. Every residual Satake eigenvalue at a retained prime of norm $q$ has modulus at most $q^{(r-1)/2}$. Its ratio after division by $q^{s_*}$ is at most $q^{-(t-r+2)/2}\le q^{-7/2}$. There are $r$ such factors per prime. Absolute convergence in a neighborhood of $s_*$ gives a nonzero analytic $L_0^S(s_*)$. Removing finitely many Euler factors preserves the nonzero residue of the Dedekind zeta function at $1$. The residue is therefore

$$
 L_0^S(s_*)\,\operatorname{Res}_{u=1}\zeta_E^S(u)
       \prod_{k=2}^{t}\zeta_E^S(k)\ne0.
$$

The zeta integral uses the additional shift, a nonzero level-place factor and a normalizing denominator regular and nonzero at $t/2$. The shift places the simple pole at exactly $t/2$. This calculation tests the unramified factors. It still requires the asserted nonzero level-place factor for the test used in that integral. [Product, parameter bounds and pole](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/SimplePoleTwistedLift.lean#L29-L52) · [Level-place factor and normalizing denominator](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/RepresentationTheoryGL/RegularisedSiegelWeil/ResidueVanishing/Rethread.lean#L71-L100)

## A set of measure zero can carry the entire residue

Give $\mathbb Z_p$ volume one. For a locally constant function $\phi$ on $\mathbb Z_p$, the residue at $s=0$ of

$$
 \int_{\mathbb Z_p}|u|_p^{s-1}\phi(u)\,du
 \quad\text{is}\quad \frac{1-p^{-1}}{\log p}\,\phi(0).
$$

Take $\phi\equiv1$. Summing shells of valuation $k\ge0$ gives $(1-p^{-1})/(1-p^{-s})$. For general $\phi$, choose a small ball on which it equals $\phi(0)$. The finitely many remaining shells give an entire function. Thus a single point of zero Haar measure carries the whole residue. An appeal to ordinary matrix volume would leave a genuine hole here.

The release applies its rank test to the **residue measure itself**. On a finite set of active places it produces a positive measure finite on compact sets. If $X$ denotes the first $r$ columns and $Z$ the next $t$, it requires invariance under $Z\mapsto Z+XY$ and the pushforward law

$$
 (Z\mapsto Zg)_*\nu=|\det g|^{-(r+t)}\nu .
$$

The exponent has an independent check. Before imposing the Hermitian Gram condition, $Z$ has $r+2t$ rows, giving one inverse determinant per row. The change of variable in the Fourier integration over $t$ by $t$ Hermitian matrices returns $t$ of those powers. At a nonsplit place, conjugation by a diagonal $g$ multiplies each diagonal coordinate by a field norm and each off-diagonal pair contributes the modulus of one extension-field coordinate. Each diagonal multiplier of $g$ appears $t$ times. At a split place the Fourier variable is an ordinary square matrix, and left and right multiplication give the same formula. Using the local field Haar moduli, the exponent remaining is $-(r+2t)+t=-(r+t)$. The source applies these changes of variables to the iterated integral and derives the measure law from test functions. [Measure, support and covariance](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/RepresentationTheoryGL/RegularisedSiegelWeil/SingularNullSets/WeakApproximationFinitePlace.lean#L65-L79) · [Two Jacobians](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/RepresentationTheoryGL/RegularisedSiegelWeil/HermitianCellMeasures/EmDefs.lean#L66-L86) · [Change of variables for the actual functional](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/OrbEx.lean#L135-L168) · [Measure supplied to the residue identity](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EisMeas.lean#L175-L186)

## Can the singular stratum satisfy that law?

Fix one active local field. The first Gram block is invertible, so $X$ has a left inverse $P$. Put $U=PZ$ and $V=Z-XU$. Suppose $V$ has rank $j<t$. On a chart, permute the columns and write $V=(V_0,V_0 H)$, where $V_0$ has $j$ independent columns. Write $U=(U_0,U_1)$ and $S=U_1-U_0H$. The coordinates free to translate at fixed $X,V_0,U_0$ are $(H,S)$, a matrix with $r+j$ rows and $t-j$ columns.

Right multiplication by the block unipotent with top-right block $Y$ sends $H$ to $H+Y$ and fixes $S$. The shear adding $X(0,Y')$ to $Z$ sends $S$ to $S+Y'$ and fixes $H$. Hence, after restricting the base coordinates to any compact subset of this chart, the measure on $(H,S)$ is translation invariant and finite on compact sets. This reasoning uses restrictions and pushforwards of the measure, and needs no conditional measure on an individual fibre.

Now multiply the final $t-j$ columns by $D\in\mathrm{GL}_{t-j}$. This fixes the base and takes $(H,S)$ to $(HD,SD)$. Translation-invariant measure on these coordinates has pushforward factor $|\det D|^{-(r+j)}$. The residue law requires $|\det D|^{-(r+t)}$. Choosing $|\det D|\ne1$ forces the measure on the chart to vanish. Concretely, over a finite place of residue size $q$, divide the unit box into translates of the box scaled by a uniformizer. Its mass $M$ satisfies $M=q^{-(t-j)^2}M$. Finiteness on compact sets gives $M=0$.

Countably many compact base sets exhaust each minor chart. The transformations can act in a single active field factor and fix the others. A finite set of active places therefore gives zero mass to every deficient frame. The rank test would fail for the point residue above, whose Dirac mass is invariant under every dilation. [Local field decomposition, left inverse and scaling](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NullSingOfIdemEx.lean#L321-L358) · [The measure tested for singular mass](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/RepresentationTheoryGL/RegularisedSiegelWeil/SingularNullSets/WeakApproximationFinitePlace.lean#L225-L234) · [Where the result enters the paired residue](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/RepresentationTheoryGL/RegularisedSiegelWeil/ThetaIdempotents/ThetaCoefficients/ResCore.lean#L48-L64)

## A direct split-prime count

The [split Gram calculation](2026-11-23-split-gram-density.md) checks the same local dimension by a second method. The normalized density exists with the release’s $2t$ complementary rows. Deleting **one** row makes it diverge, although the matrices of deficient rank still have ordinary measure zero. That example distinguishes two hypotheses that a dimension count alone could conceal.

## Unresolved

The residue and rank calculations give no counterexample to this published implication. The proof still needs the nonzero level-place factor for the test that realizes the Euler product, and a proof that every relevant downward test can be generated from the fixed map on a good Hecke eigenspace. A witness must survive the good-type conditions and change the answer for the same vector. [PAL work key](../RH-PROOF-WORK-KEY.md) · [Assembly of the downward proof](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/LiftInjNonVanTypeNZOfPrints.lean#L20-L39)
