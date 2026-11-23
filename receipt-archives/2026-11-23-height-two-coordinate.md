# A lost factor of five in the height-two coordinate

**23 November 2026.** We tested two choices that enter the proof’s divisibility estimate at an inert prime. On a curve with complex multiplication by the ring of integers of $\mathbb Q(\sqrt{-7})$, the unscaled change of coordinate has a denominator of $5$ at degree $25$. Every unit in the local CM field leaves that denominator. The released statement allows a larger field. A separate quadratic constant in the theta function is rigid. A change of one spoils a required integrality relation already at degree $10$. We identify the actual constant on this curve and check that relation in every degree. These tests concern an input to the estimate. The complete automorphic construction has further hypotheses.

## The field matters at degree 25

Take $E:y^2=x^3+Ax+B$ with $A=-35$, $B=-98$ and $\omega=(1+\sqrt{-7})/2$. This elliptic curve has CM by $\mathbb Z[\omega]$, its invariants are $g_2=140,g_3=392$, and its discriminant is a unit at $5$. The prime $5$ is inert since $-7$ is a nonsquare modulo $5$. Thus $F=\mathbb Q_5(\omega)$ has residue field $\mathbb F_{25}$. These parameters meet the discriminant, inertness and prime-size restrictions of the local CM statement. [Zagier, curve (101) and its CM endomorphism](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1007/978-3-540-74119-0_1/fulltext.pdf) · [Logarithm, good model and actual quantifiers](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean#L35-L55)

Put $t=-x/y$ at the identity, and write $\ell(t)$ for the elliptic formal logarithm with differential $dx/(2y)$ and linear coefficient one. For $n=2m+1$,

$$
 n[t^n]\ell(t)=[x^{2m}](x^3+Ax+B)^m .
$$

Indeed the left side is the residue of $t^{-n}dx/(2y)$ at infinity. Substituting $t=-x/y$ gives $-(x^3+Ax+B)^m dx/(2x^{2m+1})$. The map $x:E\to\mathbb P^1$ has ramification index two at infinity, giving the displayed coefficient. Even powers in $\ell$ vanish by inversion on $E$.

All coefficients below degree $25$ are 5-integral. The only odd denominators divisible by $5$ to check are $5$ and $15$. Their numerators are $2A$ and $105A^2B$. At degree $25$ the numerator is
$$
 924A^6+7920A^3 B^2+495B^4 .
$$
Consequently $5[t^{25}]\ell(t)\equiv99B^4\equiv-1\bmod5$.

Now use the logarithm in the release, $L(X)=X+X^{25}/5+X^{625}/25+\cdots$, and let $h(X)=\ell^{-1}(uL(X))$ with $u$ a unit. Its coefficients below degree $25$ are integral by triangular substitution. Comparing degree $25$ in $\ell(h(X))=uL(X)$ gives
$$
 5[X^{25}]h(X)\equiv \bar u+\bar u^{25}\pmod5 .
$$
For every $u\in O_F^\times$ this is $2\bar u\ne0$. Thus $v_5([X^{25}]h)=-1$ for every permitted unit **if one insists on the original local CM field**. At $u=1$ the exact coefficient is $12255462837/605$. Two computations, one from the logarithm and one from $-2\wp/\wp'$, give the same result. [Exact check](check_cm7_jets.py)

The source takes a topological closure inside $\mathbb C_5$. Its residue field is algebraically closed. The obstruction at degree $25$ requires $\bar u^{24}=-1$, which has solutions of order $48$ in $\mathbb F_{625}^\times$. For higher degrees the release solves a twisted Frobenius equation in the complete field. The mechanism is visible by hand. To solve $u=c\,\sigma^2(u)$ modulo $5$, start with a nonzero root of $x^{24}=\bar c^{-1}$. When the error is divisible by $5^k$, correcting $u$ by $5^k y$ requires solving an equation $y-\bar c\,y^{25}=b$ in the residue field. A solution exists, and the successive corrections converge. A finite unramified extension can genuinely be too small for this argument even when $c$ is rational. For $c=6$, iterating the equation through the finite order of $\sigma^2$ there would give $u=6^a u$ for some $a>0$. [The field actually defined](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean#L12-L15) · [Residue-field and logarithm hypotheses](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/LatticeFrames/EndOmega.lean#L13-L31) · [Frobenius correction](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsUnitSolutionTwistedFrobeniusSquare.lean#L62-L82) · [Where the unit enters the formal coordinate](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HeightTwoFormalGroupUnramifiedMultiplier.lean#L13-L29) · [The same unit in the coefficient bound](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/OneSubTwoOmegaSq.lean#L148-L158)

## An explicit multiplier in every degree

For this curve the extension can be made precise for every good inert prime $p\ge5$. Set $q=p^2$. Let $u$ be a root of unity of order $2(q-1)$ in the unramified extension of $\mathbb Q_p$ of degree four. Then **$\ell^{-1}(uL_+(T))$ has integral coefficients in every degree**, where $L_\pm(T)=\sum_{j\ge0}(\pm1)^j T^{q^j}/p^j$. No unit in the unramified quadratic field suffices.

Here is a proof. The trace of Frobenius on this CM curve is zero at a good inert prime. At $p=5$ this also follows at once by counting its reduction $y^2=x^3+2$, since cubing permutes $\mathbb F_5$. Frobenius $\Phi$ satisfies $\Phi^2+[p]=0$ on the special fibre. In the odd parameter $t=-x/y$ this gives $[p]_E(T)\equiv-T^q\bmod p$. For $L_+$ the multiplication-by-$p$ series through degree $q$ is $pT+(1-p^{q-1})T^q$. An integral isomorphism with linear term $u$ must intertwine the two multiplication series, forcing $\bar u=-\bar u^q$. This is impossible for a nonzero residue in $\mathbb F_q$. [Zagier, inert-prime trace for curve (101), equation (102c)](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1007/978-3-540-74119-0_1/fulltext.pdf) · [Frobenius polynomial, Corollary 2.4](https://link.springer.com/article/10.1007/s10231-024-01528-x)

For sufficiency, $\ell'$ is integral since it is the invariant differential in the good model. If $A,B$ are integral series of constant term zero and $A\equiv B\bmod p$, then $\ell(A)-\ell(B)\in pO[[T]]$. Indeed $\ell_n$ is an integral coefficient divided by $n$, and in expanding $(A^n-B^n)/n$ the term with $(A-B)^j$ has factor $\binom{n-1}{j-1}/j$. Its valuation is at least $j-v_p(j)\ge1$. Apply this to $A=[p]_E(T)$ and $B=-T^q$. Since $\ell$ is odd,
$$
 V(T)=\ell(T)+p^{-1}\ell(T^q)\in\mathbb Z_p[[T]].
$$

We claim $g=\ell^{-1}\circ L_-$ lies in $\mathbb Z_p[[T]]$. Suppose an integral truncation $A$ of $g$ gives $\ell(A)-L_-=O(T^n)$. Then
$$
 \ell(A)-L_-= V(A)-T-
 \frac{\ell(A^q)-\ell(A(T^q))}{p}
 -\frac{(\ell(A)-L_-)(T^q)}p.
$$
The middle quotient is integral by the preceding congruence since $A(T)^q\equiv A(T^q)\bmod p$. The last term begins in degree $qn>n$. Thus the error in degree $n$ is integral and can be removed by an integral coefficient, as $\ell'(0)=1$. Starting with $A=T$ proves the claim by induction. Finally $u^{q-1}=-1$ and $q$ is odd, so $L_-(uT)=uL_+(T)$. Substituting $uT$ in $g$ proves the assertion. In particular this model establishes the coordinate required below without recourse to the proof checker.

## The quadratic correction cannot be chosen freely

The analytic sigma function used here is $\Sigma_s(z)=\sigma_E(z)\exp(-s z^2/2)$. Fix a successful unit $u$ and the integral Honda formal group $F_H$ with logarithm $L$. The release's logarithmic correction $\phi_s(T)$ changes by $(b/2)u^2 L(T)^2$ on replacing $s$ by $s+b$. Its norm relation at $\alpha$ requires
$$
 \exp\!\big(\phi_s([\alpha]T)-\alpha\bar\alpha\,\phi_s(T)\big)\in O[[T]],
 \qquad L([\alpha]T)=\alpha L(T).
$$
Here $\bar\alpha$ is the nontrivial automorphism of the unramified quadratic field. For $\alpha=\omega$, $\alpha\bar\alpha=2$. [Complex normalization](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/SemiChar.lean#L13-L25) · [The correction in Honda coordinates](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/StatementE.lean#L19-L31) · [The norm relation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/StatementC.lean#L19-L30) · [Integrality in the relation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/CyclicPowerClassOfExpEquiv.lean#L22-L26)

Suppose both $s$ and $s+b$ pass. Dividing the two integral series, each with constant term one, would make $H(T)=\exp(k L(T)^2)$ integral, where $k=(b/2)u^2(\omega^2-2)$. But then
$$
 \frac{H(F_H(X,Y))}{H(X)H(Y)}=\exp(2kL(X)L(Y))
$$
would be integral as well. Its coefficient of $X^{25^j}Y$ is exactly $2k/5^j$ for every $j\ge0$. This forces $k=0$ and hence $b=0$. Third differences alone would miss this. The mixed term $cXY$ in additive coordinates has zero difference on splitting either variable. The additional CM symmetry fixes what those differences cannot see.

The first finite test is small. Through degree $10$ divide the coefficient of degree $n$ by the unit $u^n$. The coefficients at degrees $2,4,6,8,10$ of the remaining logarithm before applying the norm relation are
$$
 s/2,\quad 7/12,\quad 7/15,\quad 7/24,\quad 49/165 .
$$
They follow by twice integrating $\wp(z)-z^{-2}$, with the indicated quadratic term. The norm relation multiplies the degree-$n$ coefficient by $\omega^n-2$. Since $\omega^5\equiv\bar\omega\bmod5$, the degree-six term becomes integral. At degree ten the only possible denominators of $5$ come from the logarithm's tenth coefficient and the fifth power of its quadratic coefficient divided by $5!$. Put $\omega_0=\omega\bmod5$. Five times the resulting coefficient reduces to
$$
 (\omega_0^{10}-2)\big(49/33-(s/2)^5\big)
 \quad \text{in }\mathbb F_{25},
$$
The first factor is nonzero since $\omega_0^{10}-2=-3-\omega_0$. Among $s\in\mathbb Z_5$, precisely $s\equiv1\bmod5$ passes. The all-degree argument above rules out even an arbitrarily close but unequal correction. [Weierstrass primitives and sign](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/CurveHyp.lean#L20-L37) · [Exact series check](check_cm7_jets.py)

## Matching the complex and 5-adic constants on this curve

Write the period jump of the Weierstrass zeta function as $s\lambda+c\overline\lambda$ for $\lambda$ in the period lattice. This defines the same $s$ as in the source. For multiplication by $\omega$ the kernel has order two. Let $T$ be its nonidentity point and $e=\wp(T)$. The identity
$$
 \omega^2\wp(\omega z)=\wp(z)+\wp(z+T)-e
$$
follows by matching the poles and the constant term at zero. Taking the period jumps after integration gives $(\omega^2-2)s=e$. The $z^2$ coefficient gives $7\omega^4=3e^2-28$ using $\wp''=6\wp^2-70$. Since $\omega^2=\omega-2$, the unique root of $x^3-35x-98$ with this square is $e=\omega-4$. Hence **$s=1$ exactly**.

For the all-degree check, take any nonzero $\gamma\in\mathbb Z[\omega]$ with $n=\gamma\overline\gamma$ prime to $5$. Put $\Sigma=\Sigma_1$. Then
$$
 \left(\frac{\Sigma(\gamma z)}{\gamma\,\Sigma(z)^n}\right)^2
 =\prod_{T\in E[\gamma]\setminus\{0\}}\big(\wp(z)-\wp(T)\big).
$$
After division by the right side the zeros and poles cancel, with both points in each pair $T,-T$ accounted for. The exponential in the period multiplier of $\Sigma$ depends on $\overline\lambda(z+\lambda/2)$, so the multipliers agree by $\gamma\overline\gamma=n$. Squaring removes the signs. The quotient is an elliptic function without poles, and its leading term at zero is one.

In the elliptic parameter set $\phi(t)=-\log(\Sigma(\ell(t))/t)$. The square of $\exp(\phi([\gamma]t)-n\phi(t))$ is therefore
$$
 \left(\frac{[\gamma]t}{\gamma t}\right)^2
 \prod_{T\ne0}\big[t^2(x(t)-x(T))\big]^{-1},
 \qquad T\in E[\gamma].
$$
Every factor is integral and has constant term one. The CM action extends over the good model. For the generator $\omega$, the half-period formula gives $x(\omega z)=\omega^{-2}\big(x+(3e^2+A)/(x-e)\big)$. Its derivative supplies the corresponding formula for $y(\omega z)$. Both $1/x$ and $1/(x-e)$ are integral series starting in degree two. A nonzero prime-to-$5$ torsion point cannot reduce to the identity, since multiplication by its order has unit linear term on the formal group. Thus $x(T)$ is integral. Since $2$ is a unit, the square root with constant term one is integral.

The algebraic $\gamma$ of norm prime to $5$ are dense in $O_F^\times$. At each fixed degree the expressions above depend continuously on $\gamma$ and its conjugate, giving the norm relation for all these local units. To change to Honda coordinates substitute $t=h(T)$. The further factor $uT/h(T)$ is an integral unit with constant one. Its power by any exponent in $\mathbb Z_5$ stays integral by the binomial expansion. The preceding multiplier construction supplies the integral Honda coordinate, completing the norm-relation check for this curve at $5$.

## Where the estimate uses it

The source takes the algebraic image of the complex $s_2$ and multiplies it by the square of the Weierstrass coordinate scale. It uses this value both in the rescaled sigma series and in the local norm relation. It keeps the Honda unit and the outer rescaling of the entire kernel as separate data. The latter is harmless for the displayed column estimate because all the terms of a fixed product of minors have the same derivative degree at each site. The release takes ordinary derivatives and its coefficient formula includes the product of the factorials of its multi-index. [Choice of the actual quadratic coefficient](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/PadicNormTwoHundredSixteenEqOneOfFiveLe.lean#L687-L710) · [Agreement of the two normalizations](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/InertKernelTheory/DefsRepDict.lean#L10-L21) · [Curve data and the kernel](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/ExistsConstantCoeffOne.lean#L18-L44) · [Minors and factorials](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/Divisibility/ProductZerothFirstParts.lean#L82-L102) · [Removing the unit from the jet](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ProdOfMemSupport.lean#L58-L87) · [One local choice before the lattice and kernel vary](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/AdmissibleKernelSeriesInertPrimeNonConjugateFrob.lean#L26-L43)

## Reproduce the finite check

Run `python receipt-archives/check_cm7_jets.py`. It compares series inversion with the Weierstrass recurrence through degree 25, tests all 24 nonzero residues and checks the corrected coordinate through degree 149. It also checks the Frobenius sign at $p=5,17,19,31,41$ and all five rational residues of $s$ through degree 10. The proofs above specify the claims beyond this finite range.

## Unresolved

The first denominator is a counterexample over the initial CM field. The release works over the completed maximal unramified field. We also exhibited a finite extension sufficient in all degrees for this curve. The quadratic identity was checked here for discriminant $-7$. The later many-variable estimate must still carry the local correction, torus average and choice of frame into the very same period. [Valuation descent](2026-11-23-valuation-descent.md)
