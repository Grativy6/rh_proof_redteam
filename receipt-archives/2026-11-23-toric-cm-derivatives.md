# Positive derivatives at the conductor-137 CM point

**23 November 2026.** The first derivative exposes a possible false alarm in the arithmetic estimate. Two holomorphic modular forms give **the same derivative at the CM point**. At the original cusp one constant coefficient has 3-adic valuation **$-2$**, the other **$-1$**. Evaluating the first cusp coefficient as if it were the CM value would spend an extra power of 3. We tested the actual CM evaluation, including at the supersingular prime 17. The denominator allowance survives for **every pair of nonnegative derivative weights** in the 34-class example.

Let $r=\kappa_1+\kappa_2$. The bounds below are on the normalized twelfth powers. Each entry is a permissible denominator exponent, and zero means integral at that prime.

| Rational prime | Independent bound | Release allowance |
| --- | ---: | ---: |
| 2 | $132+36r$ | $252+48r$ |
| 3 | $12$ | $12$ |
| 7 | $60+18r$ | $120+30r$ |
| 11 | $12$ | $12$ |
| 137 | $120+12r$ | $480+60r$ |
| All other primes, including 17 | $0$ | $0$ |

The arithmetic data are $F=\mathbb Q(\sqrt7)$, $E=F(i)$, $d=7$, $\tau=(1+\sqrt{-7})/2$, conductor $(12+\sqrt7)$ and $k=2s=10$. The [zero-derivative calculation](2026-11-23-toric-cm-denominators.md) supplies the lattices, their simultaneous cusp bounds and the class function used below. [Source sum and its twelfth power](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L89-L111) · [Local arithmetic costs](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/VpBounds.lean#L26-L47) · [Released denominator requirement](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/VpBounds.lean#L65-L82)

## The derivative the source actually measures

Use the same holomorphic series $M(z_1,z_2)$ as in the preceding calculation, allowing the two complex variables to vary independently before restriction to their diagonal. It has weight $(k,k)$ under simultaneous modular transformations. Write $D_i=(2\pi i)^{-1}\partial/\partial z_i$, $t_i=1/(2\pi i(z_i-\bar z_i))$, and $\delta_{h,i}=D_i+h t_i$. Each application raises the $i$-th weight $h$ by two. At $(\tau,\tau)$ the normalized arithmetic term in the release is exactly the iterated raised value, with $\kappa_i$ applications in variable $i$, before division by the discriminant.

Indeed for one factor set $x=a+b\tau$. Expanding $(\bar x/x)^m=(1-(\tau-\bar\tau)b/x)^m$ gives the coefficients
$$
 \delta_k^{[m]} f=\sum_{j=0}^m\binom mj(k+j)_{m-j}\,t^{m-j}D^j f
$$
for $f(z)=(a+bz)^{-k}$ at $\tau$. Here $(h)_j$ denotes a rising factorial and $\delta_k^{[m]}$ uses the successive weights. The formula also follows by induction from $Dt=-t^2$. The factor $\Gamma(k+m)/\Gamma(k)=(k)_m$ and the scale $(2\pi/\sqrt7)^m$ in the source give precisely this identity after dividing by the extra $(2\pi i)^{2m}$. Both variables together give a value of weight $2k+2r$. Compact convergence permits the differentiations because $|b/(a+bz)|\le1/\operatorname{Im}z$. [Gamma factors, weight and scale](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PairingDivisors/StatementH.lean#L44-L50) · [Exact termwise checks](check_toric_derivatives.py)

## Two representatives already differ at the first derivative

First use the usual holomorphic weight-two series $E_2$ and $E_2^*=E_2-3/(\pi\operatorname{Im}z)$. The form $H(z)=(2E_2(2z)-E_2(z))|_2 S$ for $S:z\mapsto-1/z$ equals $\tfrac12E_2(z/2)-E_2(z)$. It has constant coefficient $-1/2$. Since $-2/\tau=\tau-1$,
$$
 E_2^*(\tau)=c_\tau H(\tau),\qquad
 c_\tau=\frac{\tau^2}{2-\tau^2}=\frac{-7+\sqrt{-7}}{14}.
$$
The holomorphic function
$$
 (D_1M)(z,z)+\frac{k}{12}\big(c_\tau H(z)-E_2(z)\big)M(z,z)
$$
has the correct modular transformation law and gives $\delta_{k,1}M$ at $\tau$. In the identity class its constant is $k(-c_\tau/2-1)b_0/12$, where $b_0=52955730841/(66\cdot28^5)$. This has valuation $-2$ at every place over three, because $N_{\mathbb Q(\sqrt{-7})/\mathbb Q}(c_\tau+2)=16/7$ and $v_3(b_0)=-1$.

For the second representative use $P(z)=\theta_3(z)^2$, a nowhere-zero weight-one theta form on $\Gamma(2)$ with a multiplier. Put $U_P=D\log P$, $V_P=U_P+t$ and
$$
 A=\begin{pmatrix}1&-2\\1&0\end{pmatrix},\qquad
 J_A=U_{P|_1 A}-U_P .
$$
The determinant of $A$ is two, $A\tau=\tau$ and $\lambda=A'(\tau)=2/\tau^2$. Logarithmic differentiation of the weight-one slash action gives
$$
 J_A(\tau)=(\lambda-1)V_P(\tau),\qquad
 (\lambda-1)^{-1}=-\tau/\sqrt{-7}.
$$
The difference $J_A$ is a genuine holomorphic form of weight two on a finite-index congruence subgroup. The multiplier is constant under each transformation and disappears on logarithmic differentiation. Thus
$$
 (D_1M)(z,z)+k\big((\lambda-1)^{-1}J_A(z)-U_P(z)\big)M(z,z)
$$
is another holomorphic representative of the same CM derivative. Its original cusp constant is $k(\lambda-1)^{-1} b_0/8$, of valuation $-1$ at three. To check $1/8$, factor $A=TS\operatorname{diag}(1,2)$ with $T:z\mapsto z+1$. The theta-square after $TS$ is a constant times $\theta_2^2$, of leading exponent $1/4$ in $q=e^{2\pi iz}$. Substituting $z/2$ halves that exponent. [Jacobi theta transformation formulas](https://dlmf.nist.gov/20.7#viii) · [Theta product formulas](https://dlmf.nist.gov/20.5)

## Checking the allowance in every order

Here are the bounds that make the second calculation work in all weights. On applying a simultaneous integral cusp transformation, the theta-square becomes a constant times one of $\theta_2^2,\theta_3^2,\theta_4^2$. For any of these, $4U_P$ has integral Fourier coefficients. For $\theta_2$ remove the leading $2q^{1/8}$ before logarithmic differentiation; for the other two the leading coefficient is one. All nonconstant exponents of $U_P$ are in $\tfrac12\mathbb Z$. Therefore $16(DU_P-U_P^2)$ has integral coefficients. At an arbitrary cusp $A\gamma$ has determinant two. An integral determinant-one matrix followed by an upper triangular matrix with positive diagonal $a,d$ and $ad=2$ gives its Hermite normal form. The logarithmic derivative after $z\mapsto(az+b)/d$ has the extra factor $a/d$ and root-of-unity phases. Thus $8J_A$ has algebraic-integer Fourier coefficients at every cusp. The denominator of $(\lambda-1)^{-1}$ costs at most a half unit of normalized 7-adic valuation.

For a holomorphic coefficient $f$ of $i$-th weight $h$, $D_i f-h U_P(z_i)f$ is covariant. In the nearly holomorphic expression one also has
$$
 \delta_{2,i} V_P(z_i)=V_P(z_i)^2+(D_iU_P(z_i)-U_P(z_i)^2).
$$
These identities express every successive raised form as a polynomial in $V_P(z_1),V_P(z_2)$ with holomorphic covariant coefficients. At the CM point replace both variables by $(\lambda-1)^{-1}J_A(z)$ after diagonal restriction. The result is a holomorphic modular representative of weight $2k+2r$. One may restrict to a common principal congruence subgroup for all the factors.

In the Fourier series of the original two-variable function, a partial derivative multiplies a coefficient by one embedding of $b\nu$. The [lattice bounds](2026-11-23-toric-cm-denominators.md#denominators-of-the-fourier-coefficients) give $b\in7^{-1}O_F$, $\nu\in\mathfrak d_F^{-1}I^{-1}$, $\mathfrak f\subseteq I$ and $\mathfrak d_F=(2\sqrt7)$. Thus $b\nu$ has possible denominator valuations at most $1$ at 2, $3/2$ at 7 and $1$ at 137. The theta factors add only dyadic frequency denominators. Set per-application costs $B_2=3,B_7=3/2,B_{137}=1$ and $B_\ell=0$ elsewhere. They bound each partial differentiation of a holomorphic coefficient and each use of $U_P$ or the final substitute for $V_P$. The coefficient $DU_P-U_P^2$ costs at most $2B_\ell$.

More precisely, after $r$ applications, the coefficient of a monomial of total $V_P$-degree $j$ costs at most $(r-j)B_\ell$ beyond the original Fourier coefficient bound. A derivative on that coefficient uses one cost. Creating one more $V_P$ uses none at that step. Replacing one $V_P$ by $DU_P-U_P^2$ uses two and lowers the degree by one. All combinatorial factors are integers. This is an induction at every cusp, with the theta-square appropriate to that cusp. At the final substitution the total is at most $rB_\ell$.

The original common denominator was $D_\ast=66\cdot28^5\cdot137^{10}$. Hence multiplying the holomorphic representative by $D_\ast(8\cdot7\sqrt7\cdot137)^r$ gives algebraic-integer coefficients at every cusp. Its twelfth power divided by $\Delta^{2k+2r}$ has weight zero. Applying the same monic-polynomial argument at $j(\tau)=-3375$ gives the independent column of the table. All 34 normalized lattice values, and therefore their sums against character roots of unity, obey the bound. This checks the valuations for every derivative order for which a character in the original arithmetic statement is used. [Released derivative obligation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/JetAnalytic.lean#L239-L245) · [Transition to the twelfth power](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeValueIntegralityUnramifiedOfJetIntegralit.lean#L297-L313)

## Unresolved

A cusp of the first holomorphic representative really does require an extra factor of three, even though it represents the correct derivative at the CM point. The second representative shows independently that the CM value fits the release's arithmetic allowance. For this field the same calculation applies at every $s\ge2$, replacing the base zeta denominator and the weight $k$ as in the [undifferentiated calculation](2026-11-23-toric-cm-denominators.md#scope-and-unresolved-step). Extra conductor places away from the inspected rational prime do not increase its local cost. The limiting $s=1$ series falls outside the absolute-convergence proof. Another scope boundary is the use here of the real quadratic field and the discriminant $-7$ self-isogeny when testing data from the larger family.
