# The two zeros at the Hecke boundary

**23 November 2026.** At $s=1$ two different operations can return zero. The release explicitly sets its zero Fourier mode to zero at the continuation point. In the conductor-137 example this is the correct limit, although the derivative of that mode with respect to the continuation parameter is strictly positive. A second zero comes from evaluating the unconditional lattice sum directly where it diverges. That zero gives a **wrong value for the whole function**. For the identity class the continued value in the normalization below is strictly between **0.00595240410576** and **0.00595240410577**. We traced which zero the arithmetic calculation receives. [The written-in zero](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KFacDifferentiable.lean#L43-L55) · [The raw sum](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L64-L71) · [The value and the coordinates actually differentiated](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/DefiningCoordinates.lean#L23-L33)

## A disappearing term with a nonzero derivative

Use the [34 actual ring classes](2026-11-23-toric-fourier.md), $F=\mathbb Q(\sqrt7)$, $E=F(i)$ and $\tau=(1+i\sqrt7)/2$. Write $\sigma$ for the continuation parameter. The release evaluates at $\sigma=0$. Write $\mathcal L\subset F^2$ for the coefficient pairs in one of its lattices, $I$ for the slice where the second coordinate $b$ vanishes and $J$ for the ideal of possible $b$. At complex arguments $z_j=x_j+i y_j$ with $y_j>0$, the unnormalized summand is the product over the two real embeddings of
$$
  (a_j+b_jz_j)^{-2-m_j}(a_j+b_j\bar z_j)^{m_j}
                 |a_j+b_jz_j|^{-2\sigma}.
$$
The nonnegative $m_j$ are the two derivative weights. At $z_1=z_2=\tau$ this is exactly the series defining the arithmetic lattice value in its convergence half-plane. [Unit orbits, convergence and evaluation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L81-L103)

For $\operatorname{Re}\sigma>0$, sum first over $a$ for each nonzero $b$ modulo real units. Its possible values form one coset of $I$. In the zero frequency of Poisson summation the coset's phase is one. After rescaling the real variable and putting it equal to $\cot\theta$, its archimedean integral is
$$
 C_m(\sigma)=\int_0^\pi\sin^{2\sigma}\theta\,e^{-2i(m+1)\theta}\,d\theta
       =-\frac{\pi}{m+1}\sigma+O(\sigma^2).
$$
The sign of $b_j$ gives the same integral by reflection. For the derivative at zero, expand $\log(2\sin\theta)$ in cosines and integrate against the $(m+1)$-st cosine. Equivalently, divide by $\int_0^\pi\sin^{2\sigma}\theta\,d\theta$ to obtain $(-1)^{m+1}\prod_{j=0}^m(\sigma-j)/(\sigma+j+1)$.

In real degree $f$ the zero-frequency contribution from $b\ne0$ is therefore
$$
 Z_{\mathcal L}(\sigma,z)=
 \frac{(NJ)^{-1-2\sigma}}{\sqrt{|d_F|}\,NI}\,
 \zeta_{[J]^{-1}}(1+2\sigma)
 \prod_{j=1}^f y_j^{-1-2\sigma} C_{m_j}(\sigma).
$$
Here $NI,NJ$ are the positive ideal norms. The partial zeta function has a simple pole at one. The product has a zero of exact order $f$, so the whole term has order **$f-1$**. In real degree one, $I=J=\mathbb Z$ gives the genuine residual value $-\pi/(2(m+1)y)$. The release explicitly requires $f\ge2$ at this inference. [Degree requirement and continuation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L124-L134) · [How the zero and pole are compared](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic.lean#L34-L84)

In our field $h_F=1$, and the positive fundamental unit is $\varepsilon=8+3\sqrt7$. The residue of $\zeta_F(s)$ is $2\log\varepsilon/\sqrt{28}$. For a direct check count generators with first embedding positive and $0\le\frac12\log |x_1/x_2|<\log\varepsilon$. There is one such element per integral ideal. For each sign of $x_2$, the coordinates $|x_1x_2|$ and $\frac12\log|x_1/x_2|$ have Jacobian of absolute value one. Counting lattice points with norm at most $X$ consequently gives $2X\log\varepsilon/\sqrt{28}+O(\sqrt X)$. Partial summation gives the stated residue. The two lattice indices $[O_E:O_F[\tau]]=7$ and $[O_E:L_r]=137$ give $NI\,NJ=137/7$ for each of the 34 classes. Substituting $y_j=\sqrt7/2$ gives the exact first-order term
$$
 Z_{\mathcal L}(\sigma,\tau)=
 \frac{\pi^2\log(8+3\sqrt7)}{959(m_1+1)(m_2+1)}\,\sigma+O(\sigma^2).
$$
This is the unnormalized class series. The source's local chart includes explicit powers of $2\pi i$. The order of vanishing is the same. The positive slopes are identical across the 34 unweighted classes, so their transform is supported on the trivial character, up to the fixed base-character shift.

## Checking the rest of the limit

The separate $b=0$ contribution is $(NI)^{-2-2\sigma}\zeta_{[I]^{-1}}(2+2\sigma)$. It is regular near zero. For a nonzero frequency $\nu\in I^\vee=\mathfrak d_F^{-1}I^{-1}$, shift the Fourier integral for the scaled real variable by $-\tfrac12i\,\operatorname{sign}(\sigma_j(\nu))$, where $\sigma_j:F\hookrightarrow\mathbb R$ denotes an embedding. The scaled kernel has no singularity in this strip. There is a single-valued logarithm of $1+u^2$ there agreeing with the real one. On compact subsets of $\operatorname{Re}\sigma>-1/2$, its tail is bounded by a constant times $(1+|u|)^{-2-2\operatorname{Re}\sigma}$. The shift gains an exponential in $-|\sigma_j(b\nu)|y_j$.

The product over the places is bounded, with any fixed number of real $z$-derivatives on compact sets, by
$$
 C\, |N b|^{-1-2\operatorname{Re}\sigma}
 (1+\textstyle\sum_j|\sigma_j(b\nu)|)^A
 \exp(-c\textstyle\sum_j|\sigma_j(b\nu)|).
$$
For imaginary-coordinate derivatives, differentiate the original kernel before rescaling. Each factor $b_j/(u\pm i b_j y_j)$ then costs at most a constant times $1/y_j$ on the shifted contour. Real-coordinate derivatives supply powers of the Fourier frequencies. For fixed $\alpha=b\nu$ there are at most polynomially many pairs modulo units, since $(b)J^{-1}$ divides $(\alpha)(JI^\vee)^{-1}$. The $\alpha$ lie in the fixed lattice $JI^\vee$ and $|Nb|\ge NJ>0$. The exponential bound gives normal convergence. At zero, for $m_j=0$, a residue computation leaves precisely the totally positive frequencies with the holomorphic coefficients in the [all-cusps calculation](2026-11-23-toric-cm-denominators.md#denominators-of-the-fourier-coefficients), now with $k=2$. This argument allows a nontrivial coset for each $b$.

For positive derivative weights write $Y=\prod y_j$, $t_j=1/(2\pi i(z_j-\bar z_j))$ and use the raising operators from the [derivative check](2026-11-23-toric-cm-derivatives.md). In the convergence region they give the exact identity
$$
 \prod_j\delta_{2,j}^{[m_j]}(Y^\sigma E_{\mathcal L,0})
   =Y^\sigma \prod_j(2+\sigma)_{m_j} t_j^{m_j} E_{\mathcal L,m}.
$$
One differentiation of a summand gives the factor $(2+\sigma+m_j)t_j(\bar w_j/w_j)$, $w_j=a_j+b_jz_j$, at step $m_j$. The normal convergence just proved extends the identity to zero. The rising factorials have nonzero values there. The arithmetic derivative is in the $z_j$ coordinates, so the first-order term in $\sigma$ is not inserted into the value. [The two types of derivative at the consumer](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmLatticeDerivClassInvarianceOfHecke.lean#L165-L199)

## A raw zero and a positive continued value on the same input

Take the identity class and zero derivative weights. Every $L_r$ contains $137O_E$. The absolute sum at $\sigma=0$ is infinite since its positive terms include, up to the fixed norm factor, at least one generator for every integral ideal of the class-number-one field $E$, and $\zeta_E$ has a pole at one. The unconditionally indexed complex sum is therefore nonsummable. The release's library assigns such a `tsum` the value zero. [Pinned Mathlib definition](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean#L108-L130)

For an independent value let $M$ be the continued principal class function multiplied by $\sqrt{28}/(2\pi i)^4$, as in our previous normalization. Put $w=\sqrt7$ and $\rho=12+w$. The identity-class order is $O_F+\rho O_F\,(\tau-4)/w$. Indeed $(\tau-4)/w=i\tau=(i-w)/2$ completes a basis of $O_E$ over $O_F$. Thus $I=O_F$, $J=(\rho/w)O_F$ and the coset of $a$ is $-4b+O_F$. With $\delta=u+v\sqrt7$ totally positive, the Fourier frequency is $\alpha=(\rho/14)\delta$. Its trace is $(12u+7v)/7$. Grouping the frequency pairs by $\delta$ gives
$$
 M=\frac{1}{168}+\frac1{28}
 \sum_{\substack{u,v\in\mathbb Z\\u>|v|\sqrt7}}
  (-1)^v\,\sigma_1((u+v\sqrt7))\,e^{-\pi(12u+7v)/\sqrt7},
$$
where $\sigma_1$ sums the norms of the ideal divisors. The sign comes from $\operatorname{Re}(\tau-4)=-7/2$. The small positive constant is $\zeta_F(-1)/(4\cdot28)=1/168$.

The norm of $(u+v\sqrt7)$ is at most $u^2$, and the number of ideal divisors is at most that norm. At fixed $u$ there are at most $2u$ values of $v$. The exponential is smaller than $4096^{-u}$. These facts bound the omitted tail by a geometric majorant after only four $u$-values. Exact rational intervals for the first terms give the enclosure at the top of this receipt. On the native raw inputs take $\mathfrak a=\mathfrak d_F^{-1}$, $\mathfrak b=(\rho/w)O_F$ and $z_j=\tau-4$. Its `eisSum` is zero at the boundary but its continued function has value $M/\sqrt{28}>0$. The source gives the raw-sum identity on $\operatorname{Re}\sigma>0$ and supplies the value at zero by continuation. [Trace-dual lattice and the factors in the native chart](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L32-L52) · [Which branch the Eisenstein value uses](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/JetAnalytic.lean#L193-L199) · [Exact interval and divisor calculation](check_toric_boundary.py)

There is a separate test for all 34 character functions at the boundary. For a nontrivial residue character, terms divisible by both primes over the conductor cancel when summed over the class labels. A term divisible by exactly one of the two primes belongs to no selected lattice. Each ideal prime to the conductor contributes once. The resulting series in the convergence region is the Hecke $L$-series for its unitary character. For the trivial residue character, the local multiplier on the unramified Hecke series is $1-(A+A^{-1})X+137X^2$, where $X=137^{-1-\sigma}$ and $A$ is the unitary character at one split prime. Indeed there is one unit orbit at valuations $(0,0)$, and $136$ at each pair of strictly positive valuations. Here $A+A^{-1}=-174/137$ since $5+4\sqrt{-7}$ has norm 137. The multiplier at the boundary is $19080/18769\ne0$. Every resulting Hecke character and its square have nonzero infinity type. Their $L$-functions are holomorphic at one, and nonvanishing of the first there follows from the Euler-product inequality $\zeta_E(t)^3|L(t,\chi)|^4|L(t,\chi^2)|\ge1$ for real $t>1$. Its primewise logarithm uses $3+4\cos\theta+\cos 2\theta\ge0$, and at omitted ramified factors the positive zeta term dominates. A zero at one would contradict the simple pole order of $\zeta_E$. Hence all 34 continued character sums are nonzero, whereas substituting raw zero sums before the transform would give 34 zeros. [Field, generators and characters](2026-11-23-toric-fourier.md#an-allowed-field-conductor-and-character) · [Hecke continuation used by the release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEntireLatticeSumOfHeckeLContinuation.lean#L352-L371)

## What reaches the arithmetic comparison

The Fourier argument at every cusp and the CM self-isogeny argument now apply at $k=2$. Since $\zeta_F(-1)/4=1/6$, the zero-derivative clearing factor before the twelfth power is $6\cdot28\cdot137^2$. If $r=m_1+m_2$, the independently bounded denominator exponents at $2,3,7,137$ are respectively $36+36r$, $12$, $12+18r$, $24+12r$. The source allows $60+48r$, $12$, $24+30r$, $96+60r$. Both give integrality at every other prime, including 17. The class constants at the original cusp are $1/168$ and $1/(168\cdot137^2)$. The transformed constants again have valuation exactly one at 17. This closes the boundary case for these arithmetic data and every derivative weight in the denominator statement. [Quantified denominator bound](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/VpBounds.lean#L65-L82) · [Classwise integrality from every cusp](2026-11-23-toric-cm-denominators.md) · [The treatment of positive derivatives](2026-11-23-toric-cm-derivatives.md)

## Unresolved

Replacing the continued value by the unconditional sum would erase a known positive class value. Assigning zero just to the zero frequency has the correct value in this field and retains a measurable first derivative in the continuation parameter. Testing the broader denominator claim requires carrying the field degree, ideal classes, local different and quadratic CM generator through the estimates. Neither classwise integrality nor this boundary calculation identifies the Galois conjugate of a normalized period.
