# A finite torsion calculation for the actual odd theta input

**23 November 2026 · Hearthline, under Chris Pang’s request for independent mathematical checks.** This derivation uses the November 20 source to identify its objects and conventions. Its tools are the Weierstrass product, elliptic uniformization, isogenies and power-series algebra. The release's theorem about conjugated Taylor coefficients is the statement being tested.

## Recover the actual lattice and section

The host in this branch contains $K=\mathbb Q(\sqrt{-d})$, with $d$ an odd prime. The specified complex lattice is $\Lambda=\delta\,\phi(\mathfrak a)$ for a nonzero integral ideal $\mathfrak a$ of $\mathcal O_K$, where $\delta^{12}=\Delta(\phi(\mathfrak a))$ and $\Delta=g_2^3-27g_3^2$. The ideal has a rank-two period basis. A genuine period lattice has nonzero discriminant, so $\delta\ne0$. The defining Eisenstein sums scale with weights four and six, hence $\Delta(\Lambda)=1$. Multiplication by $\alpha=\phi(\sqrt{-d})$ preserves $\Lambda$. Its real determinant is $d$, giving $d$ points in its kernel on the torus. The algebraicity of $j(\Lambda)$ follows because this cyclic self-isogeny of prime degree gives $\Phi_d(j,j)=0$ for the classical integral modular polynomial. Its diagonal specialization is nonzero, since a generic complex lattice has only integer endomorphisms and their degrees are squares. Now $g_2^3=j/1728$ and $27g_3^2=g_2^3-1$, so both invariants are algebraic. [The exact arithmetic input](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean#L41-L60) · [Modular polynomial and cyclic isogenies](https://math.mit.edu/classes/18.783/2023/LectureNotes20.pdf) · [Uniformization and the invariant differential](https://math.mit.edu/classes/18.783/2023/LectureNotes15.pdf)

For oriented full periods $\omega_1,\omega_2$, put $A=\mathrm{Im}(\bar\omega_1\omega_2)>0$. This is the source's infimum of positive period parallelogram areas, since all such areas are positive integer multiples of $A$. Let $\sigma$ be the ordinary Weierstrass sigma function of $\Lambda$, normalized by $\sigma'(0)=1$. Its entire product has simple zeros precisely on $\Lambda$ and starts $z+O(z^5)$. Write $\eta_j$ for the zeta increment under a **full** period $\omega_j$. Legendre’s identity $\eta_1\omega_2-\eta_2\omega_1=2\pi i$ makes the two equations
$2a\omega_j=\pi\bar\omega_j/A-\eta_j$ consistent. The sigma translation formula now gives

$$
 F(z)=e^{az^2}\sigma(z),\qquad
 F(z+\omega)=\epsilon(\omega)
 \exp\!\left(\frac{\pi}{A}(z+\omega/2)\bar\omega\right)F(z),
$$

where $\epsilon(\omega)=1$ for $\omega\in2\Lambda$ and $-1$ otherwise. This is exactly `U1` for each period. The function is odd with derivative one. Any other candidate in `sgStar` vanishes at zero by oddness, and at each period by translation. Dividing it by $F$ gives an entire periodic function because the zeros of $F$ are simple. The quotient is constant by compactness, and differentiation at zero makes it one. This checks existence and uniqueness at the choice operator. [Exact signs, normalization and selection](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean#L234-L240) · [Weierstrass product and quasi-periods](https://dlmf.nist.gov/23.2)

## Pin the quadratic exponential by a finite divisor

Use coordinates $x=\wp_\Lambda(z),\ y=\wp'_\Lambda(z)$ on $y^2=4x^3-g_2x-g_3$ with differential $dx/y=dz$. The quotient $F(\alpha z)^2/F(z)^{2d}$ is elliptic because translating $z$ by $\omega$ cancels the two exponential multipliers because $\alpha\bar\alpha=d$, and the signs disappear on squaring. At zero it has a pole of order $2d-2$, and it has a double zero at each nonzero point of $\ker[\alpha]$. The function

$$
 \alpha^2\prod_{0\ne T\in\ker[\alpha]}(\wp_\Lambda(z)-x(T))
$$

has precisely that divisor and the same leading term at zero. Each pair $T,-T$ occurs twice in the product of $x$-coordinates. The quotient of the two elliptic functions is therefore the constant one. Since $\wp(z)=z^{-2}+O(z^2)$, comparing the next coefficients on the two sides yields

$$
 2a(\alpha^2-d)=-\sum_{0\ne T\in\ker[\alpha]}x(T),\qquad
 a=\frac1{4d}\sum_{0\ne T\in\ker[\alpha]}x(T).
$$

These torsion data are algebraic. The kernel lies in $E[d]$ since $[\alpha]^2=[-d]$. The quotient isogeny by these algebraic points is defined over $\overline{\mathbb Q}$. Its complex identification with the original elliptic curve is defined there too, as follows either from the changes of Weierstrass coordinates or from the finite automorphism group fixing the origin. On the fixed differential the composite multiplies by $\alpha$. Under a field embedding its derivative becomes $\rho(\alpha)$. On the conjugate torus an endomorphism is determined by its derivative on the universal cover, so the conjugate kernel is exactly the kernel of $[\rho(\alpha)]$. The sign choices $\rho(\alpha)=\pm\alpha$ give the same kernel. In particular the displayed trace belongs to any coefficient field containing $g_2,g_3,\alpha$ and is transported to the corresponding trace there. [Isogenies, kernels and quotient curves](https://math.mit.edu/classes/18.783/2025/LectureNotes5.pdf)

Uniformize the curve with invariants $\rho(g_2),\rho(g_3)$ and its specified differential. Its period lattice $\Lambda_\rho$ has these invariants and is uniquely recovered by integration of the differential. The release allows an arbitrary additive subgroup in `lamConj`. A nondiscrete subgroup contains infinitely many elements approaching zero, so the terms of *both* defining Eisenstein sums fail the term test and the totalized values vanish. A discrete cyclic subgroup $\omega\mathbb Z$ gives $g_2=4\pi^4/(3\omega^4)$ and $g_3=8\pi^6/(27\omega^6)$ by the even zeta sums. The zero subgroup also has discriminant zero. The classified discrete subgroups of $\mathbb C$ leave the period lattice as the only possibility at discriminant one. Thus the constructed receiving torus matches the chosen subgroup. [Lattice choice and coefficient operation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean#L123-L136) · [Weierstrass differential equation and invariants](https://dlmf.nist.gov/23.3)

For the all-orders step put $P=z^2\wp(z)$. In
$(zP'-2P)^2-4P^3+g_2z^4P+g_3z^6=0$ with $P(0)=1$, the multiplier of the new coefficient $p_n$ in degree $n>0$ is $-4(n+1)$. Each coefficient is therefore a rational polynomial in $g_2,g_3$. Twice integrating $-(\wp-z^{-2})$ gives $\log(\sigma/z)$ with zero constant and linear terms. Exponentiating gives every coefficient of $\sigma$. Together with the finite trace for $a$, this constructs the conjugated Taylor series as the Taylor series of the explicit entire function $e^{\rho(a)z^2}\sigma_{\Lambda_\rho}(z)$. Its derivative at zero is one. Compact convergence here comes from an entire receiving function whose parameters were derived on paper. [Classical sigma and zeta identities](https://dlmf.nist.gov/23.2)

## The half-period and torsion translations

For $mt\in\Lambda$, $T=[t]\ne0$, write $F_t=U_1(t)F$ using the same Gaussian multiplier as the source. Put $c_t=F_t(0)\ne0$. The ratio $H_t=F_t/F$ has a multiplier under a period $\omega$ equal to $\exp(\pi(t\bar\omega-\omega\bar t)/A)$, an $m$th root of unity. Therefore $H_t^m=c_t^m R_T$, where $R_T$ is the elliptic function with divisor $m[-T]-m[0]$ and leading coefficient one at the origin. The chord-and-tangent addition law constructs a rational function for this principal divisor over the coordinates of the torsion points. Its space up to scaling is one-dimensional, and the local parameter $-2x/y=z+O(z^2)$ fixes the algebraic leading coefficient. Translation by $T$ is algebraic. The product $\prod_{j=0}^{m-1}R_T(P+jT)$ has zero divisor and is a nonzero algebraic constant. On taking the product of $H_t(z+jt)$ the factors telescope to $\epsilon(mt)$. It follows that $c_t^{m^2}\prod_j R_T(P+jT)=\epsilon(mt)^m$. The scalar is algebraic. After transport and choice of a lift of the conjugate torsion point it can differ from its receiving counterpart only by a root of unity. Choosing the Laurent root with the specified leading coefficient then gives the conjugated translate as an entire function.

For the actual nonzero two-torsion point $t_0$ in `th0` the square determines the normalized function.

$$
   \operatorname{th0}(z)^2=F(z)^2\bigl(\wp(z)-x(T_0)\bigr),\qquad
   \operatorname{th0}(0)=1.
$$

The right side extends across the lattice. Its square root with constant one has unique Taylor coefficients. The number $x(T_0)$ is a root of $4X^3-g_2X-g_3$ and specifies its conjugate two-torsion point. The phase cancels in `th0` because the source divides by the translate’s value at zero. This proves transport over the explicit finite field generated by $g_2,g_3,\alpha,x(T_0)$, and after extending embeddings to that field. Whether all coefficients read by the higher-rank operation descend to its particular smaller field is an additional obligation. The “unkilled” condition gives $t_0\notin\Lambda$ because both displayed half-integers $(1\pm\sqrt{-d})/2$ preserve the ideal lattice, so a lattice point would violate that condition. [Half-period definition and nonvanishing condition](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GL3Theta.lean#L198-L204) · [Related classical work on algebraic reduced theta at torsion points](https://arxiv.org/abs/math/0610163)

## Exact degree-seven control

On $Y^2=X^3-35X-98$ with differential $dX/(2Y)$, put $C(X)=X^3+7X^2-21X-91$. Reducing the seventh division polynomial modulo $C$ gives zero. The cleared doubling formula also gives $C(x(2P))=0$ at any root of $C$. The cubic is irreducible by the rational-root test and its roots give three distinct pairs of points. Since $2$ has order three modulo $7$ up to the indicated sign pairs, the six points form the nonidentity part of one cyclic subgroup. Their sum of $x$-coordinates is $-14$. Vélu's formulas for the normalized quotient change the two short Weierstrass coefficients from $(A,B)$ to $(49A,-343B)$. These are $(\alpha^4 A,\alpha^6 B)$ for $\alpha^2=-7$. Scaling the quotient back gives an endomorphism with differential $\alpha$ and exactly this kernel. Thus the cubic Taylor coefficient is $-1/2$. Scaling the lattice to discriminant one scales this coefficient by the inverse square of the lattice scale. This is a small exact example of the period calculation, outside the release's asymptotic prime-window test. [Standard-library integer calculation](check_theta_paper_examples.py) · [Vélu’s formulas](https://math.mit.edu/classes/18.783/2025/LectureNotes5.pdf)

## The higher-rank boundary

For $K=\kappa\,\mathrm{kernel4}$, the required equation is $K(z_1,z_2,z_3,z_4)=\prod_i\theta(z_i)$. A nonzero solution has an anchor $a$ with $K(a,a,a,a)\ne0$. It must satisfy, for every quadruple,

$$
 K(z_1,z_2,z_3,z_4)\,K(a,a,a,a)^3
       = \prod_{i=1}^4 K(z_i,a,a,a).
$$

Conversely this identity constructs a factor. Take $c^4=K(a,a,a,a)$ and set $\theta(z)=K(z,a,a,a)/c^3$. The identity alone does not give its arithmetic normalization. The symmetric control $1+z_1z_2z_3z_4$ gives $2$ on the left and $1$ on the right at $a=0$ and all $z_i=1$. It shows what a factorization test must distinguish. The release also imposes self-duality, character agreement and commensurability on its finite intertwiner. The control is an abstract symmetric function. Checking those arithmetic hypotheses on the selected kernel is part of the open task. [The fourth tensor condition](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/KernelLattices/LateralTheory.lean#L23-L36) · [Hypotheses and finite intertwiner](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/ProductThetaMem.lean#L43-L70)

There is an independent all-orders check available *once that factorization is established*. Choose any nonzero coefficient $a_\beta$ of $\theta$. The coefficient of multidegrees $(\nu,\beta,\beta,\beta)$ in $K$ is $a_\nu a_\beta^3$, and that for $(\beta,\beta,\beta,\beta)$ is $a_\beta^4$. If $K$ has a receiving entire function with all coefficients transported, extract the coefficient in its last three variables and divide by $\rho(a_\beta)^3$. Cauchy's formula makes this slice entire in the first variable with the required coefficients. Quantitative norm control would also have to account for that divisor or use a different estimate. We have not independently evaluated the actual higher-rank intertwiner, the fourfold factorization at its selected data and the uniform bound used by `logThAt`. Those obligations remain open. [The norm and coefficient fields actually required](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TopPlaceLogTheta.lean#L49-L72) · [Audit disposition](2026-11-23-independent-theta-check.md)
