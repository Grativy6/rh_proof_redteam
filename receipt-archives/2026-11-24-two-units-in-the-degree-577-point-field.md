# Two ordinary units in the degree-577 point field

**24 November 2026.** The two real norm problems at the original input can be reduced to **two unique classes of ordinary units in a field of degree 577**. The original real affine field has degree 332352. We determine the local power classes of both point-field units above 577, distinguish them at three more rational primes, and rule out every product of 576 simple linear factors as a way to obtain a nonzero combination of them. The ordinary units themselves still need explicit representatives.

## A norm equation becomes one comparison of conjugates

Keep $p=577$, $k=\mathbb F_p$, the abelian field $M$, the affine field $L=L_y$, and $P=\langle\tau\rangle=\operatorname{Gal}(L/M)$. Put $E=L^\Delta$, the real degree-$p$ field of the stabilizer of the marked origin. For the rest of this receipt write $\chi=z^{-1}$. If $\delta_a\in\Delta$ has $\chi(\delta_a)=a$, then $\delta_a\tau\delta_a^{-1}=\tau^a$. Write brackets for classes modulo $p$th powers, using additive notation when applying group-ring operators. [Fields and class groups](2026-11-24-the-affine-resolvent-and-its-class-groups.md#all-finite-layers-and-the-degree-577-field)

For $b=R$ or $R_0$ there is a unique class $[v_b]\in\mathcal O_E^\times/\mathcal O_E^{\times p}$ such that
$$ b\,\frac{\tau v_b}{v_b}\ \in L^{\times p}. \tag{1} $$
To see existence, start with any normalized real $S$-unit $X$ for $b$. Its class has weight $\chi$ and $[N_{L/M}X]=[b]$. Let $v=N_{L/E}(\tau X)$. In $L^\times/L^{\times p}$ this gives
$$ [v]=V[X],\qquad V=\sum_{a\ne0}a\,\tau^a,\qquad
 (\tau-1)V=-\sum_{a\in k}\tau^a . $$
The last identity follows by shifting the coefficient index, including the wrap from $p-1$ to zero. It proves (1). The only possible support of $v$ is the unique prime $(12407809)$ in $E$ over the support prime. Its valuation is the sum of the 576 valuations of $X$ and hence is divisible by $p$. Dividing by the corresponding power of the rational prime makes $v$ an ordinary unit with the same class. [All 576 valuations](2026-11-24-the-576-primes-of-the-two-norm-targets.md#the-input-fixes-every-valuation-at-the-allowed-prime)

For uniqueness, the ratio of two unit solutions gives a class fixed by both $P$ and $\Delta$. A power class invariant under a Galois group of these real fields descends. Indeed if $g(v)/v=c_g^p$, the $p$th root is unique and the $c_g$ form a Hilbert 90 cocycle. Dividing $v$ by a global $p$th power leaves an invariant scalar. Here it is rational. All finite ramification indices of $L/\mathbb Q$ are prime to $p$, since $L/M$ is unramified and $[M:\mathbb Q]=576$. A rational scalar representing an ordinary unit class therefore has all valuations divisible by $p$ and is itself a rational $p$th power. Its remaining real root in $L$ is fixed by $\Delta$ and hence lies in $E$.

Conversely, for any ordinary unit representative satisfying (1), take the unique real root
$$ d_b=\left(b\,\tau v_b/v_b\right)^{1/p}\in L. $$
Multiplying the $p$ translates telescopes, giving $N_{L/M}d_b=b$ **exactly**. Its divisor is the extension of $J_b=\operatorname{div}(b)/p$. In particular $J_R=J_{R_0}$ since $R_0/R=e_-^{95}$ is a unit. The same base scalar clears both divisors away from the support prime. Indeed $[J_b]$ has order dividing $p$ and reading $-2$ on $y$. A power of the chosen base prime with exponent $269\bmod577$ and divisible by the prime-to-$p$ part of its class order represents $[J_b]$. After multiplying both roots by the corresponding base scalar, project to weight $\chi$. The lower and diagonal readings follow from the signed norm formula. The upper correction is described below. This leaves a principalization in the abelian field $M$ and a power extraction in the explicitly presented $L$. [Original two target classes](2026-11-24-two-opposite-ideal-class-readings-at-577.md#feed-these-results-into-the-original-test)

## Which two units to find

Let $\mathcal E=\mathcal O_L^\times/\mathcal O_L^{\times p}$ and $D=\log\tau$ in $k[P]$. The truncated logarithm defines this operator since $(\tau-1)^p=0$. Its powers have the same kernels as the corresponding powers of $\tau-1$. Conjugation by $\delta_a$ takes $D$ to $aD$.

The unit norm from $L$ onto $M$ is surjective even before reduction modulo powers. A base unit is a local norm everywhere and hence a global element norm from the unramified cyclic extension. The divisor of a field preimage is $(\tau-1)I$. Raising to the class number of $L$ and removing a principal conjugate ratio gives a unit preimage for that power. The base unit itself has norm its $p$th power. Since the class number is prime to $p$, Bézout combines the two into an actual unit preimage.

It follows that $D^{p-1}\mathcal E$ is the ordinary base-unit space of dimension 575. Here $D^{p-1}=(\tau-1)^{p-1}=N_P$ in $k[P]$, and base power classes inject by real-root uniqueness. The kernel of $D$ is the space of base power classes whose divisors are multiples of $p$. Descent follows by the same Hilbert 90 argument. Conversely the divided ideal of any such base class principalizes in $L$, since $\operatorname{Cl}(L)[p]=0$, giving an ordinary unit class there. The base-unit rank and $\operatorname{Cl}(M)[p]=k(\chi)$ give kernel dimension **576**.

Consequently the Jordan decomposition of $\mathcal E$ has **575 blocks of length 577 and one block of length 576**. The rank of $D^{p-1}$ counts full blocks, the kernel counts all blocks, and Dirichlet's unit rank $332351$ gives the remaining length. The bottom characters of the full blocks are precisely the nontrivial characters of $\Delta$, once each, by the real base-unit theorem. The remaining bottom line has character $\chi$ from the divided ideal. One may choose homogeneous chains by the complement idempotents, lifting a basis of each successive terminal layer. Moving one step down a chain multiplies its character by $\chi$.

The ordinary units of $E$ modulo powers identify with $\mathcal E^\Delta$ by extension and norm of degree 576. A full block with bottom $\chi^j$ contributes one $\Delta$-fixed direction, of length $j+1$ for $1\le j\le575$. The exceptional block contributes another of length two. Thus there are **exactly two independent unit classes in $E$ killed by $D^2$**, no invariant ordinary-unit class of length one, and one further direction at each length 3 through 576. Equation (1) puts both $v_R,v_{R_0}$ in that first two-dimensional subspace. Their images $[R],[R_0]$ are independent, so they exhaust it.

The opposite end of this same filtration supplies the upper correction. The known norm lift $X_+$ of the base unit $e_+$ has weight $\chi^{-1}$. For $v_+=N_{L/E}(\tau X_+)$, expansion of $\tau^a=\exp(aD)$ in $k[P]$ gives $[v_+]=\sum_{a\ne0}a^{-1}\tau^a[X_+]=-D[X_+]$. Hence $D^{575}[v_+]=-[e_+]$. The point-field quotient on which this last power is nonzero has dimension one. Any two representatives of this normalized quotient differ by a point unit in $D^2\mathcal E$, by their positions in the chains above. Applying $D$ once more kills the difference under every local measurement into the even space of translated quadratics. In particular $-D[v_+]$ gives the same correction row $(0,0,142)$ as $D^2[X_+]$. Thus this correction also admits a search among ordinary units of $E$. [Known upper normalization](2026-11-24-two-real-unit-norm-targets-at-577.md#what-is-still-needed-upstairs)

## Every local component above 577

At the coefficient place put $v_t=\tau^{-t}v$ evaluated at the chosen completion. Relation (1) gives $[v_t]=[v_0]+t[b]$ locally. At the origin $v_0$ lies in the degree-one completion $\mathbb Q_p$, so only its rational principal-unit digit remains. From $V[X]$ that digit is $-\sum_t t d_t=\Lambda_0(X)/8$, with the same orientation as the [affine coordinate](2026-11-24-the-576-primes-of-the-two-norm-targets.md#correct-local-readings-on-the-wrong-global-elements). Thus the actual profiles at all 577 labels, grouped into the nine completions of $E$, are
$$
[(v_R)_t]=[u_-^{488t}],\qquad [(v_{R_0})_t]=[(1+577)^{190}].
$$
The first varies linearly from a trivial origin. The second is constant across the entire affine line, even though it represents a nontrivial global unit class. Complex multiplication, trace equality and the second-order lift are unnecessary for this deduction.

## Independent prime tests on the point field

An integral absolute generator of $E$ is $\theta=\sum_{e\in\operatorname{im}\lambda}s_e$, with the 64 Jacobi roots defined in the [coordinate construction](2026-11-24-the-576-primes-of-the-two-norm-targets.md#an-integral-coordinate-which-labels-the-coefficient-places). The tame complement permutes the summands. Over the closure containing $\xi$ these are distinct nonconstant basis powers of $s$ with nonzero coefficients, so the translation group does not fix their sum. This proves $\mathbb Q(\theta)=E$.

Choose rational primes $q\equiv-1\bmod577^2$ with $q\equiv127$ or $129\bmod256$. Their $z$-value is $-1$ and their $\lambda=\omega z$ value is one. Frobenius on the point field fixes one origin and pairs all other labels. Choose the place fixing the marked origin, which is possible by translation without changing the cyclotomic residue embedding. In $\mathbb F_{q^2}$ use the primitive $256p^2$th root supplied by the generator $g$ below, and measure powers in $\mu_p$ relative to $g^{(q^2-1)/p}$. At the fixed point a unit from $E$ reduces to $\mathbb F_q^\times$, whose exponent is prime to $p$. Therefore (1) forces the power-residue exponent at label $t$ to be **$t$ times the exponent of $b$**, including zero at the origin.

| $q$ | $g$ in $\mathbb F_{q^2}$ | $\exp(e_-)$ | $\exp(R)$ | $\exp(R_0)$ |
| ---: | --- | ---: | ---: | ---: |
| 1406957953 | $5+\sqrt5$ | 282 | 528 | 199 |
| 1492187777 | $3+\sqrt3$ | 94 | 301 | 576 |
| 2088130687 | $1+\sqrt3$ | 160 | 11 | 209 |

The first two slope vectors have determinant **158 modulo 577**. For a virtual unit evaluated at a prime, take a unit representative of its power class after removing its $p$-multiple valuation. This preserves the power-residue reading. The circular products in this calculation use the actual base units and all 577 wild translates. Their product returns the base circular unit before taking the character, and the norm-one quotient $\bar c/c$ gives a second check of the weighted derivative exponent. At each prime we also evaluated all 577 genuine conjugates of $\theta$ from the original Jacobi histogram. They are distinct, with $\theta_{-t}=\theta_t^q$. For example at the first prime the fixed root is 994154191 and the root with label 1 is $316091105+98163880\sqrt5$. These are necessary measurements for the unique classes proved above. Explicit generators of those classes have yet to be recovered from the measurements.

## A search among products with rational shifts

We tested all multiplicative combinations of the elements $\theta-a$ for $0\le a\le575$, allowing arbitrary rational factors and $p$th powers. At each prime take $t=1,\ldots,288$, one representative of each two-cycle. The matrix entry in column $a$ is the power-residue exponent of $\theta_t-a$. The first two primes give a square $576\times576$ matrix of determinant **234 modulo 577**. They force one candidate exponent vector for each desired unit class. Rational factors have zero reading here after removing rational $p$th powers to clear valuations. All the tested factors are units at the selected nonrational roots.

At the third prime, subtract the required readings from the candidates' readings. Already at $t=1,2$ the two error columns give
$$\begin{pmatrix}323&147\\379&548\end{pmatrix},\qquad \det=121\bmod577.$$
Thus no nonzero combination of the two target classes belongs to this entire subgroup modulo powers. This excludes all exponent vectors for these shifts. Other point-field units remain candidates.

## Reproduce

Run `python -B receipt-archives/boundary-577/point_unit_norms.py` with NumPy. A separate PARI/GP calculation checked the square determinant, both columns of the held-out error, and nine individual residue symbols using the conjugate quotient. The replay constructs the three quadratic residue fields, checks primality and generator orders, evaluates the circular and Jacobi data, solves the first square system, and tests it at the third prime. It also checks modulo $p^2$ the Gauss-operator identity $WV=p-N_P$ for $V=\sum[a]\tau^a$, $W=\sum[a]^{-1}\tau^{-a}$ and Teichmüller brackets. At a nonzero group index its coefficient is the sum of the nontrivial multiplicative residues with 1 omitted, giving $-1$. At zero it is $p-1$. [Exact replay](boundary-577/point_unit_norms.py)

## Unresolved

The search now has a specified degree-577 field, a two-dimensional target inside its ordinary units, local readings and three independently chosen prime tests. Actual representatives satisfying (1) would give the real norm preimages after the indicated base and upper corrections. The four cyclic norm fields still require their own ordinary ideal-class readings to decide the trace cube. A failure of the released domain assertion has not been established. [Cyclic calculation and its downstream scope](2026-11-24-cyclic-norm-equations-and-the-missing-divisors.md)
