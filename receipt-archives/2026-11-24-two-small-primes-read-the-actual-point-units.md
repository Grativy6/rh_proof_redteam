# Two small primes read the actual point units

**24 November 2026.** In the original conductor-256 test, let $v_R,v_{R_0}$ be the two uniquely specified ordinary unit classes of the degree-577 point field $E$. At 2309 and 3463 the old tests comparing conjugates give zero difference on every pair. We computed the common value at each prime. In the integral coordinate $\theta$ of the earlier receipt, the following tests require only arithmetic in the prime field.

| Prime $q$ | Unique degree-one root of $\theta$ | Test | Required value for $v_R$ | Required value for $v_{R_0}$ |
| ---: | ---: | --- | ---: | ---: |
| 2309 | 73 | Fourth power modulo 2309 | 2103 | 2232 |
| 3463 | 3453 | Sixth power modulo 3463 | 2849 | 1024 |

The exponents of these values relative to the chosen primitive 577th roots give the rows $(426,35)$ and $(97,522)$. Their determinant is **294 modulo 577**. On the two-dimensional space of point units killed by $(\tau-1)^2$, a class is zero exactly when it reads one in both power tests. A candidate for either named class can therefore be rejected before a large-field norm solve. Use a unit representative at the indicated place when applying the test. Membership in that two-dimensional space still requires its own evidence. [The unit space and the original three-prime exclusion](2026-11-24-two-units-in-the-degree-577-point-field.md#which-two-units-to-find)

## What the older measurements leave undetermined

Write $p=577$, $T=\mathbb Q(\zeta_f)$, $f=256p$, $M=\mathbb Q^{\ker z}$, $L=L_y$, $\chi=z^{-1}$ and $\lambda=\omega z$. The real affine group acts by $\delta_a\tau\delta_a^{-1}=\tau^a$ with $\chi(\delta_a)=a$. For a base power class $b$ in the span of $e_-,R$, the point unit is characterized by $b\,\tau v_b/v_b\in L^{\times p}$. The proof also gives $[v_b]=\sum_{a\ne0}a\,\tau^a[X]$, where $X$ is its normalized real $S$-unit norm preimage and $S$ lies above 12407809. Use additive notation for power classes. We have $R_0=Re_-^{95}$. [Point-unit norm equation](2026-11-24-two-units-in-the-degree-577-point-field.md#a-norm-equation-becomes-one-comparison-of-conjugates)

Take a prime $q\equiv1\bmod p$, with $z(q)\ne1$ and $q\nmid f$. Its affine Frobenius has one fixed point. At $q$ the class $b$ is a local $p$th power in $T$ after removing its $p$-multiple valuation. Indeed Frobenius acts on the residue power quotient as $q=1\bmod p$ and on $b$ as $\chi(q)\ne1$. Thus the point-unit comparison says all the affine places have the same power class after passing to $T$. The value at the fixed point can be nontrivial in $\mathbb F_q^\times/\mathbb F_q^{\times p}$. Write $e_q(b)$ for its discrete exponent modulo $p$ relative to the least primitive root $g_q$ of $\mathbb F_q$. The displayed gate uses $g_q^{(q-1)e_q(b)/p}$.

## A Jacobi carry gives the first common value

Let $U_q$ be the degree-$p$ field in $\mathbb Q(\zeta_q)$, $T'=TU_q$, and $\rho_q$ its character normalized by $\rho_q(g_q)=1$. Put $w(a)=\lambda(a)^{-1}$ modulo $p$ on units of $f$. Define
$$
 d_q=1-\lambda(q)^{-1},\qquad
 K_q=\sum_{a\in(\mathbb Z/fq)^\times}
   \left\lfloor\frac{2a}{fq}\right\rfloor\,w(a\bmod f)\log_{g_q}(a\bmod q)
 \quad\bmod p ,
$$
using least positive representatives. Then
$$ e_q(R_0)=-\frac{231K_q}{376d_q}. \tag{1} $$

Here is the construction and a sign check. Take an auxiliary prime $r\equiv1\bmod fq$ with nonzero unramified dual reading $u(r)$. The first split comparison prime in each numerical run below is such a prime. The earlier calculation identified $u(r)=376\exp_r(R_0)$ and the lower Kummer character of the conductor-$f$ Jacobi radicand $\beta_r$ as $(u(r)/231)y$, with $y(\tau)=1$. Throughout, arithmetic Frobenius sends a root-of-unity residue to its residue-field power. [Dual characters and their normalization](2026-11-24-two-independent-obstruction-primes.md#a-basis-of-the-dual-group) · [Identification by the explicit circular targets](2026-11-24-two-opposite-ideal-class-readings-at-577.md#the-second-divided-ideal-reads-minus-two)

Form the Jacobi sum of conductor $fq$ at $r$ with the two inverse characters, norm it to $T'$, then apply the integral projector with weights $w$ through the $f$-part. Call the result $A'$. For $\sigma\in\operatorname{Gal}(T'/T)$ with $\rho_q(\sigma)=1$ we have $[N_\sigma A']=d_q[\beta_r]$. To verify the distribution, sum the upper-half divisor over the $q$ lifts of an old index $i$. This gives $(q-1)/2+\lfloor2i/f\rfloor$. The excluded lift divisible by $q$ subtracts the old carry at $q^{-1}i$. Thus the norm of the unprojected Jacobi sum and $r^{(q-1)/2}J_f/(\sigma_{q^{-1}}J_f)$ have the same divisor and absolute values at every embedding. Their ratio is a root of unity. The $\lambda$-projection kills the rational factor and the possible root-of-unity power class, since $\lambda$ differs from $\omega$ at 2. The original Jacobi divisor calculation applies equally at conductor $fq$. [Carry and divisor proof](2026-11-24-the-577-class-on-paper.md#the-element-and-its-divisor)

Set $D=\sum_{j=0}^{p-1}j\sigma^j$ and $B'=(A')^D$. At the chosen split prime its valuation is $K_q\bmod p$ by the same upper-half carry, now weighted by the $q$ index. Take $H=T'(\sqrt[p]{\beta_r},\sqrt[p]{B'})$. Its quotient over $T$ by the last Kummer direction is $LT'$. The two Kummer directions over $T'$ are independent since $(\sigma-1)[B']=-d_q[\beta_r]\ne0$. In the central coordinate given by $B'$,
$$[\sigma,\tau]=\kappa,\qquad \kappa=d_q\,u(r)/231.$$
Indeed the value of the Kummer character of $B'$ on $\sigma h\sigma^{-1}$ is that for $\sigma^{-1}B'$ on $h$. All local groups over $T$ are abelian, since the quotient $LT'/T$ is locally cyclic. The $y$ extension splits at $p$ and $q$, and elsewhere the quotient is unramified. The full central group has exponent $p$. The two Kummer generators over $T'$ have order $p$. The $p$th power of a lift of $\sigma$ would belong to the central line, and would be fixed by the tame complement since the $p$th-power map is additive in this class-two group. That line has the nontrivial complement character $\chi$. This also shows that changing $b$ by a $p$th power leaves each local central Artin symbol unchanged.

For a virtual unit $b$ as above, multiply its local Artin symbols in $H/T$, which are central. To compute their sum using the global $X$, carry each symbol over $\tau^t w_0$ back to the base place by $\tau^{-t}$. The global product over $LT$ is one by ordinary abelian reciprocity there. Inverse conjugation adds $\kappa t\,\rho_q(\operatorname{rec} X_t)$, with $X_t$ evaluated via $\tau^{-t}$. Only the places over $q$ can contribute to this weighted sum. The character $\rho_q$ is unramified elsewhere, $X$ is a unit away from $S$, and the $S$-primes are inert for $y$. At $q$ choose the place whose affine Frobenius fixes the origin. The formula for $v_b$ shows that its local character is $-\sum_t t\rho_q(\operatorname{rec} X_t)$. A rational unit under arithmetic-normalized reciprocity acts on $\zeta_q$ by the inverse of its residue. The local character on $v_b$ is consequently $-[T_{\mathfrak q}:\mathbb Q_q]e_q(b)$. Summing gives the central product **$[T:\mathbb Q]\kappa e_q(b)$**. [Local and global reciprocity, Milne, *Class Field Theory*, I §3 and VII](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

Read the same product directly on $R_0$. At $p$ and $q$ it is a local $p$th power. At all remaining primes apart from $r$ the extension is unramified and its valuations are divisible by $p$. At the chosen $r$ the tame Hilbert symbol on the unit representative contributes $-K_q\exp_r(R_0)$. Every conjugate gives the same scalar because the valuation and the residue exponent transform by reciprocal characters. Dividing both evaluations by $[T:\mathbb Q]\kappa$ proves (1). For $q=2309$ the explicit choice $r=590386990849$ has $\exp_r(R_0)=308$, $u(r)=408$, $\kappa=305$ and $K_q/\kappa=13$. Thus the reading is $-13\cdot308=35\bmod577$.

## A second direction comes from a circular norm

Use the positive circular unit $C_-=e_-^p$ at conductor $f$ with its original weights modulo $p^2$. At conductor $fq$ take the same weighted product of $1-\zeta_{fq}^a$ over the indices with $\rho_q(a)=0$. This gives a positive unit $W_q\in MU_q$. With $\zeta_{fq}^q=\zeta_f$,
$$N_{MU_q/M} W_q=C_-/\sigma_{q^{-1}}C_-=(e_-/\sigma_{q^{-1}}e_-)^p.$$
This identity follows by multiplying the $q$ lifts of each old cyclotomic factor and dividing out the single excluded lift. Write $e=e_-/\sigma_{q^{-1}}e_-$. Choose $w$ with $\sigma w/w=W_q/e$ by Hilbert 90, and put $R_q=Nw$. Its power class on $MU_q$ is $(\sigma-1)^{p-2}[W_q]$, as in the old wild-layer calculation. Real-root uniqueness gives descent of the power class, and changing $w$ multiplies its norm by a $p$th power. Its divisor is divisible by $p$ away from $q$ because $\operatorname{div}w$ is invariant. At $q$ the nontrivial $\chi$ on the stabilizer forces divisibility as well. Thus $[R_q]$ is in the same two-dimensional base space as $e_-,R$. [Wild-layer descent and derivative formula](2026-11-24-two-opposite-ideal-class-readings-at-577.md#recover-a-second-global-target-in-the-abelian-field)

In the central product now use $w$ over $T'$ and transport its symbols by $\sigma^{-t}$. The character being transported is the everywhere-unramified $y$. At every split place the valuations of $w$ on its orbit are equal. Their first moment is zero modulo $p$ since $\sum_{t=0}^{p-1}t=0\bmod p$. At nonsplit places there is only one component. This proves $e_q(R_q)=0$. If $[R_q]=a[e_-]+b[R]$, the two equations for the remaining readings are therefore
$$ a e_q(e_-)+b e_q(R)=0,\qquad 95e_q(e_-)+e_q(R)=e_q(R_0). $$

| $q$ | $d_q$ | $K_q$ | $(a,b)$ | $e_q(e_-)$ | $e_q(R)$ | $e_q(R_0)$ |
| ---: | ---: | ---: | --- | ---: | ---: | ---: |
| 2309 | 423 | 503 | (518,267) | 500 | 426 | 35 |
| 3463 | 216 | 461 | (13,325) | 460 | 97 | 522 |
| 20773 | 481 | 359 | (485,512) | 73 | 234 | 245 |

For each $q$ two split primes determine $(a,b)$ and a third checks it. The third row uses the same original conductor-256 character throughout. It supplies the additional condition needed to keep 577 completely split in the [base-change calculation](2026-11-24-a-strict-class-gains-one-digit-after-base-change.md). The split-prime data, including primitive generators, are in the replay.

## Checks against the old work

At the old principal cyclotomic layer the Euler factor is one. Directly rerunning its upper-half sum gives carry $540=-37\bmod577$. Formula (1) gives $-231\cdot540/376=190$. The circular norm direction there is $R$ itself and reads zero. This reproduces the independently obtained origin components $0,190$ for the two point units, including the sign. The integral commutator also gives $413/8=268$, the signed norm coefficient computed previously. [Point-field local readings](2026-11-24-two-units-in-the-degree-577-point-field.md#every-local-component-above-577) · [Integral class check](2026-11-24-two-opposite-ideal-class-readings-at-577.md#feed-these-results-into-the-original-test)

For the new primes the carry was computed both by summing first over the $f$ part and by summing first over the $q$ part. Jacobi carries for multipliers 3, 5 and 7 check the normalization against the doubling carry. In the circular computation each norm distribution is checked before weighting, in each of the 576 tame weight groups. The weighted derivative is also evaluated as one product. A separate PARI calculation of the conductor-2309 derivative at 590386990849 gave 457 by evaluating a single polynomial modulo $X^{2309}-1$.

For the degree-one roots of $\theta=\sum_e s_e$, evaluate the original Jacobi histogram in the residue field containing the 256th roots. With $s^p=\beta$, $s_e=c_e s^e$ as in the point-coordinate calculation, the fixed affine origin satisfies $s^{q-e}=c_e$ for $e=\lambda(q)$. Since $p\nmid q-e$, Bézout recovers this root. Both small primes give 577 distinct reductions of the conjugates of $\theta$ and a single rational one. The degree-one root at 20773 is 9093. The roots 73 and 3453 were also recovered using different irreducible factors of the 256th cyclotomic polynomial. [Integral Jacobi coordinates](2026-11-24-the-576-primes-of-the-two-norm-targets.md#an-integral-coordinate-which-labels-the-coefficient-places)

## Reproduce

Run `python -B receipt-archives/boundary-577/central_unit_residues.py` with NumPy. To rebuild the nine large-prime comparison rows, compile `tame_circular_norms.cpp` with `g++ -O3 -std=c++17`, then pass the executable to the Python script with `--binary`. Each row is also available by calling the executable with $q$ and its split prime $r$. [Residue calculations](boundary-577/central_unit_residues.py) · [Circular products](boundary-577/tame_circular_norms.cpp)

## Unresolved

These are genuine point-unit power residues at degree-one primes. They give [two diagonal tests on the marked deformation](2026-11-24-two-tame-inertia-tests-on-the-marked-point.md). The numerical values of the two ordinary quadratic forms on the odd tangents still require a global calculation.
