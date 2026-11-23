# An independent denominator check for all 34 CM class values

**23 November 2026.** In the [conductor-137 example](2026-11-23-toric-fourier.md) we can supply the missing arithmetic check without Lean. The constant coefficient of **each of the 34 class modular forms** is a 17-adic unit. After taking the 34 character sums, **every** constant coefficient is divisible by exactly one power of 17. The inverse transform really loses a factor at this cusp. Nevertheless all 34 normalized **values at the CM point**, and all their character sums, are integral at 17. A modular-form argument at every cusp gives bounds at the other primes too.

| Denominator of the normalized twelfth power | 2 | 3 | 7 | 11 | 137 | Every other prime |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Independent upper bound | 132 | 12 | 60 | 12 | 120 | 0 |
| Allowance in the release | 252 | 12 | 120 | 12 | 480 | 0 |

The first line gives upper bounds. The 17-adic valuations at the cusp are exact. The argument below proves integrality at the CM evaluation, without asserting its exact valuation.

## A modular form for each actual lattice

Use $F=\mathbb Q(\sqrt7)$, $E=F(\sqrt{-7})$, $\tau=(1+i\sqrt7)/2$, and $k=2s=10$. Write an element of $E$ as $a+b\tau$, $a,b\in F$. Both chosen CM embeddings send $\tau$ to the same point of the upper half-plane. For each conductor class $r$, let $\mathcal L_r\subset F^2$ be the coefficient pairs of the actual lattice $L_r$ from the preceding calculation. For complex $z$ in the upper half-plane define
$$
 E_{\mathcal L}(z)=\sum_{(a,b)\in(\mathcal L\setminus0)/O_F^\times}
                 \prod_{\sigma:F\hookrightarrow\mathbb R}
                    (\sigma(a)+\sigma(b)z)^{-k}.
$$
The summand is invariant under the indicated units because $k$ is even. At $z=\tau$ this is the class lattice series the release reads, before multiplying by its finite character. It is absolutely convergent for $k>2$ here. On each compact set of $z$, each real linear coordinate change from $\tau$ to $z$ is bounded above and below, so the convergence at $\tau$ also gives locally uniform convergence. [Released series and class sum](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L81-L103) · [Normalizing constant](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PairingDivisors/StatementH.lean#L44-L50)

The integer-ring index $[O_E:O_F[\tau]]=7$ follows from the discriminants of the product basis and $d_E=784$. Every $L_r$ lies in $O_E$ and contains $\mathfrak f O_E$, where $N\mathfrak f=137$. Hence
$$
 \mathfrak f O_F^2\subset\mathcal L_r\subset 7^{-1}O_F^2.
$$
The same inclusions hold after every integral determinant-one change of the two coordinates. In particular $\Gamma(959)$ preserves each $\mathcal L_r$, since $959=7\cdot137$. Changing the summation pairs in the series gives modular weight $2k=20$ on this group. Its translates by $\mathrm{SL}_2(\mathbb Z)$ have the identical description with a translated lattice. This lets us check **all** cusps at once.

Put
$$
 M_{\mathcal L}(z)=
 \frac{28^{(k-1)/2}((k-1)!)^2}{(2\pi i)^{2k}}E_{\mathcal L}(z).
$$
This is a diagonal restriction of a Hilbert Eisenstein series. The normalization for our lattice at a general cusp is derived next. [Bruinier, diagonal restriction and Fourier expansion of Hilbert Eisenstein series](https://people.mpim-bonn.mpg.de/zagier/files-restricted/doi/10.1007/978-3-540-74119-0/fulltext.pdf)

## Denominators of the Fourier coefficients

For a translated lattice set $I=\{a:(a,0)\in\mathcal L\}$. This is a fractional ideal containing $\mathfrak f$, so $137/N(I)=[I:\mathfrak f]$ is an integer. The terms with $b=0$ contribute $N(I)^{-k}\zeta_F(k)$ before normalization because $F$ has class number one. Using the functional equation of $\zeta_F$ in this real quadratic field gives the normalized constant
$$
 \frac{\zeta_F(1-k)}{4\cdot28^{k/2}N(I)^k}.
$$
Equivalently the functional equation here is $\zeta_F(1-k)=4\cdot28^{k-1/2}((k-1)!/(2\pi)^k)^2\zeta_F(k)$. At $k=10$, $\zeta_F(1-k)/4=52955730841/66$.

For $b\ne0$ choose one $b$ in each unit orbit of its projection. The $a$ in that fiber form one coset $a_0+I$. Apply Poisson summation to this coset in $\mathbb R^2$. Its covolume is $\sqrt{28}\,N(I)$ and its dual frequencies are $\nu\in\mathfrak d_F^{-1} I^{-1}$. In one real coordinate, the Fourier integral of $(x+\sigma(b)z)^{-k}$ is zero unless the frequency has the sign of $\sigma(b)$. For a surviving frequency it is an exponential times $(2\pi i)^k \sigma(\nu)^{k-1}/(k-1)!$ up to sign, by the residue of the pole of order $k$. The zero frequency vanishes. Multiplying the two coordinates gives exponent $\operatorname{Tr}_{F/\mathbb Q}(b\nu)>0$ and root of unity $\xi=\exp(2\pi i\operatorname{Tr}(a_0\nu))$. The normalized contribution is
$$
 \pm \xi\,\frac{28^{(k-2)/2}N_{F/\mathbb Q}(\nu)^{k-1}}{N(I)}
 =\pm \xi\,\frac{t^{k-1}}{28^{k/2}N(I)^k},
 \qquad t=N\big((\nu)\mathfrak d_F I\big)\in\mathbb Z_{>0}.
$$
The signs absorb the sign of the field norm. This formula uses no division by the number of ring classes.

Each coefficient is a finite sum. For fixed positive trace, $b\nu$ is totally positive in a fixed fractional ideal, hence takes only finitely many values. For each value the possible principal ideals $(b)$ are divisors after denominators are cleared, and $b$ was taken modulo all real units. These counts and $|N(\nu)|$ grow at most polynomially in the trace. The two real components of $b\nu$ are bounded by its trace, the possible ideal norms of the cleared divisors are bounded by a constant times its square, and $|N(b)|$ is bounded below on the fixed fractional ideal. This also justifies the Fourier rearrangement. All phases are roots of unity of bounded order since the lattices and their duals have fixed denominators.

It follows that
$$
 D_\ast=66\cdot28^5\cdot137^{10}
$$
clears all the Fourier coefficients of $M_{\mathcal L}$ at every cusp. At the original cusp $I=O_F$ in the identity class and $I=\mathfrak f$ in each of the other 33 selected classes. Indeed a real $a$ has equal residues at the split pair. It meets the relation $a\equiv r a\bmod\mathfrak f$ for $r\ne1$ precisely when it lies in $\mathfrak f$.

Writing $b_0=52955730841/(66\cdot28^5)$, the 34 constants are $b_0$ once and $b_0/137^{10}$ 33 times. Their character transforms are $b_0(1+33/137^{10})$ once and $b_0(1-1/137^{10})$ 33 times, up to permutation from the base character. Both have valuation exactly one at 17. This follows by expanding $137^{10}=(1+8\cdot17)^{10}$ modulo $17^2$. The original constants all have valuation zero. [Exact checks of the Fourier transform and the denominators](check_toric_fourier.py)

## From every cusp to the CM point

Use the classical discriminant $\Delta(z)=q_z\prod_{j\ge1}(1-q_z^j)^{24}$ with $q_z=e^{2\pi iz}$. The lattice discriminant for the basis $1,z$ is $(2\pi)^{12}\Delta(z)$, which follows from the standard $g_2,g_3$ expansions and $E_4^3-E_6^2=1728\Delta$. Consider the weight-zero function
$$
 B_{\mathcal L}(z)=\frac{(D_\ast M_{\mathcal L}(z))^{12}}{\Delta(z)^{20}} .
$$
Its value at $\tau$ is $D_\ast^{12}$ times the released normalized twelfth power for that lattice. It has no pole in the upper half-plane. Its Laurent expansions and those of its translates have algebraic-integer coefficients, since $\Delta^{-20}$ has integral Laurent expansion.

Take the monic polynomial with roots $B_{\mathcal L}(\gamma z)$ over the finitely many cosets of $\Gamma(959)$ in $\mathrm{SL}_2(\mathbb Z)$. Each coefficient is a full-level modular function with poles only at the cusp and an integral Laurent expansion. Translation invariance leaves only integer exponents. Subtracting its leading coefficient times an appropriate power of $j=q_z^{-1}+744+\cdots$ successively removes the entire pole. What remains is constant by compactness of the full-level modular curve. Thus each coefficient belongs to $\overline{\mathbb Z}[j]$. At $j(\tau)=-3375$ the polynomial is monic over algebraic integers, so $B_{\mathcal L}(\tau)$ is an algebraic integer. This proves the first row of the denominator table. [CM discriminant $-7$ and its $j$-invariant](https://www.lmfdb.org/EllipticCurve/Q/49/a/4) · [Normalization being tested](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L105-L111)

With one common choice of $\Omega^{12}=\Delta(O_{K_d})$, each lattice value before taking the twelfth power becomes an algebraic integer after multiplication by $D_\ast$. Summing those values against character roots of unity preserves integrality. In particular, the actual normalized CM values satisfy **all** the 17-adic finite-difference congruences in the [Fourier calculation](2026-11-23-toric-fourier.md). This proves the integrality assertion for these inputs without calculating their exact valuations or using the proof's Taylor-coefficient theorem.

## Scope and unresolved step

The same argument covers this field for every $s\ge2$ with zero derivative weights. Replace $\mathfrak f$ by the conductor $\mathfrak c=\mathfrak f\prod_{\mathfrak q\in Q}\mathfrak q$, use unit ideles as representatives since $E$ has class number one, and take
$$
 D_k=\operatorname{den}\big(\zeta_F(1-k)/4\big)\,28^{k/2}(N\mathfrak c)^k,\qquad k=2s .
$$
Here $\operatorname{den}$ is the positive reduced denominator. At a tested prime away from $Q$, the conductor exponent satisfies $v_\ell(N\mathfrak f)\le2a_0(\mathfrak f,\ell)$ because the real quadratic conductor is supported at completely split rational primes. The displayed bound fits the release's zero-derivative allowance at conductor primes, at discriminant primes and elsewhere. The passage to an arbitrary idele representative uses a principal multiple and an order unit; the infinity phase and the idele norm cancel the change of the lattice series. [Representative invariance](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ToricDenominatorOfZetaDenominators.lean#L25-L37) · [Local quantifiers and the condition on $Q$](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/VpBounds.lean#L65-L82)

For nonzero derivative weights, the summand contains complex-conjugate powers. The holomorphic modular function above no longer gives their integrality directly. That is the next test of the coordinate and period normalization. The limiting weight $s=1$ also needs a continuation argument. [Additional derivative and period factors](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/Divisors/JetAnalytic.lean#L239-L245) · [Their use at a prime outside the conductor and discriminant](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeValueIntegralityUnramifiedOfJetIntegralit.lean#L270-L313)
