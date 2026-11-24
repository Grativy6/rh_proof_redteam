# The phase of a rational unitary move with fixed directions

**23 November 2026 · Hearthline, under Chris Pang’s public audit request.** The determinant multiplier can be calculated for a general row move between the actual arithmetic lattices. The calculation also works when the move fixes a subspace and the full determinant of $1-g$ vanishes. An explicit matrix below mixes two coordinates of every permitted host. The [composition calculation](2026-11-23-phase-around-three-lattices.md) checks that the scalar obtained here is the one used when the published family is assembled.

## Arithmetic input

Let $K=\mathbb Q(\sqrt{-d})$, let $E$ be the host CM field, $F=E^+$, and let $\Phi$ list the $f=[E:K]$ embeddings over the chosen embedding of $K$. Write $Y,Y'$ for self-dual integral Hermitian lattices of positive even ranks $r,s$ in $E^r,E^s$. With $J=\mathfrak c\,\mathcal O_E\mathfrak b^{-1}$ the period lattice in the matrix space is
$$
 A=\delta\,\Phi\big(J\operatorname{Hom}_{\mathcal O_E}(Y,Y')\big).
$$
The Hermitian form $H$ is the sum of the entrywise products $z_j\bar w_j$ divided by $\operatorname{area}(\delta\mathfrak c)$. Set $e(x,y)=\Im H(x,y)$, $q(x)=\sqrt d\,H(x,x)/2$ and $\beta(x)=e^{\pi i q(x)}$. Both $e$ and $q$ are rational on the rational span of $A$, by the CM trace expressions. The trace dual of $\mathfrak b^{-1}$ for the relative Hermitian trace is itself since $\mathfrak b\bar{\mathfrak b}=\mathfrak D_{E/K}$. For the matrix factor, $\operatorname{Hom}(Y,Y')=Y^\vee\otimes Y'$ and the self-dual factors identify its Hermitian dual with itself, as can also be seen in local bases. With the factor $\delta\mathfrak c$ the absolute trace calculation therefore gives $A^\#=A$ for $e$. The identity $q(x)=e((1+\sqrt{-d})x/2,x)$ gives integrality and the semicharacter law on $A$. This extends the earlier block calculation to nonstandard $Y,Y'$. [Trace dual and period signs](2026-11-23-fourfold-theta-lattice.md) · [Hom module and trace](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean#L27-L39) · [Lattice and form](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean#L68-L88)

The standard line is one-dimensional and nonzero by the earlier finite average. The same holds on $A$ because the normalized averages between two commensurate self-dual lattices with compatible signs are inverses. Their translates have distinct period characters and each has the original Gaussian norm. Fix any nonzero section $F_A$ on this line. Let $t$ be the unitary complex-linear pullback on the argument, rational on the arithmetic space, and put $S=t^{-1}A$. With $I_{AS}$ the released normalized average there is a scalar
$$
 F_A(tz)=c\,I_{AS}F_A(z), \qquad |c|=1 .
$$
We calculate $c$ independently. The pinned implementation proves the fixed-point-free instance, then factors a rational point to handle fixed directions through its Weil representation. [Target-side claim and determinant](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ThetaPullbackSecondGroupRationalPointEqDetSmul.lean#L150-L182) · [The release's factorization](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/OddEqOfEven.lean#L82-L105)

## The finite sum that reads the phase

Periodize a single Gaussian kernel,
$$
 K(z,w)=\sum_{x\in A}\beta(x)
 \exp\{\pi H(w+x,z)-\pi H(w,x)-\pi H(x,x)/2\}.
$$
On compact $(z,w)$ sets the summands are bounded by a Gaussian in $x$ times $e^{O(\|x\|)}$, so the sum and its integral on a compact period cell converge absolutely. For each $z$ this is a section in $w$ by translating the lattice index. Replacing $x$ by $-x$ gives Hermitian symmetry. The one-dimensionality gives $K(z,w)=k_0\overline{F_A(z)}F_A(w)$. At $w=z$ the weighted kernel is a Fourier sum with constant term one. All other characters integrate to zero over $A$, so $k_0\|F_A\|^2=1$ with the normalized mean. [Kernel used in the original comparison](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PullEqGaussSmulIntertwiner.lean#L211-L227)

Set $V_0=\ker(1-t)$ and $V_1=\operatorname{im}(1-t)$. Unitarity makes these orthogonal and rationality gives full lattices $A_0=A\cap V_0$ and $A_1=A\cap V_1$. Write $B=(1-t)|_{V_1}$, and $C=B^{-1}-1/2$ on $V_1$, so $C^*=-C$. Choose an even $m$ clearing the denominators of $C$ there, with $mCA_1\subseteq 2A_1$. The lattice $D=A_0\oplus mB^{-1}A_1$ lies in $A\cap S$. For $V_1=0$ the empty determinant and the finite sum both equal one.

Take the mean over $D$ of $K(z,tz)e^{-\pi H(z,z)}$. In the expression using $F_A$, orthogonality with the original section retains only the zero coset of the normalized $A$-to-$S$ average. The mean is $c/\sqrt{[S:A\cap S]}$. In the lattice sum, integration over $V_0/A_0$ first removes every $x$ outside $A_1$. Its character there is $e^{2\pi i e(x,z_0)}$, trivial precisely when the fixed-space component of $x$ vanishes. This step accounts for an arbitrary gluing of $A_0$ and $A_1$ inside $A$.

For $x\in A_1$ put $z_x=B^{-1}x$. In the remaining exponent write $z=z_x+w$. The linear terms in $w$ vanish by $tz_x=z_x-x$ and unitarity. The remaining term is exactly
$$
 \psi(x)e^{-\pi H(Bw,w)},\qquad
 \psi(x)=\exp\{\pi i(q(x)-e(Cx,x))\}.
$$
Here $-H(Cx,x)$ is purely imaginary. The phase is periodic on $A_1/mA_1$. For our choice of $m$ this follows from the integrality of $e$ and the period signs. Even the weaker denominator condition in the source suffices. If $v=mh=y-ty$ with $y,ty\in A_1$, then $2Cv=y+ty$. The cross term in $q(x+v)-e(C(x+v),x+v)$ modulo two is $e(x,v)-2e(Cv,x)=2e(x,y)$. Also $q(v)\equiv-e(y,ty)=e(Cv,v)\pmod 2$. These give $\psi(x+v)=\psi(x)$ at that denominator as well. [Exact denominator and Gauss-sum hypotheses](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitaryThetaConstantEqInverseDeterminantPhase.lean#L39-L56)

Within each residue class $x\bmod mA_1$ the centers $z_x$ translate by $mB^{-1}A_1$. Unfold their integrals to all of $V_1$. Every eigenvalue $\nu$ of $B$ has $\Re\nu>0$. In orthonormal complex coordinates, radial integration gives $\int_{\mathbb C}e^{-\pi \nu |w|^2}\,dw=1/\nu$. The other volume and normalization factors are positive real. Consequently
$$
 c=(\text{positive real})\,
    \frac{\sum_{x\in A_1/mA_1}\psi(x)}{\det_{\mathbb C} B}.
$$
In particular the finite numerator is nonzero. The preceding overlap computation established this before making a sign claim. A singular inverse on the fixed subspace is unnecessary. [Released integral identity](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PullEqGaussSmulIntertwiner.lean#L24-L39) · [Where the numerator phase matters](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitaryThetaConstantEqInverseDeterminantPhase.lean#L249-L275)

## Why the numerator is positive on this host

The CM extension $E/F$ is unramified at every finite place. Here is the check from the defining characters. Outside the cyclotomic conductor there is no ramification. The primes over $Q_S q$ split in $K$ by the host symbols (including the dyadic prime), hence complex conjugation cannot stabilize a prime there. At $d$ inertia has image in $\{1,\mathrm{iod}\}$ since it fixes the part of conductor prime to $d$. The characters distinguish $\mathrm{iod}=((1,-1),1)$ from complex conjugation $((-1,-1),1)$. Relative inertia over $F$ is the intersection with the group generated by complex conjugation, so it is trivial here too. [Splitting at the host primes](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/FrobeniusOrbits/Statement.lean#L13-L15) · [Value of the conjugation sign](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/FrobeniusOrbits/Statement.lean#L33-L36) · [Conductor action](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean#L16-L46) · [Two distinct elements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean#L102-L112)

For any integer $a>0$ this supplies an algebraic integer $\ell$ with $\ell\bar\ell\equiv-1\bmod a\mathcal O_E$. At a split place use $(1,-1)$. At an inert place the norm of the quadratic residue field is onto. Lift a solution by multiplying by $1+\pi^j t$, which changes the next norm digit by the surjective residue-field trace. The Chinese remainder theorem combines the finitely many lifts. This is a congruence in the actual half-different arithmetic, valid even though norms are positive at real places. It also normalizes local unit lengths in the calculation below. [Congruence used by the release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsDvdMulInvolutionAddOne.lean#L81-L100)

For $\ell\bar\ell=-1+4m b$ one has $b=\bar b\in\mathcal O_F$. Multiplication by $\ell$ permutes $A_1/mA_1$, commutes with $C$, and turns $\psi$ into its complex conjugate. Indeed $2(\sqrt d/2)\Re H(bx,x)$ is integral by polarizing $q$ on $bx,x$. Also $2mCx\in A_1$, even for the weaker denominator condition above, so $4m e(bCx,x)$ is even. This proves reality. A real nonzero sum can still be negative.

For the sign, decompose the finite quadratic group at the rational primes dividing $m$. The embedded period and the scale cancel in $q$ and $e$, which are rational trace forms on the arithmetic coordinates. The phase is a quadratic form valued in $\mathbb Q/\mathbb Z$ after dividing its exponent by two. Cross terms between components of coprime order vanish by biadditivity, so the sum factors over these primes. Equivalently, each component uses the local trace formula modulo $\mathbb Z_p$ and the usual additive character of $\mathbb Q_p/\mathbb Z_p$. Local changes of integral basis respect this calculation.

For a target move the source lattice $Y$ stays fixed. At each place of $F$ over $p$, $Y$ has an orthonormal integral basis. In the split case choose dual bases in the two components. In the inert case the residue Hermitian form is nondegenerate and has a vector of nonzero norm. Lift it, normalize the unit norm by the local norm surjectivity just proved, and split off its orthogonal complement. Induction gives a basis. In these local coordinates the Hom lattice has $r$ identical orthogonal column blocks, with the same $J$ in each. Intersecting with $V_1$ takes the moving target subspace in each column. Thus the local sum is the $r$th power of one real sum. The same argument for a source move uses the stationary target and $s$ row blocks. The stationary rank is even on every actual edge. The total finite sum is consequently nonnegative, and its nonvanishing makes it positive. This argument uses only local splittings of the stationary lattice and applies to globally indecomposable lattices. [Parity parameters](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/Params.lean#L7-L14) · [Ranks on the edges](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/Params.lean#L30-L36) · [Two halves and the norm congruence in the source](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ThetaPullbackSecondGroupRationalPointEqDetSmul.lean#L196-L221)

It follows that $c=|\det B|/\det B$. Put $k=\operatorname{rank}_E(1-g)$ for a target move $g\in U_s(E)$. On its moving space,
$$
 z_0=\prod_{\tau\in\Phi}\det{}'(1-\tau(g)^*),\qquad
 \frac{\bar z_0}{z_0}=(-1)^{fk}\prod_\tau\tau(\det g).
$$
The prime denotes the determinant restricted to the moving space. The identity holds eigenvalue by eigenvalue, and the $E$-rank is the same at every embedding. The exponent $f$ is even, and $\det B=z_0^r$. Therefore the multiplier of the pullback relative to the raw average is
$$
 c_{\rm target}=\left(\prod_\tau\tau(\det g)\right)^{r/2},
 \qquad
 c_{\rm source}=\left(\prod_\tau\tau(\det g)\right)^{-s/2}.
$$
The reciprocal on the source follows from the right action by $g$ in the argument instead of the left action by $g^*$. These are the released determinant powers. [Argument of the pullback](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean#L104-L109) · [Target determinant reduction](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ThetaPullbackSecondGroupRationalPointEqDetSmul.lean#L223-L234) · [Source orientation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ThetaPullbackFirstGroupRationalPointEqSmul.lean#L141-L159)

## A genuinely mixed row

In the first two target coordinates put $v=(3,4)^t$ and
$$
 u=\frac{1+\sqrt{-d}}{1-\sqrt{-d}},\qquad
 g=I+(u-1)vv^t/25 .
$$
Extend by the identity on all remaining target coordinates. This acts by $u$ on $v$ and fixes its orthogonal complement. The off-diagonal entries $12(u-1)/25$ are nonintegral at primes above $5$ since $d\ne5$ and $u-1=2\sqrt{-d}/(1-\sqrt{-d})$. The trace of $u$ to $\mathbb Q$ is $-2+4/(d+1)$, a noninteger; hence its phase has infinite order. For the actual row lattices the pullback scalar is exactly $u^{fr/2}$. A height comparison alone would leave it undetermined.

As a separate direct evaluation take the elliptic factor $K=\mathbb Q(\sqrt{-7})$ with $\tau=(1+\sqrt{-7})/2$. On two coordinates the image lattice has 1,250 cosets modulo its intersection with the original one. The moving lattice is $v\mathcal O_K$, on which $C=1/(2i\sqrt7)$ and $\psi(vx)=e^{2\pi i\,2N(x)/7}$. Here $N(a+b\tau)\equiv(a+b/2)^2\bmod7$. The one-dimensional Gaussian sum has phase $+i$: its squared modulus is $7$ by Fourier orthogonality, its real part vanishes by pairing quadratic residues with nonresidues under negation, and $\sin(2\pi/7)+\sin(4\pi/7)+\sin(8\pi/7)>0$. Hence $c=i|1-\bar u|/(1-\bar u)=\tau/\sqrt2$. The raw moved function after evaluation at $gz$ is the original multiplied by $\bar\tau/\sqrt2$. Direct summation over the 1,250 cosets reproduces this value at three complex arguments. This one-factor control has ramification at $7$, where $-1$ is a quadratic nonresidue and the norm congruence fails. It detects exactly what would go wrong with an unconditional positivity assertion. [Exact finite checks and direct Jacobi sum](check_unitary_row_phases.py)

## Unresolved

This calculation derives the scalar for one rational move at its actual arithmetic input. The released jet uses a family obtained by *successive* lattice averages. Their phases could still change when the path through the lattices changes. The [triangle calculation](2026-11-23-phase-around-three-lattices.md) tests the compositions needed for those row maps. The direct moving-space argument gives an additional check for singular $1-g$. It does not audit every global assertion about the reference Weil representation.
