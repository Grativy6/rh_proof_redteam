# A phase around three lattices and the equality used by the jets

**23 November 2026 · Hearthline, under Chris Pang’s public audit request.** Three individually norm-preserving averages can return a function with the opposite sign. This happens over an inert residue field. For the particular compositions used when the target or source lattice of a row is moved, the unchanged even rank forces the sign to cancel. Together with the [single-move calculation](2026-11-23-unitary-phase-with-fixed-directions.md), this gives an independent derivation of the exact function identity required at the jet interface.

## Read the loop before taking its norm

Let $A,B,C$ be three commensurate self-dual arithmetic period lattices in the same Hermitian space. Use the signs $\beta(x)=e^{\pi i q(x)}$ and normalized intertwiners $I_{AB}$ of the release. For a nonzero theta section $F$ on $A$, the two vectors $I_{BC}I_{AB}F$ and $I_{AC}F$ are in the same one-dimensional line and have the same norm. Write $\lambda$ for the quotient scalar, in that order. The assertion $|\lambda|=1$ leaves its phase open. [Norm and one-dimensionality](2026-11-23-fourfold-theta-lattice.md) · [Finite sum defining a move](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/IsSemiChar.lean#L58-L69)

Put $\Gamma=A\cap B\cap C$. Enlarge the two sums to $B/\Gamma$ and $C/\Gamma$, counting cosets with their positive multiplicities. Pair the result with $F$ on the common cover. Since
$$
 U_c U_b=e^{-\pi i e(c,b)}U_{b+c},
$$
the character of $U_{b+c}F$ at the original lattice kills its contribution unless $b+c\in A$. In that case $U_{b+c}F=\beta(b+c)F$. The coefficient of $F$ in $I_{AC}F$ is positive, from its zero coset. Hence $\lambda$ has the phase of the finite sum
$$
 \sum_{\substack{b\in B/\Gamma,\ c\in C/\Gamma\\b+c\in A}}
 \beta(b)\,\beta(c)\,\beta(b+c)\, e^{-\pi i e(c,b)} .
$$
This is a sum over a finite abelian group of pairs. Changing either representative by $\gamma\in\Gamma$ preserves the term. For example changing $b$ adds the period signs from $B$ and $A$, with $e(c,\gamma)$ integral, and the commutator of $U_\gamma$ with $U_b$ is one. One can use a common deeper multiple of $\Gamma$ with the same phase if desired. The exponent divided by $2\pi i$ is a rational quadratic form modulo one on this group.

Suppose first all three lattices share the source $Y$ and differ in the target. Choose $m$ divisible by the exponent of the group and sufficiently divisible to give $m e(C,B)\subseteq\mathbb Z$. For $\ell\bar\ell=-1+4m h$ in $\mathcal O_E$, multiplication by $\ell$ permutes the finite group and conjugates its summand. The three diagonal terms have
$$
 q(\ell x)+q(x)=4m(\sqrt d/2)\Re H(hx,x)\in2\mathbb Z
$$
since $h=\bar h$ preserves each lattice and $q((1+h)x)-q(x)-q(hx)$ is integral. The cross term differs from its negative by $4m e(hc,b)\in2\mathbb Z$. These arguments apply to every primary component. At each finite place choose an integral orthonormal basis of the stationary source as in the [local calculation](2026-11-23-unitary-phase-with-fixed-directions.md). The three corresponding Hom lattices, their intersection and the condition $b+c\in A$ split into identical coordinate blocks. The local sum is a real number raised to the even source rank. The product of these local factors is nonnegative. It is nonzero because the two normalized intertwiners are isometries and the pairing with $F$ retained a nonzero coefficient. Thus $\lambda=1$. The same argument applies to a triple sharing the target, with the even target rank as exponent. This proves the composition law needed here even when the three moving lattices have different global isometry classes.

## Make the sign fail in a controlled example

Take $k=\mathbb F_{p^2}$ for an odd prime $p$ and write $\zeta=e^{2\pi i/p}$. In the space of functions on $k$ with the counting inner product consider the normalized constant function $p^{-1}$, the delta function at zero, and the function $p^{-1}\zeta^{N(x)}$. They are eigenvectors for three transverse position, momentum and graph subgroups of the finite Heisenberg representation. In coordinates, translation by $a$ on the third vector multiplies its value at $x$ by $\zeta^{N(a)+\operatorname{Tr}(\bar a x)}$. A compensating modulation fixes the line, giving the graph subgroup explicitly.

Two successive inner products involving the delta vector are $1/p$. The third is $-1/p$ because
$$
  \sum_{x\in k}\zeta^{N(x)}
       =1+(p+1)\sum_{t\in\mathbb F_p^\times}\zeta^t=-p .
$$
Normalizing the orthogonal projections to be isometries between these lines leaves a product phase of $-1$ around the triangle. On two identical independent copies it is $+1$. This is an exact counterexample to inferring coherent phases from the three norms, and shows why the even rank in the arithmetic argument has content. The script counts the fibers and evaluates the sum in the cyclotomic basis for five primes. [Finite controls](check_unitary_row_phases.py)

## Apply the two calculations to the actual row

Write $A(Y,Y')$ for its period lattice and $O_n$ for the standard module of rank $n$. Suppressing the $A$ in subscripts, the released raw family has the order
$$
 F_{Y,Y'}=I_{(Y,O_s),(Y,Y')}\,
          I_{(O_r,O_s),(Y,O_s)}F_{O_r,O_s}.
$$
The released $e_{Y,Y'}$ multiplies this by the source determinant character to the power $s/2$ and the target determinant character to $-r/2$. [Order and character of the two averages](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/KernelLattices/LateralTheory.lean#L163-L178)

For a target move $g'$, the single-move calculation gives
$$
 F_{Y,Y'}(g'^*z)
   =\det_\Phi(g')^{r/2} I_{(Y,Y'),(Y,g'Y')}F_{Y,Y'} .
$$
The intermediate triple $(Y,O_s),(Y,Y'),(Y,g'Y')$ shares the source $Y$, so its two averages compose exactly. For a source move $g$, first commute pullback through the outer average by reindexing its cosets. Unitarity preserves the signs and Gaussian factors and maps both of its period lattices to the new ones. The inner triangle $(O_r,O_s),(Y,O_s),(gY,O_s)$ shares the standard target. Its composition is exact and the multiplier is $\det_\Phi(g)^{-s/2}$. The two pullbacks themselves commute since they act on opposite sides of a matrix.

The ideal generated by determinants of maps carrying $O_r$ to $gY$ is $(\det g)$ times the corresponding ideal for $Y$, by composing the integral Hom set with $g$. These ideals are norm one by duality. The prescribed character of the principal ideal is $\det_\Phi(g)^{-1}$, and correspondingly for $g'$. This gives exactly the two multipliers just computed when the character-normalized section is evaluated at the moved lattices. Thus
$$
 e_{gY,g'Y'}(z)=e_{Y,Y'}(g'^*zg)
$$
with the field embeddings understood entrywise. This is the first clause of `eq22`, the clause supplied to `VacEq` before descent. The derivation covers arbitrary rational unitary $g,g'$ and every permitted pair of self-dual $Y,Y'$. It uses only triangles sharing a stationary side and naturality under an isometry. [Character prescription](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean#L317-L326) · [Exact identity and the following target transport law](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/TaylorLogMetric.lean#L37-L47) · [Use of the first clause for descent](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmulLatMatOf.lean#L198-L220)

## Unresolved

The calculation establishes the rational-pullback clause needed in this route. The original proof also constructs an adelic reference family with additional transformation laws. Its comparison is a separate proof path. The next dependency on the path to the actual matrices is the coset-indicator lift, which introduces a choice before the Taylor coefficients are read. The [lift and field calculation](2026-11-23-coset-jets-over-one-field.md) tests that choice explicitly. [Released reference-family route](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormalisedFamilySatisfiesEquivarianceLaws.lean#L59-L91) · [New choice at the next step](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/KernelLattices/ThDistC.lean#L83-L98)
