# What the disappearing-tail counterexample establishes

**23 November 2026 · Hearthline, at Chris Pang’s request.** The unrestricted coefficient operation has a counterexample. The release uses it on specified theta functions. A paper calculation below checks the protection for its one-variable input, including the half-period normalization. Independent verification of the complete higher-rank input and its uniform height bound remains open.

## 1. Demonstrate the counterexample

Fix any integer $r\ge0$ and put $u=(3-\sqrt5)/2$, so $0<u<1/2$. Its field conjugate is $v=(3+\sqrt5)/2=u^{-1}>2$. Take

$$
 f_r(z)=\sum_{n>r}u^{n^2}z^n.
$$

For any $R>0$, eventually $u^nR<1/2$. On $|z|\le R$ the $n$th term is then bounded by $2^{-n}$. Thus $f_r$ is entire, and $f_r(1)>0$. All coefficients are algebraic integers in one quadratic field. Its first $r+1$ Taylor coefficients equal those of the zero function. At any fixed $z\ne0$, conjugating the coefficients gives terms of magnitude $(v^n|z|)^n$, which tend to infinity. At $z=0$ the series converges to zero. This proves the mathematical failure without a theorem prover.

The source implements this operation as `fnConj` using a total sum. The pinned library assigns zero when there is no sum. Thus on this input the implemented operation returns the zero function. Beginning the sum at $n=0$ would change the example. With a constant term one, the totalized result is one at zero and zero elsewhere. Keeping $n>r$ makes the everywhere-zero result exact. [Taylor coefficients and actual definition](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean#L110-L136) · [Pinned total-sum definition](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean#L130-L147)

## 2. Identify what the proof actually needs

The numerical consumer `logThAt` applies `fnConj` to the specific standard vacuum `B.thZero a b` before taking a norm on the conjugate lattice. At the comparison step `CjF` asks for an entire receiving function with the conjugated Taylor coefficients in **every** degree. Recovering such a function from its coefficients is standard complex analysis. Producing it for the arithmetic vacuum is the disputed obligation. Demonstrating that the operation fails on $f_r$ refutes its unrestricted use. Refuting this call requires an admissible vacuum on which its required identification or bound fails. [Norm input and field requirements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TopPlaceLogTheta.lean#L49-L72) · [Actual comparison condition](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsTraceCompatibleTorusEmbeddingStandardTorus.lean#L11-L15) · [Where that condition is consumed](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ThetaVacuaConjugatesCmPoints.lean#L44-L54)

## 3. Establish protection at the actual input

For the one-dimensional ingredient the release specifies a nonzero ideal $\mathfrak a$ of $\mathbb Q(\sqrt{-d})$, the scaled period lattice $\Lambda=\delta\mathfrak a$ in the chosen complex embedding, and a normalized odd theta section. Write $a$ for its cubic Taylor coefficient. From its translation law and divisor, one obtains

$$
 a=\frac{1}{4d}\sum_{0\ne T\in\ker[\sqrt{-d}]} x(T).
$$

This is a finite expression on the elliptic curve with its invariant differential. Transporting its finitely many torsion points transports $a$. The Weierstrass recurrence then determines all remaining coefficients and gives an explicit entire receiving function. For the normalized half-period used by `th0`, squaring gives a second explicit identity fixing every coefficient, including its phase at the origin. These are paper derivations from the data defining the input and classical elliptic-function facts. In a degree-seven example the six points give $\sum x(T)=-14$ and $a=-1/2$. [Period lattice and its normalization](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean#L41-L60) · [Odd theta being selected](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean#L234-L240) · [Half-period input](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GL3Theta.lean#L198-L204) · [Derivation, exact example and classical sources](2026-11-23-cm-theta-torsion-trace.md)

There is another choice at higher rank. The source specifies `thMM` by requiring its fourth tensor power to equal a particular finite intertwining kernel. It then takes tensor powers of `thMM` to get `thZero`. Symmetry alone would permit $1+z_1z_2z_3z_4$, which already violates the necessary slice identity at zero and one. This control gives a test for the arithmetic kernel. The open inputs include nonvanishing and factorization on the selected lattice with its actual character and normalization, the identified coefficient field, and the bound uniform over the stated ranks and embeddings. The release supplies source theorems for these steps. Their existence does not discharge the outstanding independent checks. [Fourth-power selection](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/KernelLattices/LateralTheory.lean#L23-L36) · [Additional hypotheses and the actual kernel](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/ProductThetaMem.lean#L43-L70) · [Transfer into thZero](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1.lean#L126-L138) · [Explicit slice test](2026-11-23-cm-theta-torsion-trace.md)

## Correction to the audit record

Earlier summaries used “survives” for implications whose object-identification or arithmetic hypotheses came from the release. A conditional derivation and an independently checked protection on every selected input warrant different conclusions. The same qualification applies to the [raw theta range](2026-11-23-raw-theta-integral-image.md), the [fixed-level lengths](2026-11-23-fixed-level-theta-congruences.md) and the [Hecke class-factor calculation](2026-11-23-hecke-class-factor.md). Their finite controls and algebraic deductions stand on the hypotheses stated in each receipt. The upstream rank estimates, full range and spectral identifications cited there still need independent justification wherever the objection turns on them. A checker acceptance is evidence about a formal artifact and its precise input route.

[Corpus used and how to repeat the tests](../corpus/README.md) · [Three questions in the public work key](../RH-PROOF-WORK-KEY.md#three-questions-for-a-candidate) · [Windows replay experiment](2026-11-23-windows-checker-report.md)

## Unresolved

No failure of the claimed RH implication has been established here. The unrestricted operation has been falsified, and the one-dimensional complex multiplication protection has been independently derived. The specific higher-rank kernel and its uniform arithmetic estimate remain open audit targets.
