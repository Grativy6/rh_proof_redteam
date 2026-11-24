# What is in the axiom list before anyone proves the theorem?

**24 November 2026.** On the release’s Lean 4.33.1 and Mathlib pin, the definition `RiemannHypothesis` already reports `propext`, `Classical.choice` and `Quot.sound`. The one-line function returning an explicitly supplied proof of RH reports the same three. So does the released, unconditional `riemannHypothesis` theorem. Its compiled proof term refers to `rhOfAll`. The three names alone cannot distinguish any of these cases. The same control on the corpus toolchain, Lean 4.32.1, gave the same result. [Runnable controls](AssumptionsOfStatements.lean) · [Pinned Mathlib definition](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L178-L186) · [Released declaration](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L1-L6) · [Compiled root provenance](2026-11-24-lean-check-comparison.md)

### The actual comparison

| Checked object | What it supplies | Foundational axiom names |
| --- | --- | --- |
| Mathlib’s `RiemannHypothesis : Prop` | Defines the proposition | All three |
| `riemannGiven : RiemannHypothesis → RiemannHypothesis` | Returns its input with the term `fun h => h` | All three |
| Released `riemannHypothesis : RiemannHypothesis` | Applies the released proof, with no RH premise in its type | All three |
| `FieldFrameStatement : Prop` | Defines the identical left-inverse matrix target used for comparison | All three |
| `fieldFrameGiven : FieldFrameStatement → FieldFrameStatement` | Returns its input | All three |
| `fieldFrameFromSemiring : FieldFrameStatement` | Proves that target using APCI and semiring matrix identities | All three |
| APCI’s `exactCertificate_implies_fiberConstant` | Derives equal answers on inputs with the same trace from an exact decoder | None |
| `quotient_denominator_collision` | Rules out decoding the next denominator digit from the observed residue | None |

Lean’s collector visits both the type and the value of a theorem. In the released RH declaration the constant `RiemannHypothesis` occurs literally in the type. Its three dependencies therefore already occur in the full list for this spelling. The list is a set: a proof can use the same foundations many more times without its list changing. Ordinary premises such as “given RH” or “given $LC=I$” are visible in the type. The distinction can be inspected in the [versioned collector](https://github.com/leanprover/lean4/blob/v4.33.1/src/Lean/Util/CollectAxioms.lean#L50-L66) and the [ascriptions and axiom queries](AssumptionsOfStatements.lean).

### The same measurement on the corpus

For each earlier named source declaration the [probe](probe_statement_axioms.py) enumerates the constants occurring in its inferred type and unions their transitive axioms. It then asks Lean for the full declaration’s set and checks that set against the original [theorem inventory](2026-11-24-corpus-theorem-axioms.jsonl). Each line of the [result table](2026-11-24-statement-axioms.tsv) identifies its source-inventory row. The inventory SHA-256 is `631172dbc86397eafd6c88958a525956b38e8cd3c9f750457612aa8c2a539491`.

| Observation | Corpus toolchain 4.32.1 | Unchanged declarations available on RH’s 4.33.1 |
| --- | ---: | ---: |
| Named declarations measured | 746 | 655 |
| Statement already reaches all three axioms | 296 | 248 |
| Statement reaches none | 352 | 331 |
| Full declaration adds no axiom name beyond its statement | 514 | 441 |
| Full declaration adds at least one name | 232 | 214 |
| Full declaration reaches none | 172 | 161 |

For example, APCI’s exact-decoder-implies-constant-on-fibers direction is axiom-free in both its statement and its proof. Its converse on reachable traces has an axiom-free statement and its construction uses classical choice to select a representative. All eight unchanged corpus declarations whose full lists gained `Classical.choice` on the RH pin already gained it in their **statement dependencies**. This locates the observed difference without inferring how often a proof independently uses the same axiom. The 91 unavailable declarations come from the eleven cross-version module failures documented in the [source and replay comparison](2026-11-24-lean-check-comparison.md).

### What the headline proof actually takes as input

The released `rh_of_right` literally receives the assertion that $\zeta(s)\ne0$ whenever $\Re(s)>1/2$ and $s\ne1$. For Mathlib’s zeta function this premise is **equivalent to the headline RH statement**. To prove the reverse implication on paper, take a zero with $\Re(s)>1/2$ and $s\ne1$. Its real part excludes every negative even integer. Applying the stated RH conclusion to this zero gives $\Re(s)=1/2$, a contradiction. This is an audit of the strength of a premise. [Exact reverse implication and equivalence](ZetaHalfPlaneCut.lean) · [Released premise and case split](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GammaFactorNonvanishing/RhOfRight.lean#L5-L15)

The forward direction has a short independent reading. Given a nontrivial zero with $\Re(s)<1/2$, let $w=1-s$. Then $\Re(w)>1/2$ and $w\ne1$, as $\zeta(0)=-1/2$. The functional equation writes $\zeta(s)$ as $2(2\pi)^{-w}\Gamma(w)\cos(\pi w/2)\zeta(w)$. The gamma and exponential factors are nonzero there. A vanishing cosine would make $w$ a positive odd integer, making $s$ zero or a negative even integer. The right-half-plane premise rules out $\zeta(w)=0$. This excludes left-half-plane nontrivial zeros. A nontrivial zero on the right was excluded directly. [Functional equation and exceptional points](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GammaFactorNonvanishing/RhOfRight.lean#L15-L62) · [Mathlib’s functional equation](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L178-L180)

The parent `rh_of_every` supplies this premise from `EveryCharacter` by taking modulus $1$ and its trivial character, whose Dirichlet $L$-function is $\zeta$. The proof term `rhOfAll` supplies `allChi`. The upstream declaration passes a named Galois representation theorem into `everyCharacter_of_row`. That step consumes the automorphic window and additional arithmetic inputs. The appearance of an RH-equivalent premise in the reflection lemma therefore locates a handoff. Establishing a circle or a failure would require finding where its upstream justification assumes that premise, or exhibits some different property. [Modulus-one substitution](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GammaFactorNonvanishing/CritLine.lean#L29-L32) · [Quantified nonvanishing statement](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean#L13-L17) · [Parent proof term](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Supplements/Kernels/MainTheorems.lean#L7-L12) · [How the parent receives its input](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L7-L14) · [Named Galois input](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean#L4-L8) · [Window consumer](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean#L3-L5)

### Chris’s blank-slot control

The corpus’s axiom-free APCI implication lets us give the decoder any proposition as the answer it prints. Choose Mathlib’s actual `RiemannHypothesis`. Two different switches with the same trace now print the same answer. Lean accepts the aptly named `iUsedLeanToProveRH : RiemannHypothesis = RiemannHypothesis`. The same template accepts `False = False`. A negative control offers the RH equality as a proof of bare `RiemannHypothesis` and requires Lean to reject it. The equals sign would like a coauthor credit. [The complete joke](IUsedLeanToProveRH.lean)

### Reproduce

Compile [SpectralFrameControls.lean](SpectralFrameControls.lean) and then [AssumptionsOfStatements.lean](AssumptionsOfStatements.lean) against the pinned Mathlib and APCI interface, with the output directory in `LEAN_PATH`. Compile the [joke](IUsedLeanToProveRH.lean) against those same libraries. For [ZetaHalfPlaneCut.lean](ZetaHalfPlaneCut.lean), first compile the unchanged pinned [RhOfRight.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GammaFactorNonvanishing/RhOfRight.lean#L1-L62) at its original module path and include that object directory. The release source file has SHA-256 `7e2c0b519ee420192cad8fb281c2d2bfebae2ba553342fd579c81c2aa0bd3dc5`. The new proofs can be inspected and the displayed arithmetic can be followed independently of the checkers.

I compiled the unchanged release reflection lemma on 4.33.1, compiled the reverse implication against it, and replayed both with the native kernel and lean4lean. The statement controls passed native replay on both pins and independent replay on 4.33.1. The APCI joke passed both checkers on 4.33.1. In a separate compile, offering its equality as a proof of bare RH returned a type mismatch and exit code 1.

For the corpus table use the build trees from the [previous replay](2026-11-24-lean-check-comparison.md). Run `python probe_statement_axioms.py --help`. Supply each pin’s Lean binaries, matching dependency packages, and the PAL and CPX `objects` directories, along with a fresh `--out` path. The script verifies the compiler version, the named record count and each full axiom list before emitting the TSV.

### Unresolved

The source and assumption counts answer Chris’s comparison question. They give a weaker ordinary hypothesis for the same matrix inference and an explicit example of two equal observations with different arithmetic answers. The [integral frame](2026-11-24-integral-spectral-frame.md) and [inert transfer calculation](2026-11-24-three-colliding-eigenlines.md) check whether those omitted data actually enter two uses in the release. Where the mathematical comparison remains open, the labels on either Lean proof have no deciding role.
