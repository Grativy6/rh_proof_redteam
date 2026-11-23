# RH proof work key 01 — What does the geometry witness certify?

**23 November 2026 · Prepared by Hearthline under Christopher D. Pang’s request for a public audit.** The target is Levent Alpöge and Claude’s released proof of the Riemann Hypothesis. Jenny Lorraine Nielsen identified a geometry predicate that accepts every input. The PAL corpus gives us a way to test which mathematical distinctions survive that formalization. [Nielsen’s critique](https://philarchive.org/rec/NIEIOT-2) · [Alpöge’s announcement](https://alpo.ge/remark.pdf)

## Turn this key

> Find a point where the mathematical argument calls for a property X, the released Lean code certifies a property Y, and one can hold Y fixed while changing the answer to X. Trace the first consumer that needs X and check what it actually receives.

A **key** records the object, question and test before the outcome is known. Chris selects the work. **Turning** the key means doing the mathematics. The **receipt** preserves the evidence, what failed, and the next reader’s starting point. This key refines the [initial zero-pairing preparation](https://github.com/Grativy6/rh_proof_redteam/blob/65351a0a720c7ef80e06b70c7c99767f509698f2/RH-PROOF-WORK-KEY.md) after Chris clarified that the target is a mathematical mismatch that can survive formal checking.

## First turn

The first use of this key produced a counterexample to the mixed-intersection interpretation of the chosen geometry model. Its two positive weights give 2 in one order and 8 in the other, while the classical answer is 4. The receipt also tests surface replacement and corrects two source links using the compiled dependency graph. [Turn 1 receipt](receipt-archives/2026-11-23-geometry-witness.md)

## Second turn

The chosen divisor builder fails the release’s section-growth condition at every stage. A genuine mixed numerical estimate on the RH path uses a different intersection operation. We tested a case where substituting the first-slot operation would change its strict premise from false to true. The nonempty-index theorem and the genuine mixed-degree calculation both passed kernel replay against the original release libraries. [Turn 2 receipt](receipt-archives/2026-11-23-mixed-estimates.md)

## Coefficient descent

A nonzero complex input can turn into zero on descent to a number field. We tested the actual field of definition, the degrees that enter the theta operator, and the cost of replacing an integral line by a single vector. The original complex coefficients enter the field construction before descent. [Argument and examples](receipt-archives/2026-11-23-coefficient-descent.md)

## Quotient covolume

We took the same integral quotient before and after changing the complex embedding. The resulting difference has no uniform upper bound in rank one. The release uses an inequality in the direction that this difference permits. A second calculation tests the two primes used in a Hermitian basis change. [Calculations and consumer](receipt-archives/2026-11-23-quotient-covolume.md)

## Periods on a quotient

We tested whether an orthogonal representative can introduce a denominator, whether individual maps can vanish after projection, and whether separate rotations of the target could collapse the combined rank. [Hand-checkable examples and the lost-dimension estimate](receipt-archives/2026-11-23-period-on-quotient.md)

## The local theta integral

Holding the compact weight fixed, we varied the polynomial and evaluated the matrix-coefficient integral. The [receipt](receipt-archives/2026-11-23-oscillator-cancellation.md) identifies which contraction removes a genuine zero and which extra hypotheses enter the global estimate.

## The downward lift

We used two vectors with the same Hecke label to distinguish the two injectivity obligations. We checked whether a singular stratum could carry the residue needed for the downward argument, and re-counted a split Gram fibre at the exact dimension where integrability changes. [Map, residue and rank](receipt-archives/2026-11-23-downward-residue.md) · [Local density](receipt-archives/2026-11-23-split-gram-density.md)

The [fixed downward test](receipt-archives/2026-11-23-fixed-downward-test.md) follows the proposed kernel vector through its compact integral, exhibits a full-rank point outside the selected translates, and tests the passage from individual observers to a common finite set.

## Rational and integral comparison

We fixed all rational integrality tests, varied a lattice after extending scalars, and calculated the change in divisibility and determinant. We traced the additional integral-span requirement to the finite-place bound on a period. [The two lattices and the period](receipt-archives/2026-11-23-valuation-descent.md)

## A number assigned on an empty block

We followed a scalar set equal to the requested lower bound under a logarithm. We tested whether an unused label at one level could carry a period at the other. [Two levels, one character projector and the exact scope of the default](receipt-archives/2026-11-23-zero-part-eigenvalue.md)

## Transporting a normalization

We varied an algebraic unit across complex embeddings, then varied a formal group coordinate and one quadratic coefficient at an inert prime. The [phase calculation](receipt-archives/2026-11-23-conjugated-phase.md) checks what multiplies each class sum. The [CM calculation](receipt-archives/2026-11-23-height-two-coordinate.md) identifies the first denominator and the field extension required to remove it on one curve.

## Zero maps and the price of combining orbits

Hold the input lattice fixed and replace the chain by zero. Follow both the resulting index and the period of one fixed pair of vectors. Then preserve every individual orbit rank and force their bad directions to coincide. [The zero chain and the arithmetic comparison](receipt-archives/2026-11-23-zero-chain.md) · [Four powers of 5 missing from the rank-only estimate](receipt-archives/2026-11-23-correlated-places.md) · [An exact obstruction to isolating a single edge](receipt-archives/2026-11-23-edge-separation.md) · [Order at each graph plane](receipt-archives/2026-11-23-localiser-order.md)

## Testing the claimed rank

Fix the number of residual factors and their integral span condition. Vary which minors are selected and test every primitive combination of their products. Then keep the input degrees fixed and compare the images of different descriptions of an orbit segment. [The product calculation](receipt-archives/2026-11-23-minor-product-rank.md) · [The fixed-degree collision and its decoding](receipt-archives/2026-11-23-segment-collision.md) · [The cost of projecting the labels](receipt-archives/2026-11-23-trace-denominator.md) · [What the corrected dual test retains](receipt-archives/2026-11-23-corrected-trace-test.md)

## Testing the restricted plane pairing

Fix a vector spanning the entire exact source type. Make the factorial pairing on that line arbitrarily small at the prime, keep the allowed error, and look for the first relaxed test that can detect it. [Restricted determinant and cofactor](receipt-archives/2026-11-23-plane-determinant.md) · [Large-prime test](receipt-archives/2026-11-23-large-prime-plane.md) · [Projection on two representatives](receipt-archives/2026-11-23-model-projection.md)

## Starting sources

- Freeze the original release at `40e56bab026552e089d7afcfeff08d2defb9c005`. Begin with the distinction between `geoOf` and `anyGeometry`, the `OAt` record, the closure constructor, and the occurrence in the package supplied to the all-characters proof. [Predicates and record](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean#L14-L49) · [Selection on the compiled RH path](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L57-L72)
- Use the PAL v2.4-M `M-INTERFACE-FIBER` card and APCI’s reachable-image criterion. Name the two admissible inputs, everything the selected interface reads, and the specific answer it is supposed to certify. Use BRIDGE’s distinction between an object and its observable image when following the record into a consumer. [PAL v2.4](https://doi.org/10.5281/zenodo.22888036) · [APCI interface theorem](https://github.com/Grativy6/PAL-Lean-Audit/blob/5d5f88d283cd3fdab27aa2c7d91ceb0745653cd0/projects/APCI/APCILeanAudit/Interface.lean#L62-L66) · [Earlier audit](receipt-archives/2026-11-23-proof-audit.md)

## Object and first test

For the first turn, take X to be the explicit surface requirement in the release’s stronger geometric predicate. Take Y to be the selected geometry certificate **together with** its row/log compatibility. Fix the row, labels, relevant embeddings and numerical inputs. Try replacing the surface representation while preserving the readouts used to establish Y. Check whether the replacement satisfies the actual types, where the objects are chosen, and whether the stronger surface property can be recovered. Distinguish the published mathematical description, Nielsen’s proposed interpretation and the actual Lean requirement.

## How to decide the result

1. Exhibit an admissible witness to Y with X false, derive that Y entails X, or identify the exact missing construction. State any nonemptiness hypotheses. A counterexample to Y implying X establishes a local semantic mismatch.
2. Follow a named consumer into the RH argument. If that consumer needs only a weaker numerical fact, find the supplier of that fact. If it relies on X, identify where X is proved for the very same object.
3. Report separately the semantic result, its bearing on the geometric explanation, and the evidence about the headline theorem. A statement checked on different inputs, or a property suggested by a name, cannot settle any of these on its own.

## First-session deliverable

Return a dated receipt with the **target, source state, object, work, result, failure information, artifacts, and next live question**. Link the pinned declarations and include a reproducible test or a derivation another reader can check. Credit Nielsen for her published objection, Pang for the corpus and audit direction, and the reviewer for the particular test.

## Unresolved

The explicit rank-one cancellation has been traced to the joint harmonic condition. The analytic transfer, the quantitative size bound and the regular value of the global integral remain open to further tests. [Upward integral](receipt-archives/2026-11-23-oscillator-cancellation.md#unresolved)

The [fixed downward test](receipt-archives/2026-11-23-fixed-downward-test.md#unresolved) records the real character, split type primes and the remaining local branches. The [valuation comparison](receipt-archives/2026-11-23-valuation-descent.md#unresolved) returns to the arithmetic endpoints of a single pairing. The [zero-part test](receipt-archives/2026-11-23-zero-part-eigenvalue.md#unresolved) traces the archimedean estimate to the lower bound on an occupied block. The [matrix-ball check](receipt-archives/2026-11-23-formal-degree.md) computes the real-place integral for the scalar holomorphic series. The [CM coordinate](receipt-archives/2026-11-23-height-two-coordinate.md) and [sharp jet loss](receipt-archives/2026-11-23-jet-loss-and-frames.md#unresolved) trace the finite-place calculation. The [weighted rejection test](receipt-archives/2026-11-23-zero-chain.md#a-prime-whose-selected-orbit-set-is-empty) accounts for primes discarded at the threshold. The [edge test](receipt-archives/2026-11-23-edge-separation.md#unresolved) finds the exact one-slot degree cost and follows its change under Frobenius. The [higher-rank test](receipt-archives/2026-11-23-localiser-order.md#unresolved) finds the exact divisibility bought by the selected localiser. The [product](receipt-archives/2026-11-23-minor-product-rank.md#unresolved) and [segment](receipt-archives/2026-11-23-segment-collision.md#unresolved) tests locate two restrictions needed to count independent directions. The [trace calculation](receipt-archives/2026-11-23-trace-denominator.md#unresolved) reaches equality in the projection budget and follows the sum over nested prefixes. The [corrected dual test](receipt-archives/2026-11-23-corrected-trace-test.md#unresolved) can acquire other types. Its source-level margin survives the test. The [plane test](receipt-archives/2026-11-23-plane-determinant.md#unresolved) exhibits a whole exact line that fails while a cofactor succeeds. The [large-prime test](receipt-archives/2026-11-23-large-prime-plane.md) distinguishes scalar determinant characters from the nearby non-scalar type. The [positive-frame example](receipt-archives/2026-11-23-model-projection.md#unresolved) tests the operation on two representatives. The next question is the precision of the derivative after a digit carry.
