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

The quotient-covolume comparison uses a one-sided bound. Two live questions are how the actual lift fills a whole Hecke eigenspace and what forces the period to vanish on the kernel of the row projection. [Current return point](receipt-archives/2026-11-23-quotient-covolume.md#unresolved)
