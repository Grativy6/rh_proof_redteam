# RH proof work key 01 — Can every arithmetic pairing vanish?

**Prepared on 23 November 2026 by Hearthline at Christopher D. Pang’s request.** The target is Levent Alpöge and Claude’s released proof of the Riemann Hypothesis. Chris authorized this public key and its first attempt. The starting red-team record is [the first audit](https://github.com/Grativy6/rh_proof_redteam/tree/d02ee086e9fcea163dfc33a5c2b4a823c7623b1a).

## Turn this key

> Try setting every pairing used in the height estimate to zero. Follow the maps into the rank or averaged estimate used to reach RH. Find an input on which the proof draws a false conclusion, or find the premise that excludes the input and show how it works.

In our Keyring a **key** records a question, the objects to use and what would settle this attempt. **Turning** it means doing the mathematics. The **receipt** records the outcome and gives the next reader a precise place to resume. A saved key carries context. Chris selects the work.

## Starting sources

- Use the 20 November release, commit `40e56bab026552e089d7afcfeff08d2defb9c005`. Read the endpoint and the height condition with its surrounding hypotheses. [RH endpoint](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L4) · [WordFacts](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean#L128-L133)
- Use PAL v2.4-M’s `M-INTERFACE-FIBER` card to name the information retained after a projection. Use the Riemann–Pang Ledger §§23–25 to ask whether contributions supported in unobserved coordinates can survive the aggregate bound. BRIDGE supplies the question about what the readout can see. Translate each idea into the release’s own maps and norms. [PAL v2.4](https://doi.org/10.5281/zenodo.22888036) · [Riemann–Pang Ledger](https://doi.org/10.5281/zenodo.21894278) · [Prior height derivation](receipt-archives/2026-11-23-proof-audit.md#eliminate-the-chosen-height)

## Object

Fix one admissible family member and its word-indexed pairings `D.div.Bk u`. For a nonzero pairing the measured map height is bounded above by a reported height. If the pairing is zero, that premise is false. We want to know what prevents the entire useful signal from being zero while the remaining data still qualify. The zero `iMj` in an auxiliary construction is a different map. Any proposed identification needs its source and target.

## Mechanism and missing implication

Separate the part of a matrix that records the arithmetic pairing from any added coordinates. Try to support the columns entirely in the added coordinates. Keep track of the domain dimension, rank, projection, normalization, and which bounds apply to a single word or to a sum over words. The decisive question is whether a consumer can extract a positive contribution from the arithmetic part of a family whose entire arithmetic part vanishes.

## Attack

1. Find the first consumer that controls the size or rank of the arithmetic projection. Write its hypotheses and conclusion with the strict inequalities intact.
2. Construct the smallest exact example in which the proposed loss occurs after one of those hypotheses is removed. Then put the hypothesis back and check whether the same example is admissible.
3. Follow the relevant hypotheses into the actual producer and the conclusion toward the RH route. If zero is legitimate for one word, test the family-wide argument. If an estimate blocks the all-zero family, record the inequality that does it. If the bridge remains unresolved, name the exact missing implication.

## First-session deliverable

Return a dated receipt with the **target, source state, object, work, result, failure information, artifacts, and next live question**. Give the word or family, the maps and the failed conclusion for any proposed counterexample. Record finite arithmetic controls with their tested range. A source-level obstruction earns a result for that step. A claim against the whole proof also needs a dependency on the path to `riemannHypothesis`.

## Unresolved

At preparation time the nonzero-word height requirement and its zero branch are located. The unsettled question is how much of the aggregate contribution can disappear into the added coordinates. The dated receipt will carry any disposition of that question.
