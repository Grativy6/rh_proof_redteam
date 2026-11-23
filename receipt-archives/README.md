# Reproduce the audit

The original proof is pinned to commit `40e56bab026552e089d7afcfeff08d2defb9c005` of `leanprover-community/riemann-hypothesis`, using Lean 4.33.1. The controls in this directory are standalone theorems checked separately with Lean 4.32.1 and Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`. [Audit](2026-11-23-proof-audit.md) · [Evidence inventory](MAP.md)

### Verify the sources

For the [minor-product calculation](2026-11-23-minor-product-rank.md), run `python receipt-archives/check_minor_product_rank.py`. It expands the polynomials in both coordinate conventions. For the [segment collision](2026-11-23-segment-collision.md), run `python receipt-archives/check_segment_collision.py`. The latter verifies the numerical hypotheses and degree budgets with integers.

For the [exact higher-rank localiser order](2026-11-23-localiser-order.md), run `python receipt-archives/check_localiser_order.py`. It evaluates both exchanged minors for all 289 two-row graph matrices over the prime subfield.

The [edge-separation receipt](2026-11-23-edge-separation.md) proves the one-slot bound at every degree. Run `python receipt-archives/check_edge_separation.py` to check the two-slot example at all 289 competing points.

The [zero-chain proof](2026-11-23-zero-chain.md) can be checked on paper. For the [four-operator test](2026-11-23-correlated-places.md), run `python receipt-archives/check_correlated_places.py`. It computes the elementary divisors for both families, including the positive definite symmetric matrices.

For the [jet loss and polynomial frames](2026-11-23-jet-loss-and-frames.md), run `python receipt-archives/check_honda_jet_loss.py`. The proof gives equality at infinitely many orders.

For the [CM curve and quadratic correction](2026-11-23-height-two-coordinate.md), run `python receipt-archives/check_cm7_jets.py`. The [conjugated-phase test](2026-11-23-conjugated-phase.md) uses an explicit quartic and a finite ideal-class character.

The [formal-degree receipt](2026-11-23-formal-degree.md) evaluates real-place integrals by two one-row beta integrals, including an exact $U(2,2)$ example.

The [zero-part eigenvalue calculation](2026-11-23-zero-part-eigenvalue.md) gives two finite-group examples and the proof that relates their character dimensions to occupancy of a period block.

The [valuation-descent receipt](2026-11-23-valuation-descent.md) can be checked with a square root of 5, a quadratic nonsquare modulo 5 and a two-by-two determinant.

The [fixed downward test](2026-11-23-fixed-downward-test.md) includes a two-column example over the 3-adics and a proof using saturated lattices. All its calculations can be checked on paper.

The [downward residue](2026-11-23-downward-residue.md) gives a short matrix counterexample and a scaling proof for singular measures. Run `python receipt-archives/check_split_gram.py` to reproduce finite-ring checks for the [split Gram density](2026-11-23-split-gram-density.md).

For the [oscillator calculation](2026-11-23-oscillator-cancellation.md), run `python receipt-archives/check_oscillator_integral.py`. It compares the oscillator and disk models with exact fractions. The receipt gives a proof for all degrees.

The [period-on-quotient receipt](2026-11-23-period-on-quotient.md) gives an exact denominator example and a dimension bound proved by taking traces of orthogonal projections.

The [quotient-covolume calculation](2026-11-23-quotient-covolume.md) can be checked by multiplying three algebraic conjugates and testing a split prime of the Gaussian integers. The unbounded example has a separate proof in the same record.

For coefficient descent, run `python receipt-archives/check_coefficient_descent.py`. The [receipt](2026-11-23-coefficient-descent.md#reproduce-the-checks) includes the optional compiled-graph check and the proof of the arithmetic obstruction.

For Turn 2, run `python receipt-archives/check_mixed_estimates.py` for the independent integer checks. The [reproduction section](2026-11-23-mixed-estimates.md#7-artifacts) describes the original-release Lean and compiled-graph checks.

For the geometry work key, run `python receipt-archives/check_geometry_witness.py` to reproduce the degree calculation. The [Turn 1 commands](2026-11-23-geometry-witness.md#7-artifacts) add the compiled-graph check.

From the red-team repository, pass a Git checkout or bare mirror that contains the original commit. The script uses Python 3 and Git, reads the objects at that commit and verifies the SHA-256 of each selected file. It also accepts the original handoff ZIP as an optional second input. The ZIP is read in place.

```sh
python receipt-archives/check_sources.py /path/to/riemann-hypothesis
python receipt-archives/check_sources.py /path/to/riemann-hypothesis --handoff /path/to/RH_PAL_Research_Pack_2026-11-23.zip
```

The second command matched 374 handoff entries to 358 distinct release files. [Pinned identities](source-pins.json)

### Recheck the eight controls

In a built Mathlib checkout at the control revision above, elaborate the file using its absolute path.

```sh
lake env lean /path/to/rh_proof_redteam/receipt-archives/AuditControls.lean
```

For module replay, copy `AuditControls.lean` into a scratch directory. Use the same Lean executable and Mathlib library search path there. Compile it to `AuditControls.olean`, put that scratch directory on `LEAN_PATH` alongside the Mathlib libraries and invoke `leanchecker AuditControls`. The two commands for those last steps are below.

```sh
lean -o AuditControls.olean AuditControls.lean
leanchecker AuditControls
```

The recorded run prints the foundational axiom dependencies for all eight theorems. The seven additional APCI controls in the original handoff were rebuilt separately in this session and replayed. The [audit](2026-11-23-proof-audit.md#evidence-from-the-handoff) gives their scope. [Type-check run](lean-run-2026-11-23/manifest.json) · [Axiom output](lean-run-2026-11-23/stdout.txt)

Recorded by Hearthline on 23 November 2026 at Christopher D. Pang’s request.
