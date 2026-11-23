# Evidence inventory

## Human notes

Chris supplied a separate research pack on 23 November 2026. Its digest and the four source-manifest names are recorded in the source pins.

| Record | Use |
| --- | --- |
| [Restricted plane determinant](2026-11-23-plane-determinant.md) · [Factorial and cofactor check](check_plane_determinant.py) | Detecting the vector on its exact type fails at arbitrary precision. The one-unit weight relaxation meets the local conclusion. |
| [The corrected trace test](2026-11-23-corrected-trace-test.md) · [Factorial pairing check](check_corrected_trace_test.py) | Exact cancellation on the selected line, a primitive component outside it, and a lower bound on the weight allowance. |
| [The trace denominator](2026-11-23-trace-denominator.md) · [Exact valuation check](check_trace_denominator.py) | The cost in the actual endomorphism lattice, a family attaining the bound in every rank, and the accumulation of loss over nested projections. |
| [Minor products](2026-11-23-minor-product-rank.md) · [Smith computation](check_minor_product_rank.py) · [Segment collision](2026-11-23-segment-collision.md) · [Degree check](check_segment_collision.py) | An exact family of integral rank losses and a many-to-one substitution at fixed degree, with the restrictions used by the released count. |
| [Exact order on graph planes](2026-11-23-localiser-order.md) · [Scalar evaluations](check_localiser_order.py) | A single competing plane forces the uniform bound down to one. The release takes the required power of its polynomial. |
| [Degree required to separate one lattice edge](2026-11-23-edge-separation.md) · [Complete finite-field test](check_edge_separation.py) | A sharp obstruction to the local rank predicate on binary forms, and the exact cost of separating a residue point with several Frobenius slots. |
| [The zero chain](2026-11-23-zero-chain.md) · [Four correlated places](2026-11-23-correlated-places.md) · [Exact lattice calculation](check_correlated_places.py) | A literal zero substitution, its precise arithmetic limit, and an index bound that fails with individual rank controls alone. |
| [A sharp jet loss and finite-field frames](2026-11-23-jet-loss-and-frames.md) · [exact derivative check](check_honda_jet_loss.py) | An all-orders extremal family and a polynomial whose coefficients lose fewer powers of the prime than all its evaluations in a fixed unramified field. |
| [CM formal coordinate and theta correction](2026-11-23-height-two-coordinate.md) · [exact series check](check_cm7_jets.py) | A forced denominator in the original field, an all-degree coordinate over a finite extension, and the unique quadratic correction for a discriminant $-7$ curve. |
| [Conjugating the phase](2026-11-23-conjugated-phase.md) | A Salem-unit counterexample, the finite class character, a common phase on the class sum and a reduced-test evaluation. |
| [The normalized formal degree](2026-11-23-formal-degree.md) | Haar normalization, cancellation of the factorials, direct matrix-ball integrals, and a multiplicity counterexample. |
| [Written-in eigenvalue on a vacant block](2026-11-23-zero-part-eigenvalue.md) | Actual assignment, its two level flags, the multiplicity-one condition and a check for all nonzero column labels. |
| [Rational and integral valuation descent](2026-11-23-valuation-descent.md) | Two lattices with identical rational preimages, an unbounded determinant discrepancy and the denominator of the base period. |
| [The fixed downward test](2026-11-23-fixed-downward-test.md) | Character conjugation, the congruence subgroup, a missed full-rank point and the finite set of translates for all observers. |
| [The downward theta residue](2026-11-23-downward-residue.md) | Checks the separate injectivity obligation, the location of its pole and the measure of singular frames. |
| [Split Gram density](2026-11-23-split-gram-density.md) · [finite counts](check_split_gram.py) | Exact density in the release dimension, failure one row below it and finite-set normalization. |
| [Oscillator cancellation](2026-11-23-oscillator-cancellation.md) · [exact-arithmetic check](check_oscillator_integral.py) | A nonharmonic zero, the full rank-one kernel, and the higher-rank radial and compact tests. |
| [Does the period survive the quotient?](2026-11-23-period-on-quotient.md) | Integral-image and kernel tests, an aggregate bound on erased dimensions, and the common target unitary. |
| [Quotient covolume and conjugate places](2026-11-23-quotient-covolume.md) | Rank-one counterexample to a uniform equality, proof of its sign in the actual bound, and the paired-prime test over the Gaussian integers. |
| [Coefficient descent and the integral period](2026-11-23-coefficient-descent.md) · [exact finite and graph checks](check_coefficient_descent.py) | A nonzero input lost by descent, the field condition on the theta operator, and a nonprincipal line with an exact index of three. |
| [Work key 01, second turn](2026-11-23-mixed-estimates.md) | Countertheorem for the selected builder, on-path mixed-degree calculations, and the point where the proof branches meet. |
| [General builder proof](GeneralFlagGrowth.lean) · [fixed flags and polarization](FlagGrowth.lean) · [native replay record](turn-02-native/kernel.json) | Actual release types, fixed example and universal obstruction. |
| [Exact and graph checks](check_mixed_estimates.py) · [compiled-term reader](InspectIntersection.lean) · [returned values](2026-11-23-mixed-check.json) | Run the arithmetic separately or inspect the published graphs and module files. |
| [Work key 01, first turn](2026-11-23-geometry-witness.md) | Exact mixed-intersection and surface-record counterexamples. Corrected RH-path locators for the earlier geometry reading. |
| [Geometry check](check_geometry_witness.py) and [result](2026-11-23-geometry-check.json) | Integer coefficient calculation and a bounded comparison of the full and RH-reachable compiled graphs with the release source. |
| [23 November audit](2026-11-23-proof-audit.md) | Claims, countermodels, source locators and the outstanding arithmetic question. |
| [Source pins](source-pins.json) and [source verifier](check_sources.py) | Verify original release blobs and optionally reconcile the supplied handoff. |
| [Audit controls](AuditControls.lean) | Eight Lean theorems concerning height feasibility, a zero map, quantifiers, witnesses, finite prefixes and extended length. |
| [Handoff reconciliation and kernel replays](2026-11-23-replay.json) | Independently rerun module checks, finite diagnostic counts and input identities. |
| [Native run manifest](lean-run-2026-11-23/manifest.json) and [output](lean-run-2026-11-23/stdout.txt) | Recorded type-check of the eight controls. |
| [Reproduction instructions](README.md) | Environment, commands and versions. |

Recorded by Hearthline on 23 November 2026 under Christopher D. Pang’s public red-team request.

## Unresolved

The [fixed downward test](2026-11-23-fixed-downward-test.md#unresolved) follows the two questions left by the [downward residue](2026-11-23-downward-residue.md#unresolved). The [oscillator receipt](2026-11-23-oscillator-cancellation.md#unresolved) records the analytic test reached from the [period receipt](2026-11-23-period-on-quotient.md#unresolved) and [quotient-covolume receipt](2026-11-23-quotient-covolume.md#unresolved). The [coefficient-descent receipt](2026-11-23-coefficient-descent.md#unresolved) gives the preceding lattice question and the outcome of the [cusp-form comparison](2026-11-23-mixed-estimates.md#8-next-live-question). The earlier mixed-call question is preserved in [Turn 1](2026-11-23-geometry-witness.md#8-next-live-question).

The [CM coordinate](2026-11-23-height-two-coordinate.md#unresolved) leads to the [jet and frame test](2026-11-23-jet-loss-and-frames.md#unresolved) and the [cost of the threshold rejection](2026-11-23-zero-chain.md#a-prime-whose-selected-orbit-set-is-empty). The [four-place example](2026-11-23-correlated-places.md#unresolved) led to the [one- and multiple-slot edge tests](2026-11-23-edge-separation.md#unresolved) and the [exact higher-rank order](2026-11-23-localiser-order.md#unresolved). The [product](2026-11-23-minor-product-rank.md#unresolved) and [segment](2026-11-23-segment-collision.md#unresolved) calculations trace what happens to rank across the subsequent maps. The [trace denominator](2026-11-23-trace-denominator.md#unresolved) tests the passage to rational components. The [corrected test](2026-11-23-corrected-trace-test.md#unresolved) traces the component after assembly. The [restricted determinant](2026-11-23-plane-determinant.md#unresolved) tests the ensuing plane bound. The [conjugated-phase receipt](2026-11-23-conjugated-phase.md#unresolved) tests the change of embedding in the global pairing. The [eigenvalue convention](2026-11-23-zero-part-eigenvalue.md#unresolved) leads to the [formal degree on occupied blocks](2026-11-23-formal-degree.md#unresolved). The [valuation receipt](2026-11-23-valuation-descent.md#unresolved) traces the arithmetic half of the pair of bounds in the [first audit](2026-11-23-proof-audit.md#unresolved).
