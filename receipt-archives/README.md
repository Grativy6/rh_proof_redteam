# Reproduce the audit

The original proof is pinned to commit `40e56bab026552e089d7afcfeff08d2defb9c005` of `leanprover-community/riemann-hypothesis`, using Lean 4.33.1. The controls in this directory are standalone theorems checked separately with Lean 4.32.1 and Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`. [Audit](2026-11-23-proof-audit.md) · [Evidence inventory](MAP.md)

### Compare the Lean checks

The [side-by-side receipt](2026-11-24-lean-check-comparison.md) contains the four reproduction steps for the corpus, RH endpoint metadata and a shared matrix lemma. The [full source theorem inventory](2026-11-24-corpus-theorem-axioms.jsonl) gives each inferred proposition, source line, and axiom set by toolchain. [Pins and file outcomes](2026-11-24-lean-comparison.json)

The [statement-level census](2026-11-24-assumptions-before-the-proof.md) gives the axiom names already present in the type, the [RH premise reversal](ZetaHalfPlaneCut.lean), and Chris’s [APCI blank-slot joke](IUsedLeanToProveRH.lean). The [integral-frame test](2026-11-24-integral-spectral-frame.md) and [inert transfer calculation](2026-11-24-three-colliding-eigenlines.md) use the corpus’s collision criterion on the arithmetic. Run `python check_inert_spectral_frames.py` from this directory to enumerate the local examples.

The [pole experiment](2026-11-24-value-at-the-zeta-pole.md) checks an actual use of the assigned value at 1. On the same proof route the [tail estimate](2026-11-24-log-window-tail.md), [prime readouts](2026-11-24-prime-pair-readouts.md), and [cross-modulus proof](2026-11-24-one-exception-across-moduli.md) work from the given analytic and arithmetic objects. Run `python check_prime_window_readouts.py` here for the prime certificates, finite differences and CRT control.

The [dyadic counterexample](2026-11-24-dyadic-class-enters-late.md) gives the exact finite input, the number-field class and the threshold used downstream. Run `python check_dyadic_window_class.py` from this directory to check the prime, scale and finite cocycles. [Survival through the tower](2026-11-24-dyadic-class-in-the-tower.md) and the [independent relative prime estimate](2026-11-24-relative-prime-count.md) give the neighboring checks.

For Chris’s [P versus NP double feature](2026-11-24-p-vs-np-double-feature.md), the [prebuilt inputs](p-vs-np-comparator-exports.tar.xz) go directly to the exported-statement judge. The [source runner](replay_p_vs_np.py) can also rebuild the inputs from the pinned definitions.

The [joint rank-three replay](2026-11-24-one-hecke-line-at-571.md) includes the integer Hecke operators, a compressed subspace witness and an independent full-rank certificate. The [positive trace calculation](2026-11-24-two-ramified-hecke-fields.md) explains the half-valuation, and the [global comparison](2026-11-24-global-residual-character-at-571.md) links the weight-two modular-symbol and [quintic checks](2026-11-24-quintic-check-for-the-even-alternative.md) used to identify the residue.

For the [order-five calculation](2026-11-24-an-order-five-class-and-a-hundred-missing-levels.md), run `python -B receipt-archives/check_odd_selmer_precision.py`. The [rank-two exclusion](2026-11-24-the-rank-two-alternative-at-571.md) and [rank-three test](2026-11-24-which-rank-three-representations-remain.md) use its modular coefficients and Bernoulli sum. PARI/GP runs the independent checks with `gp -fq receipt-archives/check_odd_class_fields.gp`. The [split Hecke row](2026-11-24-directed-hecke-test-at-level-571.md) and both dimensions replay with `python -B receipt-archives/check_unitary_level_571.py`.

The [twisted-norm collision](2026-11-24-when-minus-eighty-erases-a-class.md) identifies a real kernel element and accounts for its cost. Run `python check_twisted_norm_readouts.py` for the [changing prime witnesses](2026-11-24-every-place-splits-in-the-limit.md), `python check_tower_centres.py` for the [abstract controls](2026-11-24-fixed-centres-and-exceptional-twists.md), and `python check_dyadic_L_values.py` for the [measured arithmetic lengths](2026-11-24-dyadic-lengths-on-the-actual-fields.md). The optional `gp -fq check_small_norm_kernel.gp` certifies the small field’s exact kernel size and checks the two base logarithmic class groups.

### Verify the sources

Run `python receipt-archives/check_coupled_type_residue.py` for the [terminal local matrix calculation](2026-11-23-coupled-type-prime-residue.md). The [expanded corpus](../corpus/README.md) has 40 source files. Run `python receipt-archives/check_corpus_sources.py --upstream` to check the direct public files and the two extracted package members. The optional `--shelf PATH` checks the ten author-supplied records against an original Corpus folder.

Run `python receipt-archives/check_unitary_row_phases.py` for the [mixed row](2026-11-23-unitary-phase-with-fixed-directions.md), [negative finite triangle](2026-11-23-phase-around-three-lattices.md), [excluded coset lift](2026-11-23-coset-jets-over-one-field.md) and [coefficient-field conjugation](2026-11-23-conjugation-in-the-height-field.md). It also evaluates a 1,250-term Jacobi average independently. Run `python receipt-archives/check_theta_jet_height.py` for [level refinement and the determinant derivative](2026-11-23-gaussian-bound-for-the-jet-operator.md).

Run `python receipt-archives/check_theta_lattice_transport.py` for the [fourfold average](2026-11-23-fourfold-theta-lattice.md), [divided torsion lifts](2026-11-23-theta-transport-at-a-place.md), [CM class means](2026-11-23-theta-height-at-the-cusp.md) and [phase of a moved row](2026-11-23-phase-of-a-moved-theta-row.md). The finite character and subgroup checks are exact. The script also evaluates Jacobi sums directly and compares two numerical formulas for each class mean.

The [independence review](2026-11-23-independent-theta-check.md) applies the [working corpus](../corpus/README.md) to the disappearing tail. Run `python receipt-archives/check_theta_paper_examples.py` for its finite arithmetic and `python receipt-archives/check_corpus_sources.py` for source identities. The [Windows replay receipt](2026-11-23-windows-checker-report.md) gives the exact 4.35.0 reproduction and the 4.33.1 comparison.

The [determinant-class selector](2026-11-23-hecke-class-factor.md) finds an integral Hecke root, identifies the residual support ideal and gives a resultant bound when residual roots collide. Run `python receipt-archives/check_determinant_class_selector.py` for exact root and factor lifting on finite orbits.

The [fixed-level calculation](2026-11-23-fixed-level-theta-congruences.md) and the [unramified determinant calculation](2026-11-23-unramified-determinant-classes.md) track two costs into the localized Hecke lengths. Run `python receipt-archives/check_fixed_level_theta_congruences.py` for the colliding Satake roots, two finite marking coordinates and the quadratic ideal of order three.

The [split Hecke calculation](2026-11-23-good-bad-hecke-eigenvalues.md) derives the integral image on a family of row eigenforms. A cyclic group of order 25 checks the denominator by hand. The [raw theta calculation](2026-11-23-raw-theta-integral-image.md) follows their preimages to the fixed larger level, evaluates the actual class-sum denominators and gives a two-coordinate test of the remaining loss.

The [modular overlap calculation](2026-11-23-good-bad-modular-overlap.md) gives the congruence depths on cyclic products inside the row lattice. Run `python receipt-archives/check_good_bad_congruence_block.py` to reproduce the elementary divisors and two-place intersection example.

The [good-type spectral cut](2026-11-23-good-type-spectral-denominator.md) follows the rank estimate and the integral projection to the same row lattice. Run `python receipt-archives/check_spectral_cut_denominator.py` for the finite square-class count and the Fourier coefficient whose diagonal hides 11.

The [retraction norm calculation](2026-11-23-integral-retraction-norm.md) determines the exact geometric orbit and proves a bound for any tilt using the same Petersson norms and the denominator ideal. Its two-sample calculation is verifiable in the real quadratic subfield.

The [character trace on cusp components](2026-11-23-level-trace-on-cusp-components.md) and the [ray field over the exact core](2026-11-23-core-ray-intersection.md) test the two return maps at the selected level. Run `python receipt-archives/check_deep_level_traces.py` to verify the local-unit kernels, component cut and prime-order examples.

The [deep-cover ray field](2026-11-23-deep-cover-ray-field.md) gives the exact degree and root discriminant of the ray field selected in construction. Its numerical example includes the reduced-form counts and the modulus so the degree can be checked by hand.

The [window trace and slope](2026-11-23-window-trace-and-integrality.md), [small-section limits](2026-11-23-field-and-section-count.md) and [level stabilizers](2026-11-23-ramified-level-stabilizers.md) follow the field into lattice counts and descent. Run `python receipt-archives/check_cyclotomic_counts.py` to reproduce the finite checks of the Gauss periods, prime-power Fourier identities and ramified frames.

The [window coefficient-field calculation](2026-11-23-window-coefficient-degree.md) proves a growing degree is forced on the trivial-character branch. Run `python receipt-archives/check_window_coefficient_degree.py` for the finite class and trace-frame controls.

The [conjugated theta series](2026-11-23-conjugated-theta-tail.md) gives a paper counterexample to transporting convergence from coefficient-field membership and an exact mean-square calculation on a thin torus. The [finite-place normalization](2026-11-23-vacuum-scalar-field.md) gives an exact minimum extension degree. Its [ideal calculation](check_vacuum_scalar.py) runs with standard-library Python.

The [arithmetic-map audit](2026-11-23-arithmetic-map-height.md) traces the frame and height through their common bilinear pairing. Run `python receipt-archives/check_arithmetic_map_height.py` from the repository root to reproduce the unit, finite frame and branching calculations.

[Gemini Neon’s archive](gemini-neon/README.md) contains the contributor’s reports, two numerical labs and pinned sources. The [manifest](gemini-neon/SOURCE-MANIFEST.tsv) identifies the original bytes. Hearthline’s [DARK review](2026-11-23-gemini-tail-review.md) includes [exact checks](check_gemini_tail.py) runnable with `python receipt-archives/check_gemini_tail.py` from the repository root.

For the [actual 891-class denominator loss](2026-11-23-partial-zeta-loss.md), run `python receipt-archives/check_partial_zeta_loss.py`. The standard-library check enumerates ideals and independently verifies the total zeta values. Add `--cm-certificate` with python-flint 0.9.0 installed to reconstruct the CM class polynomial using complex balls.

For the [Hecke boundary calculation](2026-11-23-toric-hecke-boundary.md), run `python receipt-archives/check_toric_boundary.py`. The checker encloses the principal class value with rational arithmetic and tests the local factors.

For the [positive CM derivatives](2026-11-23-toric-cm-derivatives.md), run `python receipt-archives/check_toric_derivatives.py`. It checks the raising formula term by term, both CM correction factors and sample coefficients at the theta cusps.

For the [glued slope](2026-11-23-aligned-lattice-slope.md), [place-selected grid](2026-11-23-selected-grid.md) and [mean valuation](2026-11-23-mean-valuation.md), run `python receipt-archives/check_selected_grid.py`. For the [34-class transform](2026-11-23-toric-fourier.md) and [actual CM denominators](2026-11-23-toric-cm-denominators.md), run `python receipt-archives/check_toric_fourier.py`. The receipts include the proofs for unbounded degrees and all cusps.

For the [rank-four mass](2026-11-23-hermitian-mass.md), run `python receipt-archives/check_hermitian_mass.py`. It counts norm-two vectors and neighbors, checks the two automorphism orders, and evaluates the ratios. To verify the catalog entries as well, pass `--class-table PATH` with [Kirschmer’s original archive](https://www.math.uni-bielefeld.de/~mkirschm/forms/res_herm.tar.bz2). For the [split-prime class count](2026-11-23-split-class-count.md), run `python receipt-archives/check_split_class_count.py`. The [indefinite-volume comparison](2026-11-23-indefinite-mass-volume.md) contains its mathematical calculation.

For the [rank after projection](2026-11-23-plane-test-rank.md), run `python receipt-archives/check_plane_test_rank.py`. It checks the basis in each coordinate weight and the finite rank bounds.

For the [two scalar projection tests](2026-11-23-scalar-projection.md), run `python receipt-archives/check_scalar_projection.py`. It compares direct polynomial expansions with the two factorial formulas and verifies the numerical budgets.

For the [derivative across a digit carry](2026-11-23-frame-derivative.md), run `python receipt-archives/check_frame_derivative.py`. It compares finite differences with polynomial coefficients, checks the determinant calculation at small sizes, and verifies the full example’s numerical hypotheses.

For the [large-prime plane test](2026-11-23-large-prime-plane.md), run `python receipt-archives/check_large_prime_plane.py`. For the [projection on two representatives](2026-11-23-model-projection.md), run `python receipt-archives/check_model_projection.py`.

For the [restricted plane determinant](2026-11-23-plane-determinant.md), run `python receipt-archives/check_plane_determinant.py`. It checks the factorial digit lifting and the valuation calculations.

For the [corrected trace test](2026-11-23-corrected-trace-test.md), run `python receipt-archives/check_corrected_trace_test.py`. It evaluates the actual factorials before and after substitution.

For the [trace denominator](2026-11-23-trace-denominator.md), run `python receipt-archives/check_trace_denominator.py`. The paper calculation gives the sharp cost for all symmetric powers.

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
