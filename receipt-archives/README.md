# Reproduce the audit

The original proof is pinned to commit `40e56bab026552e089d7afcfeff08d2defb9c005` of `leanprover-community/riemann-hypothesis`, using Lean 4.33.1. The controls in this directory are standalone theorems checked separately with Lean 4.32.1 and Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`. [Audit](2026-11-23-proof-audit.md) · [Evidence inventory](MAP.md)

### Test an exact theta zero and the two-digit rank

Run `python -B check_theta_orbit_and_digits.py` here. It uses the Python standard library and the existing `check_e8_theta_refinement.py` in this directory. The script checks the orbit matrix, energy bounds, first unmatched shell, 28-dimensional residue calculation and integer determinant $-3456$. The [paper proof of the exact zero](2026-11-24-a-zero-theta-sum-on-the-supported-lattice-orbit.md) gives the convergent series and Hensel estimate. [Four entries](2026-11-24-the-determinant-inside-the-disappearing-sum.md) · [Rank proof and determinant certificate](2026-11-24-how-many-theta-directions-the-second-digit-recovers.md) · [Wild and prime-to-$p$ symmetries](2026-11-24-what-exact-symmetry-earns-at-a-ramified-prime.md)

### Refine two genuine theta coefficients

Run `python -B check_e8_theta_refinement.py` here for the 240 roots, tied minima, finite-field residues and second binary digit. Run `python -B check_theta_descent_bounds.py` for the short labels, compatible tables, singular surface and blowup tests. Both use the Python standard library. [Theta series](2026-11-24-when-the-golden-unit-changes-a-genuine-theta-term.md) · [Field of values](2026-11-24-what-compatible-theta-sums-recover.md) · [Ramification cost](2026-11-24-the-ramification-cost-in-divisor-descent.md) · [Which traits detect a divisor](2026-11-24-which-traits-detect-a-divisor-at-a-singular-point.md)

### Check the golden angle and the two tied lattice terms

Run `python -B check_golden_carry.py` here. Its integer calculations check the six-sector carry, Fibonacci near-returns, the golden-ratio unit, and the two leading lattice points. The [receipt](2026-11-24-the-golden-angle-and-the-unit-in-the-lattice-sum.md) locates both the source’s actual residue substitution and the sign in its square-root cover.

### Test the ordinary flags at the moving primes

Run `python -B check_moving_prime_flags.py` here. It checks both splitting types at $q$, the forced residue degree two at $d$, and the first differing local Frobenius digit. The [paper calculation](2026-11-24-when-a-moving-prime-can-hide-a-linked-flag.md) proves the count for every sufficiently late page and gives the hypothesis required for the global unlinking argument.

### Count the strict 577-classes across the dyadic tower

Run `python -B fixed-character-577/dyadic_conductors.py` and `python -B fixed-character-577/dyadic_local_digits.py` here with NumPy. The first program compares direct CRT and periodic evaluations covering arbitrarily high conductors. The second prints the local readings for the 27 remaining character and twist pairs at two Jacobi primes. [Tower and source comparison](2026-11-24-one-strict-class-in-the-entire-real-dyadic-tower.md) · [Divisor and local proof](2026-11-24-which-of-the-27-class-group-directions-split.md)

### Reassemble the modulus-one branch

From this directory run `python -B check_rhofall_reassembly.py`. It reuses the two certified prime pairs, checks the signed row and its inverse on prime powers including both ramified primes, and computes three exact quadratic values at $-2$. The [four-character calculation](2026-11-24-taking-rhofall-apart-at-the-four-characters.md) includes a PARI/GP cross-check. The [two-page calculation](2026-11-24-two-dyadic-pages-behind-one-prime-sum.md) gives the corresponding field comparison and identifies the negative sign on an existing order-577 class. The same script checks the rational estimates in the [two-prime budget counterexample](2026-11-24-two-primes-break-one-window-budget.md).

### Replay the norm and lattice tests

From this directory, `python -B check_host_norm_defect.py` checks 31, the finite norm obstruction and the two genus means. `python -B boundary-577/dyadic_point_field.py` verifies the 579-bit prime certificate, the explicit second strict class and its level-seven corner obstruction. Both use the Python standard library. [Norms](2026-11-24-the-local-norm-that-does-not-compose.md) · [Self-dual lattice](2026-11-24-the-self-dual-lattice-with-no-unit-vector.md) · [Explicit point field](2026-11-24-the-dyadic-ideal-of-order-577.md)

For the original 577 input, run `python -B boundary-577/first_order_norms.py`, `python -B boundary-577/real_norm_units.py` and `python -B boundary-577/wild_unit_norms.py` with NumPy. The [comparison-field receipt](2026-11-24-two-opposite-ideal-class-readings-at-577.md#reproduce) gives the optional independent Jacobi histogram replay. [Minimum quotient rank](2026-11-24-which-norm-tests-see-the-cube.md) · [Four norm tests](2026-11-24-four-norm-kernels-for-the-two-quadratics.md) · [Base-unit coefficients](2026-11-24-two-real-unit-norm-targets-at-577.md)

Run `python -B boundary-577/cyclic_norm_moments.py` to check all 577 local parameters, the four changes of a local reading and the 183 + 394 norm-one control. [Cyclic equations and proof](2026-11-24-cyclic-norm-equations-and-the-missing-divisors.md)

The [X-files comparison](2026-11-24-the-x-files-model-and-the-actual-rank-cut.md) gives the pinned external sources, the arithmetic check of the discarded rank, and the surviving geometric question. The earlier spectral-projector replay is linked there.

For the two small-prime tests, run `python -B boundary-577/central_unit_residues.py` with NumPy. The [derivation](2026-11-24-two-small-primes-read-the-actual-point-units.md#reproduce) includes instructions for rebuilding the nine comparison rows using C++17. The same replay checks the two-prime deformation matrix and all 577 twist residues of the cyclic base-change example. The nine comparison rows were rebuilt with g++ 13.3.0, Python 3.12.14 and NumPy 2.3.5.

With NumPy, run `python -B boundary-577/norm_input_coordinates.py` for the support divisor and the Jacobi coordinate, `python -B boundary-577/ramified_norm_depths.py` for the local lifts, and `python -B boundary-577/point_unit_norms.py` for the two actual unit classes and the test of 576 linear factors. [Support](2026-11-24-the-576-primes-of-the-two-norm-targets.md) · [Local norm](2026-11-24-a-local-norm-with-a-nonintegral-logarithm.md) · [Point-field units](2026-11-24-two-units-in-the-degree-577-point-field.md)

All three replays completed on 24 November 2026 using Python 3.12.14 and NumPy 2.3.5. Fresh copies of their source dependencies gave the same results. PARI/GP 2.15.4 supplied separate checks of the relative minimal polynomial and the held-out residue matrix.

### Replay the local match and the global distinction

From this directory, run `python -B boundary-577/unramified_layers.py` for the four base characters and the **0 versus 457** test. Run `python -B boundary-577/artin_units.py` for the nine local readings and discriminants, `python -B boundary-577/hilbert_reciprocity.py` for the independent local and finite-prime symbol calculations, `python -B boundary-577/quadratic_words.py` for the second-order brackets and raw trace derivatives, and `python -B boundary-577/trace_powers.py` for their two surviving squares. All five use Python and NumPy. [Ideal-class argument](2026-11-24-the-unramified-character-that-local-data-miss.md) · [Local unit normalization](2026-11-24-four-local-units-at-577.md) · [Raw trace test](2026-11-24-two-raw-traces-on-the-released-subgroup.md)

### Check the order-577 class through the next digit

From this directory, run `python -B boundary-577/local_gap.py` with NumPy to check the six local readings, the two-prime matrix and the tame errors. The [local power calculation](2026-11-24-the-last-577th-power-digit.md#reproduce-the-computation) gives the C++ and independent GMP commands that rebuild its inputs. For the cyclotomic weights, run `python -B boundary-577/center_digits.py` with the Python standard library. Adding `--direct 3` repeats the third-level zero by direct enumeration. [Weight computation](2026-11-24-the-cyclotomic-module-of-the-fixed-class.md#locate-the-relaxed-center-by-finite-sums)

The [dual characters](2026-11-24-two-independent-obstruction-primes.md), [affine field class groups](2026-11-24-the-affine-resolvent-and-its-class-groups.md) and [nonsplit obstruction](2026-11-24-the-obstruction-at-the-nonsplit-point.md) give the derivations and individual replays. Hearthline prepared these under Chris Pang’s continuing public audit request on 24 November 2026.

### Compare the Lean checks

The [side-by-side receipt](2026-11-24-lean-check-comparison.md) contains the four reproduction steps for the corpus, RH endpoint metadata and a shared matrix lemma. The [full source theorem inventory](2026-11-24-corpus-theorem-axioms.jsonl) gives each inferred proposition, source line, and axiom set by toolchain. [Pins and file outcomes](2026-11-24-lean-comparison.json)

The [statement-level census](2026-11-24-assumptions-before-the-proof.md) gives the axiom names already present in the type, the [RH premise reversal](ZetaHalfPlaneCut.lean), and Chris’s [APCI blank-slot joke](IUsedLeanToProveRH.lean). The [integral-frame test](2026-11-24-integral-spectral-frame.md) and [inert transfer calculation](2026-11-24-three-colliding-eigenlines.md) use the corpus’s collision criterion on the arithmetic. Run `python check_inert_spectral_frames.py` from this directory to enumerate the local examples.

The [pole experiment](2026-11-24-value-at-the-zeta-pole.md) checks an actual use of the assigned value at 1. On the same proof route the [tail estimate](2026-11-24-log-window-tail.md), [prime readouts](2026-11-24-prime-pair-readouts.md), and [cross-modulus proof](2026-11-24-one-exception-across-moduli.md) work from the given analytic and arithmetic objects. Run `python check_prime_window_readouts.py` here for the prime certificates, finite differences and CRT control.

The [dyadic counterexample](2026-11-24-dyadic-class-enters-late.md) gives the exact finite input, the number-field class and the threshold used downstream. Run `python check_dyadic_window_class.py` from this directory to check the prime, scale and finite cocycles. [Survival through the tower](2026-11-24-dyadic-class-in-the-tower.md) and the [independent relative prime estimate](2026-11-24-relative-prime-count.md) give the neighboring checks.

For Chris’s [P versus NP double feature](2026-11-24-p-vs-np-double-feature.md), the [prebuilt inputs](p-vs-np-comparator-exports.tar.xz) go directly to the exported-statement judge. The [source runner](replay_p_vs_np.py) can also rebuild the inputs from the pinned definitions.

For the [marked directions](2026-11-24-three-deformation-directions-at-577.md) run `python -B residual_directions.py` from `receipt-archives/marked-directions-577`. In that directory `python -B matrix_checks.py` and `python -B two_words.py` check the [ramification test](2026-11-24-why-the-trace-field-must-ramify.md). The command `python -B auxiliary_constant.py` checks the [auxiliary digits](2026-11-24-one-ramified-digit-at-the-auxiliary-prime.md). The independent PARI controls are `gp -fq upper_local.gp` and `gp -fq rank_floor.gp`.

The [conductor-256 witness](2026-11-24-the-577-class-on-paper.md) can be replayed from `fixed-character-577` with `python -B fourier_witness.py`, `python -B bounds.py`, and `python -B group_ring_witness.py`. The [discovery search](fixed-character-577/find_characters.py) is optional. The [full twist calculation](2026-11-24-all-odd-twists-at-two-conductors.md) also gives the separate FLINT and PARI replay at conductor 106619.

The [order-25 replay](2026-11-24-two-classes-of-order-twenty-five.md) checks six host primes with standard-library Python. For both exact upper bounds use the [divisor and local power tests](2026-11-24-why-the-classes-stop-at-twenty-five.md). In the same calculation directory run `python -B check_weight_two.py` for the two signed modular-symbol computations at 2179, and `python -B unitary_106619.py` for the [two directed rows and their joint test](2026-11-24-where-the-adjoint-disappears.md) at 106619. Those two scripts need NumPy. The [marked-point argument and tangent sign](2026-11-24-the-two-tangent-signs.md) can be checked on paper.

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
