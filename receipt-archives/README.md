# Reproduce the audit

The original proof is pinned to commit `40e56bab026552e089d7afcfeff08d2defb9c005` of `leanprover-community/riemann-hypothesis`, using Lean 4.33.1. The controls in this directory are standalone theorems checked separately with Lean 4.32.1 and Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`. [Audit](2026-11-23-proof-audit.md) · [Evidence inventory](MAP.md)

For the proofs in reading order, start with the [front collection](../proofs/README.md). Its [contribution record](../proofs/PROVENANCE.md) links the independently registered Pang corpus editions to the dated proof receipts.

### Replay the constructive RH calculation

For the [fixed one-thirteenth comparison](../proofs/one-thirteenth-of-a-returned-layer.md), run `python -B receipt-archives/check_pal_returned_horizon.py`. It returns the largest measured discrepancies and their cuts, and encloses all elementary constants rationally. [Direct ranges and both theorem comparisons](2026-11-26-pal-returned-horizon.json)

The [two separate signs](../proofs/why-either-side-of-the-pocket-is-enough.md) now have a fixed challenge for excess alone, shortage alone, and an actual deadline-respecting family of injections. [Build, independent exports, kernels and bare comparison](2026-11-26-pal-signed-pocket.json)

For [expiring gap credit](../proofs/how-long-prime-gap-credit-must-survive.md), run `python -B receipt-archives/check_pal_expiring_gap_credit.py --show-partitions`. The output gives the two optimum block caps at each active head and all boundaries of one optimal partition for each transition. [Exact costs and pencil example](2026-11-26-pal-expiring-gaps.json)

For [the one-sided subset comparison](../proofs/one-integer-comparison-to-rh.md), run `python -B receipt-archives/check_pal_one_subset.py`. Prime-power readings and their logarithmic primitives are independently recomputed from all-integer log and harmonic sums. The same solution export was tested against two fixed statements. [Conditional acceptance and bare-statement mismatch](2026-11-26-pal-one-subset.json)

For [the unit tick lattice](../proofs/how-many-layers-a-prime-trip-needs.md), run `python -B receipt-archives/check_pal_tick_layers.py`. It computes two integer clocks, exhaustively recovers small complete cubes, decodes the middle-prime placement and tests all common size-four Pascal states. [Counts, ranges and fixed comparison](2026-11-26-pal-tick-layers.json)

For [the distance experiment](../proofs/how-far-a-prime-trip-must-move.md), run `python -B receipt-archives/check_pal_distance_transport.py` and `python -B receipt-archives/check_pal_prime_strip.py`. The first emits optimal assignments with one-column shortage witnesses. The second minimizes the worst error over every integer height and records the two cuts forcing failure. [Ranges, sources and replay](2026-11-26-pal-local-distance.json)

For [the Pascal construction](../proofs/two-pascal-rows-fit-on-every-board.md), run `python -B receipt-archives/check_pal_pascal_board.py`. It recovers every record at the first three sizes, compares individual binomial factors to prime carries, and prices the two orientations and the negative inventory at five. [Fixed comparisons, scopes and bounds](2026-11-26-pal-pascal-board.json)

For [the least cutoff and prime-pair calibration](../proofs/the-first-prime-a-board-has-to-give-up.md), run `python -B receipt-archives/check_pal_horizon_pairs.py`. It counts unordered prime pairs through selected roots up to 10,000, compares small cases to direct gcd readings, and encloses both spectral prices. [Finite scope and proof record](2026-11-26-pal-horizon-cut.json)

For [the factorial frame](../proofs/what-happens-when-the-sieve-forgets-five.md), run `python -B receipt-archives/check_pal_sieve_frame.py`. It tests both meanings of erasing five, checks the first failure, and reproduces the integer products, cutoff arithmetic and decoder controls. [Ranges and fixed statements](2026-11-26-pal-sieve-frame.json)

For [the fourth-power board](../proofs/which-prime-boards-have-to-fit.md), run `python -B receipt-archives/check_pal_board_intervals.py`. A segmented prime census and convex bounds certify full intervals through one billion. An independent division-quotient sieve counts the primes at the last head. [Integer bounds, ranges and fixed-target comparison](2026-11-26-pal-fourth-power-boards.json)

For the [signed factorial boundary](../proofs/what-the-signed-factorial-rows-leave-at-zero.md), run `python -B receipt-archives/check_pal_signed_factorials.py` and `python -B receipt-archives/check_pal_boundary_zero.py`. The first recovers the finite square weights and counts signed primes, squares and higher powers separately. The second encloses an actual critical zero and prices the missing reading. [Numbers and scope](2026-11-26-pal-signed-factorial-boundary.json)

For the [prime board](../proofs/how-much-room-the-prime-board-needs.md), run `python -B receipt-archives/check_pal_prime_board.py`. The default computes the integer allowance and paired rounding budget through 100,000, tests the full single-cell sequence through 5,000, and decodes every input at size three. Its second product comparison uses leading binary digits with explicit enclosures. [Products, ranges and fixed-target result](2026-11-26-pal-prime-board.json)

For [the Dyson doubling window](../proofs/what-one-doubling-hears-in-the-primes.md), run `python -B receipt-archives/check_pal_dyson_window.py`. It prices all prime powers for every root from 2 to 2663, independently recomputes selected small heads, encloses the diagonal without using a zero table, and checks the prime-square compensation through 99,999. Add `--divisor-control 2663` to recover the same large reading from the independent divisor-product recursion and decimal logarithm enclosures. [Numerators, bands and fixed analytic comparison](2026-11-26-pal-dyson-octave.json)

For the [square-root exposures](../proofs/what-can-move-inside-a-square-root-window.md), run `python -B receipt-archives/check_pal_square_exposure.py`. To recompute both native counts, compile `g++ -O3 -std=c++17 receipt-archives/square_shell_mass.cpp -o square_shell_mass` and pass `--native ./square_shell_mass` to the Python command. The native `squares 10000` mode independently emits consecutive shell readings. [Inputs, bounds and fixed integer challenges](2026-11-26-pal-square-exposure.json)

For the [adaptive trailing rows](../proofs/how-far-a-square-mark-must-reach.md), `python -B receipt-archives/check_pal_trailing_rows.py` rebuilds the two orientations and all 25,005 upper-envelope panels from the recorded native inputs. Compile `trailing_row_hull.cpp`, `trailing_spike.cpp` and `trailing_row_moments.cpp` in this directory with `g++ -O3 -std=c++17`. Run `./trailing_row_hull 50000000`, `./trailing_spike 72 1 5184 past` and `./trailing_spike 72 1 5184 future`. Rebuild the direct grid with `./trailing_row_moments 10000000000000 18000000 physical range 300 200001 > rows.tsv` and pass `--grid rows.tsv` to the Python command. The independent ordinary recurrence uses cutoff 21000000. The optional `bins 200000000` mode writes the recorded little-endian first-moment maxima to standard output. [Source hashes and results](2026-11-26-pal-trailing-rows.json)

For the [integer-cell comparison](../proofs/what-a-quotient-leaves-between-integers.md), `python -B receipt-archives/check_pal_cell_remainders.py` encloses every reconstructed step through 200,000, checks its factorization sign and square-gap allowance, and calculates the original division remainders independently at the listed heads. The run also prices every square through 200,000 and the separate root 2663. The four-decimal witnesses use integer square roots. [Full record](2026-11-26-pal-cell-remainders.json)

For the [terminal-window tests](../proofs/how-much-can-the-newest-half-gain.md), run `g++ -O3 -std=c++17 receipt-archives/terminal_window_counts.cpp -o terminal_window_counts`, then `./terminal_window_counts 50000000`. Run `python -B receipt-archives/check_pal_terminal_windows.py` to reconstruct all 25,005 larger panels, including each first unresolved sign. [Inputs and two kernel comparisons](2026-11-26-pal-terminal-windows.json)

For the [last-two-roots proof](../proofs/why-the-last-two-square-roots-remain.md), run `python -B receipt-archives/check_pal_dense_square_payment.py --counts receipt-archives/2026-11-26-pal-dense-squares.json`. This rebuilds the root capacities, first and second signed portions, and initial sign range. Rebuild the integer columns with `g++ -O3 -std=c++17 receipt-archives/dense_square_counts.cpp -o dense_square_counts` and run `./dense_square_counts 10000000000000 20000000 mobius 1 10`, then `./dense_square_counts 10000000000000 16000000 liouville 1 10`. The arguments select the head, sieve length, arithmetic direction and quotient indices. [Recorded native inputs and outputs](2026-11-26-pal-dense-squares.json)

For the [running-integer proof](../proofs/the-integer-that-turns-at-forty-four.md), `python -B receipt-archives/check_pal_signed_mass.py --ten-trillion` independently recomputes all 22,165 upper-envelope panels from the included little-endian ordinary bin maxima and the Lioen–van de Lune bound. `python -B receipt-archives/check_pal_rise_direction.py` replays the signed portion and compact divisor reader. To regenerate the maxima, compile `g++ -O3 -std=c++17 receipt-archives/signed_mass_envelope.cpp -o signed_mass_envelope` and run `./signed_mass_envelope 200000000 10000000000000 2048 maxima.bin`. For the independent physical quotient grid, compile `receipt-archives/physical_mass_grid.cpp` with the same flags, run it with arguments `32000000000000 30000000 400 160001`, then with `32000000000000 26000000 400 160001 --rough`. Save either output as `mass.tsv` and pass `--grid mass.tsv` to the Python replay. The optional `--terminal-binary /path/to/cubic_window_moments` independently rebuilds the final primitive and mass. The [record](2026-11-25-pal-running-mass.json) includes the fixed integer challenge, the exports and the scope of each finite input.

For the [physical primitive](../proofs/one-quantity-at-each-fourth-power.md), compile `g++ -O3 -std=c++17 receipt-archives/fourth_primitive.cpp -o fourth_primitive` and run `./fourth_primitive 100 > dense.json`, followed by `python -B receipt-archives/check_pal_fourth_primitive.py --scan dense.json`. Reprice every continuous panel from its saved endpoints with `python -B receipt-archives/check_pal_primitive_mesh.py --replay-record receipt-archives/2026-11-25-pal-one-head-primitive.json`. Use `--moments-binary /path/to/cubic_window_moments --work /path/to/scratch` instead to regenerate both quotient recurrences. After building the pinned project, `python -B receipt-archives/export_pal_configured_check.py pal-rh/checks/one-head/compare.json /path/to/exports` exports the isolated reference and solution. On the Linux judge run `lake comparator --config pal-rh/checks/one-head/compare.json --challenge-from-export /path/to/exports/challenge.ndjson --solution-from-export /path/to/exports/solution.ndjson`. [Finite endpoints and fixed-statement verdict](2026-11-25-pal-one-head-primitive.json)

Compile `g++ -O3 -std=c++17 receipt-archives/reference_obstruction.cpp -o reference_obstruction`, then run `./reference_obstruction 40000000 > inverse.json` and `python -B receipt-archives/check_pal_reference_prices.py --scan inverse.json`. Add `--primecount /path/to/primecount` to repeat the finite prime counts. [Directed endpoints, exact margin and signed partner](2026-11-25-pal-reference-price.json)

Run `python -B receipt-archives/check_pal_two_prime_carriers.py` to factor four complete fourth-power blocks, enclose all five moments and test the capacities of the two chosen prime supports. [Full-block record](2026-11-25-pal-two-prime-carriers.json)

For the [one-large-prime proof](../proofs/why-one-large-prime-leaves-nine.md), replay the small population directly with `python -B receipt-archives/check_pal_large_prime_surplus.py receipt-archives/large-prime-calibration.csv 89 --trial-division`. Recheck all six stored matrix systems with `python -B receipt-archives/check_pal_large_prime_surplus.py --replay-record receipt-archives/2026-11-25-pal-large-prime-surplus.json`. To regenerate the trillion-sector populations, compile `g++ -O3 -std=c++17 -fopenmp receipt-archives/large_prime_block.cpp -lprimesieve -lprimecount -o large_prime_block`, run `./large_prime_block 1600000000000 1666666666666 31622 100000 4 > sector.csv`, then run `python -B receipt-archives/check_pal_large_prime_surplus.py sector.csv 31622 --head 2000000000000`. The [record](2026-11-25-pal-large-prime-surplus.json) gives the corresponding inputs and population hashes for the other heads.

Run `python -B receipt-archives/count_pal_cell_signs.py` for the exact sign counts, then `python -B receipt-archives/check_pal_cofactor_block.py` for the four growing-cofactor examples, the 2663 reversal and both cross-cofactor allocations. Both scripts use the Python standard library. [Combined record](2026-11-25-pal-cell-prices.json)

Run `python -B receipt-archives/check_pal_prime_transport.py` to reconstruct the fractions and the full-sector percentages. To regenerate the counts with GCC and the development libraries, run `g++ -O3 -std=c++17 -fopenmp receipt-archives/prime_transport_counts.cpp -lprimecount -lprimesieve -o prime_transport_counts`, then `./prime_transport_counts 1600000000000 1666666666666 2000 347 4 > counts.csv`. The same command with arguments `1600000 1666666 100 347 4` produces a small calibration file. Pass it to the Python script as `--check-small-counts small.csv`. [Inputs, bounds and formal scope](2026-11-25-pal-prime-transport.json)

Run `python -B receipt-archives/check_pal_central_mirror.py` for the reciprocal polynomials, local coefficients and residue checks. The [record](2026-11-25-pal-central-mirror.json) identifies the range checked and the theorems in the normal project build.

Run `python -B receipt-archives/check_pal_clock_resonance.py` to enclose the zero and test its response to the stated square clocks. For the [residue windows](../pal-rh/what-a-reflected-remainder-carries.md), `python -B receipt-archives/check_pal_reflected_cells.py` runs the direct small cases. Appending the compiled `cubic_window_moments` binary described below also reproduces the trillion-scale angular sector and the twelfth-power panels. [Exact results](2026-11-25-pal-reflected-cells.json)

For the [fourth-power test and omitted-label calculation](../pal-rh/what-the-first-omitted-label-sees.md), run `python -B receipt-archives/check_pal_cubic_window.py` for the direct small cases. For the large cases build `g++ -O3 -std=c++17 receipt-archives/cubic_window_moments.cpp -o /tmp/cubic-window-moments` and run `python -B receipt-archives/check_pal_cubic_window.py /tmp/cubic-window-moments`. The two modular moment recurrences and directed reciprocal intervals run locally. [Results, ranges and compiler details](2026-11-25-pal-cubic-window.json)

Run `python -B receipt-archives/check_pal_square_pass.py` to reconstruct the original, each square rescaling alone and the full pass. It checks all half-rows from 1 through $2^{23}$ and directly sums the first negative row before and after the pass. [Exact bounds](2026-11-25-pal-square-pass.json) · [Derivation](../pal-rh/how-many-square-passes-the-sign-needs.md)

Run `python -B receipt-archives/check_pal_prime_renewal.py` to reconstruct both orders of the simple-prime calculation and the exact finite-grid prices. [Results and limits](2026-11-25-pal-prime-renewal.json) · [Mathematical account](../pal-rh/what-the-ordinary-primes-still-owe.md)

Run `python -B receipt-archives/check_pal_signed_areas.py` for the first integer sign reversal, both cumulative costs, the two independent integrals and the complex phase test. [Stage results](2026-11-25-pal-signed-areas.json) · [Derivation](../pal-rh/what-the-two-signs-cost-together.md)

For the independently posed conditional theorem, build the pinned project, run `python -B receipt-archives/export_pal_check.py fourths /path/to/exports`, then run Lake Comparator with `pal-rh/checks/fourths/compare.json` and the generated `fourths-challenge.ndjson` and `fourths-solution.ndjson`. The [stock-only reference](../pal-rh/checks/fourths/FourthChallenge.lean) spells out the rational data. The [solution](../pal-rh/checks/fourths/FourthSolution.lean) proves its price agrees with the branch’s original frame.

Run `python -B receipt-archives/check_pal_carried_edge.py` for the two-row reading, its neighboring-frame update, and directed enclosures at cubes and fourth powers. [Results and distinctions between finite and infinite claims](2026-11-25-pal-carried-edge.json)

Run `python -B receipt-archives/check_pal_tapered_newton.py` to reconstruct the balanced lists, price the first errors in both directions and enclose all-row and finite-square costs. [Results](2026-11-25-pal-tapered-newton.json) · [What the direction implies](../pal-rh/when-a-drop-would-count.md)

[Averaged square replay](2026-11-25-pal-smoothed-square.json) uses `python -B receipt-archives/check_pal_smoothed_square.py`. It includes the physical values, the backward second difference, the same assigned signs, and five direct Gaussian comparisons. [Paper and proof scope](../pal-rh/averaging-the-square.md)

The [square-boundary stage](2026-11-25-pal-square-boundary.json) uses `python -B receipt-archives/check_pal_core_squares.py` for the genuine Möbius values and `python -B receipt-archives/check_pal_boundary_packets.py` for the separate side-information counterexample. Both use the standard library. [Pencil-and-paper calculation](../pal-rh/the-signed-matrix-inside-a-square.md)

[Octave and square-window budgets](2026-11-25-pal-octave-growth.json) use `python -B receipt-archives/check_pal_growth_windows.py`. The [reader proof](../pal-rh/what-the-next-octave-costs.md) identifies the finite computations and the all-scale estimates.

[What 5 carries](../pal-rh/what-five-carries.md) has [one stage record](2026-11-25-pal-prime-flow.json). Run `python -B receipt-archives/check_pal_two_clock_flow.py` for the cutoff calculation, then `python -B receipt-archives/check_pal_exits.py` for all four infinite-interval bounds and both universal lower bounds. The separate [candidate selection](select_pal_exits.py) uses NumPy. The two mathematical checkers use the Python standard library.

[Two row-repair calculations](2026-11-25-pal-row-repair-and-parents.json) run with Python’s standard library. Use `python -B receipt-archives/check_pal_row_repair.py` for the rational fits and `python -B receipt-archives/check_pal_single_parent.py` for the missed wave.

[Strict successors on both targets](2026-11-25-pal-strict-successor.json) records the ordinary Lake build, replay command and hashes for the [paper argument](../pal-rh/every-fit-has-a-successor.md).

[First tick, sieve reversal and clock comparisons](2026-11-25-pal-first-tick-stage.md) includes the all-row rational runs for the two-way transfer and sequential improvements. Use `python -B receipt-archives/check_pal_first_tick.py` and `python -B receipt-archives/check_pal_close_clocks.py` from the repository root.

[Construction-key replay](2026-11-25-pal-construction-replay.md) gives the pinned target, clean build, rational comparisons, and independent statement/kernel runs. The [variable-prime checker](check_pal_prime_refits.py) uses only the Python standard library.

[Prime phases and the all-row bound](2026-11-25-pal-rh-rational-distance.md) gives the integer replay command and the formal theorem statements. [Standalone checker](check_pal_residue_distance.py)

### Check the two-row conductor identity

Run `python check_two_row_bernoulli_identity.py` here. It records coefficients separately for each residue and verifies that exactly twice one designated weight survives. The [proof](2026-11-25-two-rows-halve-the-bernoulli-conductor-cutoff.md) covers arbitrary odd conductor and includes an independent check of the release’s original shift. [Python](check_two_row_bernoulli_identity.py)

### Check the conductor cutoff at 17

Run `python check_seventeen_dyadic_cutoff.py` here to compare the original Bernoulli sums with the signed coefficients and enumerate the 64 row cases covering all high conductors. The [derivation](2026-11-25-the-order-seventeen-class-at-conductor-64.md) includes a separate PARI/GP check of the degree-16 class group and its Galois action. [Python](check_seventeen_dyadic_cutoff.py)

### Check simultaneous character readings and Frobenius powers

Run `python check_four_character_precision.py` and `gp -fq check_frobenius_centralizer_cost.gp` here. The first enumerates the four-point sets of the affine plane over the field of five elements and the first shared readings. The second independently ranks the truncated coefficient matrices through precision 13 and checks their Smith exponents. The [character proof](2026-11-25-the-centroid-that-hides-four-character-readings.md) and [matrix proof](2026-11-25-the-exact-cost-of-powering-a-frobenius-matrix.md) cover arbitrary precision. [Python](check_four_character_precision.py) · [PARI/GP](check_frobenius_centralizer_cost.gp)

### Check the class-group increments

Run `python check_auxiliary_class_tower.py` here. The standard-library calculation gives generalized Bernoulli norms for the first two layers at 11 and 211. The [derivation](2026-11-25-the-class-lifts-and-loses-its-inertia-symmetry.md) proves the all-layer lower bound and determines why every higher-precision lift loses inertia invariance. [Code](check_auxiliary_class_tower.py)

### Replay the auxiliary-prime calculation

Run `gp -fq check_auxiliary_prime_residue.gp` here with PARI/GP 2.15 or later. It checks the quintic identity, both residue fields at 11, the ray groups at 11 and 701, the class group after tame base change, and the Frobenius readings at 307 and 2663. The [general rank bound](2026-11-25-why-the-auxiliary-prime-loses-both-classes.md) and the [lifting obstruction](2026-11-25-a-fifth-power-at-eleven-and-the-missing-digit.md) include the proofs. [Calculation file](check_auxiliary_prime_residue.gp)

### Check the component equations and the trace kernel

Run `python -B check_component_and_dual_trace.py` from this archive. It checks the finite polynomial models, the tangent through two truncations, and the space of trace-zero derivations for block sizes two and one over two fields. The formal local and Galois conclusions are proved in the [component calculation](2026-11-25-two-determinant-tests-at-a-component-intersection.md) and the [trace proof](2026-11-25-the-trace-kernel-on-the-cyclotomic-subgroup.md). [Credits and digests](2026-11-25-proof-collection-component-supplement.json)

### Read the spherical-closure example

The [elliptic-curve comparison](2026-11-24-four-branch-points-and-the-primes-that-see-the-twist.md) gives the quotient differential, the exact residue classes of the distinguishing primes, a rank descent and a PARI/GP replay. The two original papers and their checksums are in the [corpus](../corpus/README.md#the-shadow-and-the-sphere).

### Replay the original 116-digit certificate and the ordinary-line tests

Run `python -B check_release_prime_large.py` for the Lucas certificates and the three prime values in the bounded quadratic-norm family. Add `--source PATH_TO_UPSTREAM_GIT_REPO` to repeat the original-source census. `python -B check_ordinary_congruence_levels.py` computes the Hecke matrices and the exact precision cutoffs. Both scripts use the standard library. [Upstream prime and its use](2026-11-24-the-three-prime-norms-up-to-the-released-example.md) · [Ordinary operator](2026-11-24-one-ordinary-line-through-all-congruence-levels.md) · [Same finite readings](2026-11-24-two-linked-flags-with-identical-finite-readings.md) · [Credits and digests](2026-11-24-proof-collection-prime-and-refinement-supplement.json)

### Check the coefficient prime 2663 on every real dyadic layer

Run `python -B check_prime_2663.py` here with NumPy. The two evaluations of the high-conductor norms give product 95 modulo 2663. Independent split-prime unit calculations treat the single small-conductor candidate and the principal character. [Proof](2026-11-24-what-prime-2663-does-in-the-real-dyadic-tower.md) · [Provenance and digests](2026-11-24-proof-collection-2663-supplement.json)

### Check the distinguished prime and the mixed traces

Run `python -B check_distinguished_prime.py` and `python -B check_irreducible_trace_words.py` from this directory. Both use the standard library. The first computes integral Smith factors, counts fixed flags and reconstructs spherical polynomials. The second ranks the complete trace-derivative matrix in the displayed three-generator example. [Projection](2026-11-24-the-integral-cost-of-the-distinguished-prime-projector.md) · [Packet and polynomial](2026-11-24-recovering-the-spherical-parameter-and-counting-an-occupied-packet.md) · [Finite word test](2026-11-24-finitely-many-word-traces-detect-an-irreducible-deformation.md) · [Attribution and digests](2026-11-24-proof-collection-arithmetic-supplement.json)

### Test the weighted triangle and the nonsplit carry

Run `python -B check_triangle_and_nonsplit_carry.py` here with the standard library and the neighboring E₈ check. It verifies the elliptic flex value in the 25-element residue field, counts the orders of all 81 points of the restricted polarization kernel, and compares the weighted triangle optima. [Triangle](2026-11-24-three-ways-to-read-the-nine-fourths-triangle.md) · [Nonsplit periods](2026-11-24-the-order-nine-carry-in-a-nonsplit-degeneration.md) · [Moving coefficient](2026-11-24-when-the-coefficient-and-the-good-torsion-point-move-together.md)

### Recover a marked metric and distinguish arithmetic actions

Run `python -B check_marked_lattice_and_torsion.py` here. It uses only the Python standard library and checks Gram recovery through rank four, a Hensel correction modulo $2^{324}$, the corrected torsion size bounds, fourfold action matrices and the integer face identities. [Doubling proof](2026-11-24-reconstructing-a-marked-lattice-by-doubling.md) · [Exact Fourier measurements](2026-11-24-the-torsion-reading-that-sees-through-the-zero.md) · [Mixed toric and good reduction](2026-11-24-a-theta-zero-at-every-toric-depth.md) · [Arithmetic action](2026-11-24-two-arithmetic-actions-indistinguishable-at-full-level.md) · [Fan limit](2026-11-24-the-golden-limit-and-the-rational-boundary.md) · [Supporting tuple](2026-11-24-an-explicit-support-for-the-zero-orbit.md)

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
