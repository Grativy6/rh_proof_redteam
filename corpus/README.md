# Corpus used in the RH proof audit

Chris Pang asked for the complete Context Stack alongside the sources already used in the public audit. The shelf holds 40 source files, including alternate reading formats, original packages, an illustration and prompt-version records. The earlier screen of 74 readings across nine shelves was a discovery pass. The table and worked examples identify which methods have been applied. [Source files and exact editions](MAP.md) · [Machine-readable provenance](sources.json)

The public formal projects have a [separate Lean comparison](../receipt-archives/2026-11-24-lean-check-comparison.md), including all seven current Context Parallax formal files. It records the exact propositions and assumptions the checkers read.

The same [APCI source](Interface.lean) produces a [literal blank-slot control](../receipt-archives/IUsedLeanToProveRH.lean) and an [axiom-free obstruction to decoding the next denominator digit](../receipt-archives/2026-11-24-integral-spectral-frame.md). The [new census](../receipt-archives/2026-11-24-assumptions-before-the-proof.md) measures which axiom names enter at the statement itself.

In the [pole-value control](../receipt-archives/2026-11-24-value-at-the-zeta-pole.md), the observation consists of all values of zeta off its pole. APCI identifies precisely which pointwise claim the observation cannot determine. The [three-point arithmetic readout](../receipt-archives/2026-11-24-prime-pair-readouts.md) recovers a sign lost by recording only the prime-window conditions.

The [two dyadic places](../receipt-archives/2026-11-24-dyadic-class-enters-late.md) give a concrete APCI test. A global change flips both local entries. Their difference detects a class missed at coefficient order two, even after allowing every global change.

The [twisted norm and its weighted observation](../receipt-archives/2026-11-24-when-minus-eighty-erases-a-class.md) now give genuinely distinct source classes in one observation fiber. On the actual arithmetic fields the source keeps separate counts for that fiber and the image. [Two concrete primes](../receipt-archives/2026-11-24-every-place-splits-in-the-limit.md) show why fixing a list of observations before passing up the tower changes what can be recovered.

With [CLEF](CLEF_cluster_layer_entropy_focus_v1_0.pdf), fix the [order-five class](../receipt-archives/2026-11-24-an-order-five-class-and-a-hundred-missing-levels.md) and vary only the coefficient level at the same prime. Its order stays five while the first local solution can move to level 101. With [BLA](BLA_in_PAL_v0.9.1.pdf), follow the surviving class into the [actual rank-two corner](../receipt-archives/2026-11-24-the-rank-two-alternative-at-571.md) and compare the two [directed observations](../receipt-archives/2026-11-24-directed-hecke-test-at-level-571.md) on one function.

On the [full 571 space](../receipt-archives/2026-11-24-one-hecke-line-at-571.md), keep the same vector while changing the prime and direction of observation. The two readings above 2 share a five-dimensional eigenspace, and the primes through 29 reduce it to a single line. On lifting coefficients, [two ramified quadratic fields](../receipt-archives/2026-11-24-two-ramified-hecke-fields.md) share precisely that residue. The [quintic test](../receipt-archives/2026-11-24-quintic-check-for-the-even-alternative.md) checks whether a different global representation could mimic it.

At order 25 we used CLEF to keep the [same global class under three local measurements](../receipt-archives/2026-11-24-two-classes-of-order-twenty-five.md#the-same-global-class-under-three-host-prime-tests). The readings have orders 1, 5 and 25. The [marked matrix calculation](../receipt-archives/2026-11-24-the-two-tangent-signs.md) uses APCI to test whether a scalar trace recovers the sign of the class. The lower entries $u,-u$ and $u,u$ distinguish the two directions that the trace forgets.

## Follow the terminal coordinate across two measurements

The [Context Stack](context-stack/README.md) includes the model, map and rhythm papers, MIND, Context Parallax and the prompt protocols with their available working and published editions. [BLA](BLA_in_PAL_v0.9.1.pdf) supplies the distinction between a residual that has been observed and an explanation that still needs a test. [CLEF](CLEF_cluster_layer_entropy_focus_v1_0.pdf) asks which layer makes a distinction readable. For the terminal matrix, retain the ordinary columns and change only the auxiliary coset. A single local denominator becomes a residue after the basis change, and that residue determines the final Fourier character. Repeating in a swapped frame can change the surviving support from one point to a whole affine subspace. [Paper calculation](../receipt-archives/2026-11-23-coupled-type-prime-residue.md) · [Exact controls](../receipt-archives/check_coupled_type_residue.py)

## Run the disappearing-tail test on paper

Start with any finite cutoff $r$. Ask whether knowing the Taylor coefficients through $r$, and knowing that all coefficients lie in one number field, certifies convergence of the conjugated series. Set $u=(3-\sqrt5)/2$ and put $u^{n^2}$ after the cutoff. The zero series and this series agree on every reported coefficient. One embedding makes the new tail decay on every compact disc. The other sends $u$ to $u^{-1}>1$ and makes its terms grow at every nonzero argument. Varying $r$ repeats the test after any prescribed finite observation.

APCI supplies the reason one collision suffices for that question. An answer recovered from the observed data must be constant on each set of indistinguishable inputs. The mathematical counterexample is the root-test argument itself. The next question is whether the particular theta section in the release can have this tail. That needs an argument about its periods, coefficients and normalization. [Paper derivation and actual-input check](../receipt-archives/2026-11-23-independent-theta-check.md)

| Corpus source | Operation used here | Public work |
| --- | --- | --- |
| PAL v2.4-M, §9, M-INTERFACE-FIBER | State exactly what a checker or a finite jet reads. Hold that observation fixed and vary the requested answer. | [Geometry work key](../RH-PROOF-WORK-KEY.md) |
| PAL v2.4-M, §§6–9, with the Spine, Ledger and Conformance Tests in the handoff | Check the order of uniform quantifiers, coverage by generators and what completion preserves. The handoff calls out T45, T46, T48, T54–T57 and T62, and ledger pairs D33/O54 and D35/O56. | [Handoff and source audit](../receipt-archives/2026-11-23-proof-audit.md) |
| Riemann–Pang Ledger v1.0, §4 and Parts V–VI | Specify a finite prefix and the signed or unbounded tail still to be controlled. Changing the cutoff changes the witness. | [Conjugated theta tail](../receipt-archives/2026-11-23-conjugated-theta-tail.md) |
| APCI v1.0.0 and its reachable-image theorem | Identify two inputs a trace merges. Distinguish an answer on reachable traces from a default assigned outside its mathematical domain. | [Pinned APCI source](Interface.lean) · [Geometry audit](../receipt-archives/2026-11-23-proof-audit.md) |
| Abstract Loops v1.0, §1.1 and the joint-trace test | Ask whether a second observation actually separates the pair. Adding an all-orders coefficient identity can distinguish two functions that have the same finite jet. | [Independent theta check](../receipt-archives/2026-11-23-independent-theta-check.md) |
| BRIDGE v0.4, “Endpoint Certificate Transport” and “Residue and Binding Transport” | Track the input object, its readout and the target of the next map. The raw and projected theta images pose distinct lattice questions. | [Raw theta image](../receipt-archives/2026-11-23-raw-theta-integral-image.md) |
| DARK v1.0, §§4.6, 8.2 and 9.3 | Hold the readout fixed, vary the underlying object, and ask whether the proposed return was obtained independently. Originally applied to Gemini Neon’s tilt and character-sum tests. | [DARK application to Gemini’s results](../receipt-archives/2026-11-23-gemini-tail-review.md) |

## Test two lifts with the same readout

The PAL interface-fiber test and APCI ask whether two inputs with the same observed data can have different downstream answers. In the [level-25 example](../receipt-archives/2026-11-23-theta-transport-at-a-place.md), two lifts agree at level 5 and only one belongs to the moved lattice. Dividing the actual arithmetic columns recovers the extra information. In the [two-coset row](../receipt-archives/2026-11-23-phase-of-a-moved-theta-row.md), the Gaussian norm gives the same answer before and after a rotation, while the raw functions differ by a computable phase. Exact equality is needed before taking the matrix coefficients. Both tests can be repeated with `python receipt-archives/check_theta_lattice_transport.py`. [Finite checks and direct theta evaluations](../receipt-archives/check_theta_lattice_transport.py)

The next [coset-lift test](../receipt-archives/2026-11-23-coset-jets-over-one-field.md) holds the readout at the selected prime over 11 fixed. Dropping the paired condition at its conjugate changes the phase by an eleventh root of unity. The [triangle test](../receipt-archives/2026-11-23-phase-around-three-lattices.md) holds three operator norms fixed and reads the sign after composing them. The actual even rank supplies the missing sign information. [Checks](../receipt-archives/check_unitary_row_phases.py)

## Three questions for each objection

1. What paper argument or independently reproducible observation demonstrates the failure? Give the inputs and the conclusion that fails.
2. Where does the pinned RH argument use this operation, and what property of the particular inputs does its downstream step need?
3. Which of the conditions excluding the objection can a reader establish for those inputs without assuming the bridge under review? State the remaining obligation as *unresolved* whenever only the source assertion has been traced.

A published source link locates a claim. A checker run records what a particular executable accepted or rejected. In the receipts, the mathematical justification for an actual input is the independent argument and the hypotheses it checks. The dated [evidence review](../receipt-archives/2026-11-23-independent-theta-check.md) applies that distinction to earlier conclusions.

Run `python receipt-archives/check_corpus_sources.py` from the repository root for the offline byte checks. Add `--upstream` to compare each file to the public deposit or pinned Git revision. [Verification script](../receipt-archives/check_corpus_sources.py)

## Attribution

The Zenodo editions retain their deposited CC BY 4.0 terms. The original APCI Lean source is from the Apache-2.0 PAL-Lean-Audit repository. The ten author-supplied Context Stack records have separate provenance in the manifest. Chris authorized publication of the expanded shelf on 23 November 2026. Hearthline prepared the guide and verified original bytes through 24 November. [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) · [APCI source repository license](https://github.com/Grativy6/PAL-Lean-Audit/blob/5d5f88d283cd3fdab27aa2c7d91ceb0745653cd0/LICENSE)
