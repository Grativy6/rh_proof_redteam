# The corpus and RH Lean checks, side by side

**24 November 2026.** Chris Pang asked Hearthline to compare his corpus with the Alpöge–Claude RH release on assumptions and source length. On their published toolchain, all 121 corpus files in this comparison compiled and passed native kernel replay. Every one of the **746 explicitly named public theorem or lemma declarations** used a subset of the RH endpoint’s three foundational axioms. **172 used none.** The corpus sources totaled **12,758 physical lines**, compared with **17,374,215** in the RH release. I also tested both approaches on one identical statement actually used by the RH argument. Both five-line declarations passed and used the same three axioms. [Per-theorem statements and axiom sets](2026-11-24-corpus-theorem-axioms.jsonl) · [Counts, pins, file outcomes and direct failures](2026-11-24-lean-comparison.json)

## What was compared

| Public source | Files | Physical lines | Named source declarations checked on the published pin | Files checked on RH’s Lean 4.33.1 setup |
| --- | ---: | ---: | ---: | ---: |
| PAL collection root, including experiments and audit modules | 93 | 9,808 | 570 | 87 |
| APCI project | 5 | 246 | 15 | 5 |
| FRONT project, including inherited modules | 15 | 2,144 | 124 | 10 |
| APCI manuscript supplement | 1 | 73 | 4 | 1 |
| Current Context Parallax formal package | 7 | 487 | 33 | 7 |
| **Pang corpus in scope** | **121** | **12,758** | **746** | **110** |
| Alpöge–Claude release, all tracked Lean files under `src/` | **175,187** | **17,374,215** | Five published headline targets examined | 175,187 module replays reported by Sutherland |

I used the public PAL collection at `5d5f88d2` and the current seven files in the deposited Context Parallax v1.0 formal package. The main PAL repository alone accounts for 114 files and 12,271 lines. On both sides the line measure counts blank lines and comments and excludes dependency packages. For PAL it excludes 974 vendored external-audit Lean files and three Lake configuration files. The counts retain copies actually compiled in separate projects. Collapsing identical source bytes leaves 117 corpus files and 12,101 lines, with 711 distinct named source locations. The BLA and CLEF manuscripts enter the separately documented arithmetic investigation. [PAL paper-to-project map](https://github.com/Grativy6/PAL-Lean-Audit/blob/5d5f88d283cd3fdab27aa2c7d91ceb0745653cd0/papers/INDEX.md) · [Context Parallax deposit](https://zenodo.org/records/23306102) · [Corpus application](2026-11-23-coupled-type-prime-residue.md)

## What “same or fewer assumptions” can establish

Lean’s axiom report follows the proof’s dependencies. It reports names of foundational axioms used by that particular proof. The corpus census calls Lean’s `collectAxioms`, the same operation used by `#print axioms`. The statement separately records its variable inputs, typeclasses and ordinary hypotheses. For example, a theorem saying a left inverse implies injectivity receives the left inverse as a premise. A theorem comparing all zeros of a specific analytic function makes a different mathematical demand.

On Lean 4.32.1, the union of foundational axioms used in the checked corpus is exactly `propext` (propositional extensionality), `Classical.choice` (classical choice), and `Quot.sound` (quotient soundness). Of the 746 source declarations, **366 used all three and 380 used a strict subset**. The latter count includes the 172 axiom-free proofs. No registered project axiom or `sorryAx` was a dependency of these declarations. The inventory distinguishes source commands from compiler-generated equation, constructor and other theorems. It also preserves each theorem’s inferred type so the hypotheses can be inspected. [Complete inventory](2026-11-24-corpus-theorem-axioms.jsonl)

| Named declaration | What it proves | Reported foundational axioms on its published pin |
| --- | --- | --- |
| `APCILeanAudit.collision_persists_under_postprocessing` | Equal traces stay equal after applying the same postprocessor. The equality of the starting traces is an explicit premise. | None |
| `APCILeanAudit.exactOnReachable_iff_fiberConstant` | An answer can be decoded on reachable traces exactly when it is constant on every trace fiber. | `Classical.choice` |
| `APCILeanAudit.exactCertificate_iff_fiberConstant` | The analogous characterization for a total decoder, with an inhabited answer type to supply a fallback. | All three |
| `CPX.ProtectedReturn.protected_return` | If the answer factors through a projection and an update preserves that projection, the answer is preserved. | None |
| `Experiments.FiniteAbstractionControls.pointwise_bounds_without_constant_bound` | Each natural number has a larger bound, while one constant cannot bound them all. | `propext`, `Quot.sound` |
| `riemannHypothesis` | Mathlib’s `RiemannHypothesis`, with its nontrivial-zero conditions. The root proof term refers to `rhOfAll`. | All three |

The comparison driver also asked Lean whether each checked theorem’s type is definitionally equal to Mathlib’s `RiemannHypothesis`, with definitions transparent. **Zero matched**, both on the published corpus toolchain and in the successfully compiled cross-version subset. A reformulation could still be linked by a mathematical equivalence or implication. Such a bridge is a separate theorem and would need its own evidence. [APCI statements and proofs](https://github.com/Grativy6/PAL-Lean-Audit/blob/5d5f88d283cd3fdab27aa2c7d91ceb0745653cd0/projects/APCI/APCILeanAudit/Interface.lean#L57-L112) · [Finite-bound control](https://github.com/Grativy6/PAL-Lean-Audit/blob/5d5f88d283cd3fdab27aa2c7d91ceb0745653cd0/Experiments/FiniteAbstractionControls.lean#L26-L34) · [Original RH target](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L1-L6)

## One common statement with exactly the same premises

Take a field $F$, matrices $C:F^d\to F^n$ and $L:F^n\to F^d$, and the hypothesis $LC=I_d$. The common target is injectivity of $x\mapsto Cx$. This particular lemma occurs on a 16-edge proof-body path to the released RH endpoint. One direct caller uses it to obtain injectivity in the quotient-frame Hermitian calculation. The comparison was selected because the existing APCI left-inverse lemma applies to this actual frame test. [Released lemma, lines 29–33](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L29-L33) · [Caller](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L199-L205) · [Reachability data and file hashes](2026-11-24-lean-comparison.json)

The released proof applies $L$ to an equality $Cx=Cy$ and simplifies using $LC=I$. The APCI proof constructs exactly the same left inverse on vectors and applies its four-line general lemma. I compiled the complete unchanged release module and separately compiled the APCI application, which imports only Mathlib and the APCI interface. A third file assigned both results to one explicit `FrameClaim`. All three modules passed Lean’s native checker and `lean4lean` at the RH compiler pin. [Independent APCI application](FrameByAPCI.lean) · [Shared type and axiom queries](CompareFrameClaim.lean)

| Measure | RH project proof | APCI application |
| --- | ---: | ---: |
| Direct declaration, including statement and proof | 5 lines | 5 lines |
| Ordinary matrix premise | $LC=I$ | $LC=I$ |
| Foundational axioms reported for the matrix theorem | All three | All three |
| Additional reusable corpus lemma | — | 4 lines, axiom-free |

I also cut the original five-line declaration out verbatim and compiled it in isolation with only Mathlib, the original release options, and a fresh namespace. It again passed both checkers with all three axioms. The source module sits in a project-local import closure of 64 files and 9,808 lines. This experiment shows directly that those 9,808 lines are not needed to prove this individual lemma. Likewise the one-line RH wrapper in `Main.lean` delegates its proof to a much larger imported argument. [Isolated-slice digest and replay outcomes](2026-11-24-lean-comparison.json)

Multiplication by a prime $q$ has the left inverse $1/q$ over a number field, and that inverse is unavailable on the integral lattice. Both checked matrix theorems are correct on their stated field. Any later passage to an integral inverse needs its own hypothesis. The shared comparison establishes no counterproof to the RH implication.

## Which checks ran on Dust

I freshly compiled the pinned corpus source against precompiled dependencies and ran the native kernel checker. The published environment uses Lean 4.32.1 and Mathlib `520045ab`; the APCI project itself uses core and Std. I repeated the experiment on unchanged sources using Lean 4.33.1, RH’s Mathlib `0df444a3`, the native checker and independent checker `lean4lean` at `67f63b0c`. All 110 modules that compiled in the latter run passed both replays. They contained 655 of the 746 source declarations. On this common toolchain 309 used all three foundational axioms and 346 used a strict subset, including 161 that used none. The stock checker accepts namespace prefixes; a prefix-expanded replay that timed out was rerun on an import-limited path. Counts of passing replays require an exit code of zero.

Four unchanged modules encountered direct elaboration errors on the newer compiler and library. Seven dependent modules consequently could not be built. The original-version build and replay passed for all eleven.

| Source module | First cross-version error |
| --- | --- |
| `FrontLean.Linear` | Line 86 leaves a quotient-map simplification goal. |
| `FrontLean.Correction` | Line 117 fails while deriving `Fintype` for `TestAtom`. |
| `Experiments.GPPREncoding` | Line 84 leaves an equality of valuations where factorization values are expected. |
| `Experiments.Pal24Continuation` | Line 128 reports that `simp` made no progress. |

Eight unchanged source declarations that passed on both setups acquired `Classical.choice` in the newer proof-term dependency set. For example, this happened to `Experiments.FiniteAbstractionControls.finite_set_does_not_cover`. The axiom count measures a particular elaborated proof with particular library dependencies. The counts do not establish the logically weakest axioms from which the statement can be proved. [Exact outcomes and all eight changes](2026-11-24-lean-comparison.json)

For the RH headline I read the type, immediate proof constants and the compiler-recorded axiom table of the actual `Main.olean` on Dust with Lean 4.33.1. Its SHA-256, `9146dfb4148e24d2252e04c50742f3e49dd126dfcc5006d10bf5f873ddf796ad`, matches Andrew Sutherland’s original and sandbox rebuild manifests. Each of the five records also matched his published `#print axioms` transcript. The full-release replay evidence here is Sutherland’s: he reports all 175,187 modules passed `lean4lean`, with five needing a raised step limit, and independent checks of the complete export. My fresh RH kernel replay covered the selected original frame module and its isolated declaration. Reading a compiled axiom record is a metadata inspection. [Original axiom log](https://math.mit.edu/~drew/grh/audit.log) · [Full verification and build manifests](https://math.mit.edu/~drew/grh/)

## Repeat the comparison

1. Check out the two revisions named above and keep the CPX v1.0 companion from the [public corpus shelf](../corpus/context-stack/CPX_v1.0_Companion.zip). Run `python measure_lean_sources.py --pal PAL_CHECKOUT --rh RH_CHECKOUT --cpx PATH_TO_CPX_ZIP --out sizes.json` from this directory. A bare RH Git mirror also works.
2. Run `python compare_corpus_lean.py --source PAL_CHECKOUT --bin LEAN_BIN --packages DEPENDENCY_DIR --work NEW_WORK_DIR` for the selected compiler. Supply matching compiled dependencies. The package directory may contain ordinary Lake checkouts or restored binary library directories. To use an independent checker, add `--second-checker PATH_TO_LEAN4LEAN`. Use a separate work directory with `--cpx-only PATH_TO_CPX_ZIP` for CPX. The output includes the compiler version, every stage exit code, source line, inferred type, axiom list and RH type-comparison result. It saves the full result and returns a nonzero exit code if any source or replay failed.
3. Run `python read_rh_axioms.py --bin LEAN_4_33_1_BIN --work NEW_WORK_DIR` for the compact RH endpoint comparison. It fetches a pinned module and checks it against both published build manifests. The accompanying Lean reader decodes the type-erased axiom records using the 4.33.1 schema; it contributes no theorem to either proof. [Reader](ReadAxiomReceipt.lean) · [Lean’s own versioned axiom collector](https://github.com/leanprover/lean4/blob/v4.33.1/src/Lean/Util/CollectAxioms.lean)
4. To repeat the common-claim test, make the compiled original `Formalism.LocalToGlobal.Divisibility.FramesLemmas`, matching Mathlib, and the separately compiled APCI `Interface` available on the 4.33.1 Lean search path. Compile `FrameByAPCI.lean` into a fresh directory, add it to the search path, and run `lean CompareFrameClaim.lean`. The two ascriptions verify the common statement and the three printed axiom sets expose the cost of its specialization.

[Source counter](measure_lean_sources.py) · [Corpus compilation and assumption checker](compare_corpus_lean.py) · [RH endpoint verification](read_rh_axioms.py)

## Unresolved

The head-to-head result concerns a necessary frame lemma, with the matrix left inverse explicitly supplied. An implication that is central to the RH argument could still have a shorter proof, or a missing premise. Establishing either requires a comparison at that exact statement and the actual arithmetic inputs that invoke it. The [type-prime calculation](2026-11-23-coupled-type-prime-residue.md) records a place where the distinction between a field map and its integral lattice is measurable.
