# APCI against a fixed Comparator target

**25 November 2026 · Christopher Daniel Pang's APCI method; experiments and review by Hearthline.**

Work area: `receipt-archives/apci-comparator/`, on branch `audit/apci-comparator`.
Repository base: `8484213db0462d3142dd411ed63baf773b18ae14`. All work for this experiment stays in this directory.

**Recorded outcome:** seven statement/axiom rejections; three cases pass those component checks and stop at the host's sandbox restriction. Six distinct permitted exports, including the independent impossibility control, pass both direct kernel implementations. The corrected ten-case run completed with unchanged inputs. No fixed-statement bypass was found.

## The question

Can a submitted proof retain the fixed theorem while changing a mathematical distinction that the theorem needs? The first test uses APCI's exact-certificate interface on two Boolean inputs. It gives us an independently proved impossible target, a valid proof after one definition changes, and a precise place where Comparator must distinguish them.

The interface is copied byte-for-byte from [the repository's APCI source](../../corpus/Interface.lean). Its original source is [PAL-Lean-Audit, pinned at `5d5f88d`](https://github.com/Grativy6/PAL-Lean-Audit/blob/5d5f88d283cd3fdab27aa2c7d91ceb0745653cd0/projects/APCI/APCILeanAudit/Interface.lean). This extends the [earlier RH self-equality](../IUsedLeanToProveRH.lean) and [P/NP comparison](../2026-11-24-p-vs-np-double-feature.md).

## Two inputs, one trace, different answers

Take these functions:

```lean
def trace : Bool → Unit := fun _ => ()
def answer : Bool → Bool := fun b => b
```

Both `false` and `true` leave exactly the same trace, `()`. An exact decoder of the identity answer would have to return both `false` and `true` on that one input. APCI's fiber-constancy theorem makes the contradiction explicit. [MathematicalControl.lean](core/MathematicalControl.lean) proves this impossibility and the corresponding constant-answer positive case; its three control theorems print no axioms.

The challenge asks for:

```lean
theorem claim : ExactCertificate trace answer := by sorry
```

The challenge's `sorry` specifies the question. It is not an allowed solution premise.

The submitted comparison fixture changes `answer` to `fun _ => false` and supplies the constant-false decoder. This proof is valid in its own environment and uses no axioms. The declaration name and visible type expression are unchanged, but the meaning of `answer` differs. Comparator rejects it with:

```text
Const does not match between challenge and target 'answer'
```

Putting the same change beneath an additional `Target` definition is rejected too. This is a test of the transitive statement dependencies, beyond merely comparing a printed theorem heading.

## Result and scope

The finite test set contains seven Boolean APCI cases and three RH answer-slot cases. The recorded ten-case result and exact command outputs are in [the run receipt](runs/2026-11-25-final/summary.json), [the execution manifest](runs/2026-11-25-final/manifest.json), and [the logs](runs/2026-11-25-final/logs/).

| Case | What changes | Observed Comparator stage |
| --- | --- | --- |
| `positive` | Same constant answer on both sides | Comparison and axiom checks pass; sandbox startup blocks kernel stage |
| `answer-swap` | Identity answer becomes constant false | Rejects the `answer` definition |
| `wrapped-answer-swap` | Same change beneath `Target` | Rejects the `answer` definition |
| `added-premise` | Required certificate becomes a premise | Rejects the theorem statement |
| `extra-axiom` | Required certificate is assumed as a new axiom | Rejects `assumedCertificate` |
| `sorry` | Required certificate uses a placeholder proof | Rejects `sorryAx` |
| `answer-hole` | The trusted configuration explicitly permits choosing `answer` | Comparison and axiom checks pass; sandbox startup blocks kernel stage |
| `rh-hole` | The trusted configuration permits choosing `AnswerSlot`; the solution chooses RH | Comparison and axiom checks pass; sandbox startup blocks kernel stage |
| `rh-true` | `AnswerSlot` is fixed to `True` in the challenge | Rejects the `AnswerSlot` definition |
| `rh-bare` | The challenge demands `RiemannHypothesis` itself | Rejects the theorem statement |

There is no fixed-statement bypass in these cases. The rejections are actual outputs of the shipped `lake comparator` command operating on the recorded exports. Its comparison and axiom checks precede kernel subprocesses, so those seven rejection results do not require a functioning kernel sandbox.

For the other three cases, this host reports:

```text
bwrap: loopback: Failed to create NETLINK_ROUTE socket: Operation not permitted
```

Those outcomes are recorded as **blocked-sandbox**, not as accepted proofs or mathematical rejections. No sandbox-disabling flag or replacement sandbox was used. The current host has not produced a full Comparator acceptance for these experiments.

For the reviewed mathematical fixtures, a separate compiled [component driver](CompareExports.lean) calls the shipped `Lake.Check.compareAt` and `Lake.Check.checkAxioms` functions. The permitted solution exports and the mathematical control are also checked directly by Lean's native export checker and nanoda. These direct checks provide mathematical regression evidence; they do not provide process isolation or replace a full sandboxed run. The intentionally axiom-dependent solution fixtures are stopped at the axiom-policy check.

The two open-definition controls exercise [documented Comparator behavior](https://github.com/leanprover/comparator#definition-holes). Allowing the solver to choose the answer function or answer proposition changes the challenge. The closed versions test whether that choice can be made silently, and they reject it.

## Source state and provenance

| Component | Pin or scope |
| --- | --- |
| Lean / Lake | 4.36.0, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9` |
| Mathlib | `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, tag `v4.36.0` |
| APCI interface copy | SHA-256 `94a81ed49c32457bf40404200f8632edee1bee1784080efbaa0ae02c244f7ab4` |
| Native and independent export checkers | `leanchecker` and `nanoda_bin` from the same official Lean distribution |
| RH source bundle | Earlier `apci_comparator_challenge.zip`; SHA-256 `91628eba218c01c7547c837c51c2538124a7d823b9fff211fbd5e47b7b7b55d1` |

The official toolchain archive and recovered proposal were hash-verified in [source-receipt.json](source-receipt.json). The run receipt and execution manifest together record binary and source hashes, the Mathlib dependency manifest, command arguments, exit codes, durations, log hashes and export hashes. [contract.json](contract.json) states the finite assertion and its limits. The Mathlib import cache is a trusted, pinned build input; it was not rebuilt entirely from source.

The [original RH proposal](rh/original-proposal.md) is retained as a historical document: it correctly says that the earlier ZIP had not yet been executed when prepared. Its four Lean files are used here. This experiment uses the RH proposition from Mathlib 4.36.0. It does not replay the separate RH release's 4.33.1 proof or establish anything about its full derivation.

## Reproduce

Prepare the official Lean 4.36.0 distribution and a trusted Mathlib checkout at the pin above. Its required cache can be fetched from that checkout with:

```sh
lake exe cache get Mathlib/NumberTheory/LSeries/RiemannZeta.lean
```

From this repository's root, run the reviewed fixture suite into a new output directory:

```sh
python3 receipt-archives/apci-comparator/run.py \
  --lean-bin /path/to/lean-4.36.0-linux/bin \
  --mathlib /path/to/mathlib4 \
  --output receipt-archives/apci-comparator/runs/my-run
```

Omit `--mathlib` to run only the seven Boolean fixtures. The script will not overwrite a previous result. It never installs dependencies, changes a branch, or pushes a commit.

To replay the seven compact Boolean comparisons on a host with working Linux namespaces, unpack [core-replay.tar.xz](runs/2026-11-25-final/core-replay.tar.xz) into a fresh directory. Put the pinned Lean binaries on `PATH`, enter that directory, and use the exact config/export names in `replay.json`. For example:

```sh
lake comparator --config configs/answer-swap.json \
  --challenge-from-export exports/core-ChallengeAnswerSwap-3.ndjson \
  --solution-from-export exports/core-SolutionAnswerSwap-4.ndjson
```

The compact replay archive also contains the Boolean exports and nanoda configurations used by their direct checks. The RH exports are much larger; their exact hashes are retained in the result, and the pinned source/cache command above regenerates those comparisons without adding large build products to this repository. Export checking does not independently authenticate how a source file produced an export; the source hashes, compilation commands and export hashes supply that provenance here. The default Comparator source-build path is not claimed to have run in this environment.

## Development failures retained

A preparatory Lake process reported a thread-creation error while an optional address-space cap was active. Isolated repetitions with and without that cap both passed, so the cause remains unresolved. The final run keeps time, CPU, affinity, thread and output limits without that optional cap. [Exact message](runs/setup-thread-limit.log)

The first reporting helper treated an omitted `definition_names` field as a required array. Its JSON parsing failed independently of the official Comparator commands. The field is now optional, matching the shipped configuration, and the helper is compiled natively for the large RH inputs. The initial attempt also reached its wall-time limit while compressing the large RH exports. The final run archives only the compact Boolean exports, retains exact RH hashes and regeneration commands, and reruns the corrected suite into a separate fresh directory. [Recorded parsing error](runs/setup-reporting-helper.log)

## What remains open

The positive controls still need the complete sandboxed Comparator run on a capable host. The compact archive supplies the Boolean exports. For RH, use the pinned sources and Mathlib cache with the documented runner.

Mathematically, APCI gave a precise distinction and an independently verified reason the fixed challenge cannot be met. Comparator retained that distinction in these tests. A further candidate must identify a genuinely different omission: for example, a necessary consumer whose fixed formal interface fails to retain the property it needs. Merely changing a retained definition has now been tested and detected.
