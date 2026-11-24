# P equals NP. Also, P does not equal NP.

Chris asked for the RH blank-slot joke with both answers to P versus NP, using Mathlib’s rules and a release-style statement comparison. Both receipts passed. The two actual Millennium-problem challenges each rejected the corresponding receipt. This is the same APCI lemma as the [RH joke](IUsedLeanToProveRH.lean), applied to the public complexity classes.

```lean
theorem iProvedPEqualsNP : (P = NP) = (P = NP) :=
  bothSwitchesAgree (P = NP)

theorem iProvedPNotEqualsNP : (P ≠ NP) = (P ≠ NP) :=
  bothSwitchesAgree (P ≠ NP)
```

Lean also checked two ordinary logical statements about the unwrapped alternatives, `P = NP ∨ P ≠ NP` and `¬ (P = NP ∧ P ≠ NP)`. The latter theorem is called `noDoublePrize`. [The complete Lean file](PvsNPDoubleFeature.lean)

## The judge’s verdicts

The same solution export went to all three challenges. The Linux `lake comparator` ran in its normal sandbox with the allowed axioms `propext`, `Quot.sound` and `Classical.choice`.

| Challenge | Result | What was checked |
| --- | --- | --- |
| The four propositions actually written, including the two self-equalities | **Accepted, exit 0** | Statement comparison passed. The independent nanoda kernel and Lean’s default kernel accepted the solution. |
| `iProvedPEqualsNP : P = NP` | **Rejected, exit 1** | The solution theorem’s statement differs from the challenge. |
| `iProvedPNotEqualsNP : P ≠ NP` | **Rejected, exit 1** | The solution theorem’s statement differs from the challenge. |

The generic APCI proof uses zero axioms. Each class definition already carries all three foundational axiom names. The two joke proofs, their disjunction and `noDoublePrize` each print those same three. Offering either joke as its bare conclusion also gives a compiler type mismatch. The RH release’s endpoint declaration has the bare type `RiemannHypothesis`. Its comparator challenge asks for that proposition itself. [Earlier axiom comparison](2026-11-24-assumptions-before-the-proof.md) · [Released RH statement](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L1-L6) · [Independent RH verification setup](https://math.mit.edu/~drew/grh/)

## What P and NP mean in the file

The definitions come unmodified from Google DeepMind’s Formal Conjectures. Both classes are sets of Boolean decision problems on bitstrings. Membership in `P` requires a polynomial-time decider. Membership in `NP` requires a polynomial-time verifier and a polynomial bound on the witness length. Their `IsPolyTime` uses Mathlib’s `TM2ComputableInPolyTime`, which supplies a finite Turing machine, a natural-coefficient polynomial and a proof of the time bound for every encoded input. [Complexity classes](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjecturesForMathlib/Computability/Complexity.lean#L48-L96) · [Mathlib’s machine and time bound](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/TuringMachine/Computable.lean#L166-L188) · [Clay’s problem statement](https://www.claymath.org/library/monographs/MPPc.pdf)

The upstream problem catalogue records `P ≠ NP` using `sorry` to mark the open conjecture. We imported only the definitions module and its bitstring-encoding dependency from that project. A separate environment check confirmed that the catalogue’s `ComplexityTheory.P_ne_NP` declaration was absent. The two independent bare challenges use placeholders as the questions to the judge. Their files are compiled separately from the submitted solution. [Upstream conjecture entry](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/Millennium/PvsNP.lean#L37-L45) · [Comparator’s challenge convention](https://github.com/leanprover/comparator/blob/v4.33.0/README.md)

## Run the actual comparison

The [927,948-byte replay bundle](p-vs-np-comparator-exports.tar.xz) contains the submitted proof export, three independently generated challenge exports, their sources, configs and provenance. SHA-256 of the bundle is `427174c90ff75b38b74831d7f63da40811bf8ef3561127b251e3dd64018aff32`. After unpacking it in a fresh directory, run the following from inside that directory on Linux with Lean 4.36.0, its bundled `nanoda_bin`, and working `bwrap`:

```shell
lake comparator --config AsWritten.json --challenge-from-export ChallengeAsWritten.ndjson --solution-from-export double-feature.ndjson
lake comparator --config BareYes.json --challenge-from-export ChallengeBareYes.ndjson --solution-from-export double-feature.ndjson
lake comparator --config BareNo.json --challenge-from-export ChallengeBareNo.ndjson --solution-from-export double-feature.ndjson
```

On Dust the first printed `Your solution is okay!`. The other two named the submitted theorem and reported a statement mismatch. Independently running nanoda on the comparator-ready solution export checked **2,541 declarations with no errors**. Its solution SHA-256 is `2515a39d97e61c1b0d1fb4e09e1a2f4e569947a08d2cb2bc7d4be94c55ebda20`. The [machine-readable receipt](2026-11-24-p-vs-np-replay.json) records every export’s digest and all three judge outcomes.

To rebuild, use [replay_p_vs_np.py](replay_p_vs_np.py) with `--lean-bin` pointing to Lean 4.33.1 and `--packages` pointing to the compiled packages for Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The two upstream class-definition sources are fetched at a pinned commit and hash-checked. The runner compiles five modules, queries their dependencies and verifies that the two direct bare submissions and the conjunction are rejected. Supply `--lean4lean PATH` to replay each module in the independent checker and `--exports DIR` to regenerate the comparison inputs. On Linux, `--judge-bin PATH` runs the three comparisons after export. Our source build and both module checkers used the release’s 4.33.1 pin. The five module replays and the exported dependency-closure replay cover different units of verification. The exporter was `lean4export` at `15f6055e`, built with 4.33.1, and the final comparison used the Linux 4.36.0 judge with nanoda. [Formal Conjectures toolchain](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/lean-toolchain) · [Its exact Mathlib pin](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/lake-manifest.json) · [Lean’s exported-comparator fixture](https://github.com/leanprover/lean4/blob/v4.36.0/tests/lake/tests/comparator-from-export/test.sh#L18-L40)
