# APCI versus Comparator — answer-slot boundary experiment

Prepared in Chat-Hearthline, 25 November 2026, following Christopher Daniel Pang's APCI method. Source-only proposed experiment: NOT executed or compiled in this environment. No upstream modifications.

The same submitted Solution.lean is tested against three independent challenge statements. The open slot is Comparator's documented RH example, now with the APCI exact-certificate/fiber-constancy derivation. The fixed True slot and bare RH are negative controls. Expected outcomes: Hole accepted, True rejected, Bare rejected. Acceptance of Hole is intentional documented behavior, not a kernel exploit or an RH proof. Any contrary result needs investigation; infrastructure failures are not mathematical verdicts.

Use Linux, an unprivileged account, Lean 4.36.0, and its working Comparator sandbox. Run each test in a separate fresh copy of this source directory; never precompile an untrusted Solution in the trusted challenge workspace. In each copy run `lake update` and, if you trust the Mathlib cache, `lake exe cache get`, then `lake comparator --config Hole.json` (or True.json or Bare.json). Capture the version, exit status, complete output, and toolchain/dependency revisions. Do not disable sandboxing. Optional independent kernels can be configured following upstream docs. The project's toolchain is newer than the original RH release; it is a test of the interface, not a replay of the RH theorem. If a CLI option has changed, inspect `lake comparator --help`.

Sources:
- https://github.com/leanprover/comparator#definition-holes
- https://github.com/Grativy6/PAL-Lean-Audit/blob/5d5f88d283cd3fdab27aa2c7d91ceb0745653cd0/projects/APCI/APCILeanAudit/Interface.lean
- https://github.com/Grativy6/rh_proof_redteam/blob/main/receipt-archives/IUsedLeanToProveRH.lean
- https://github.com/Grativy6/rh_proof_redteam/blob/main/receipt-archives/2026-11-24-p-vs-np-double-feature.md

APCI code is a specialized extract of the cited interface. Challenge files contain intentional sorry placeholders; the solution does not. No claim of novelty or successful execution is made.
