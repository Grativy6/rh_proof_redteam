# Reproduce the audit

The original proof is pinned to commit `40e56bab026552e089d7afcfeff08d2defb9c005` of `leanprover-community/riemann-hypothesis`, using Lean 4.33.1. The controls in this directory are standalone theorems checked separately with Lean 4.32.1 and Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`. [Audit](2026-11-23-proof-audit.md) · [Evidence inventory](MAP.md)

### Verify the sources

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
