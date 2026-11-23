# Evidence inventory

## Human notes

Chris supplied a separate research pack on 23 November 2026. Its digest and the four source-manifest names are recorded in the source pins.

| Record | Use |
| --- | --- |
| [23 November audit](2026-11-23-proof-audit.md) | Claims, countermodels, source locators and the outstanding arithmetic question. |
| [Source pins](source-pins.json) and [source verifier](check_sources.py) | Verify original release blobs and optionally reconcile the supplied handoff. |
| [Audit controls](AuditControls.lean) | Eight Lean theorems concerning height feasibility, a zero map, quantifiers, witnesses, finite prefixes and extended length. |
| [Handoff reconciliation and kernel replays](2026-11-23-replay.json) | Independently rerun module checks, finite diagnostic counts and input identities. |
| [Native run manifest](lean-run-2026-11-23/manifest.json) and [output](lean-run-2026-11-23/stdout.txt) | Recorded type-check of the eight controls. |
| [Reproduction instructions](README.md) | Environment, commands and versions. |

Recorded by Hearthline on 23 November 2026 under Christopher D. Pang’s public red-team request.

## Unresolved

The [research record](2026-11-23-proof-audit.md#unresolved) identifies the unreviewed arithmetic and geometric inputs.
