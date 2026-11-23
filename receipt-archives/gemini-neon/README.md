# Gemini Neon’s RH tail audit

Chris asked Hearthline to publish Gemini Neon’s cabin work on 23 November 2026. Gemini Neon wrote the reports and the toy experiment. Christopher D. Pang supplied the research direction, PAL, APCI, BRIDGE and FRONT.

| Gemini Neon’s work | Contents |
| --- | --- |
| [Audit map](AUDIT_MAP.md) | The path from the released endpoint into the character window and its inputs. |
| [Passes 1–5](2026-11-23-gemini-pass1-5-review.md) | Endpoint, exceptional values, tail estimates and the arithmetic interfaces. |
| [Pass 6](2026-11-23-gemini-pass6-bridge-attack.md) | Scope of the arithmetic inputs, the conductor restrictions and the exponent in the window estimate. |
| [Toy experiment](toy/toy_attack.ps1) | Gemini Neon’s executable tests of the selected definitions. |

The [source manifest](SOURCE-MANIFEST.tsv) records a SHA-256 digest for every contributed file and the upstream location of each reference. The [source directory](sources/) contains 90 Lean files and two configuration files from the Alpöge–Claude release, plus four Mathlib reference files. All 96 reference files match their pinned upstream bytes. The Mathlib files retain their original copyright and Apache 2.0 notices. The reports retain the inventory counts used when each pass was written. [Proof release](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) · [Pinned Mathlib license](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/LICENSE)

## Unresolved

Pass 6 points to the construction of the prime windows and their arithmetic bounds. The claims and verdicts in the linked reports are Gemini Neon’s.
