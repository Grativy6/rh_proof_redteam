# Replay the PAL construction stage

25 November 2026. Christopher Daniel Pang activated this run from research branch commit `7c289ca6344c658c622335e89dbc4cdd94db924e`. Hearthline performed the derivations, finite computations and self-review. The review and these machines belong to this project. [Key](../pal-rh/CONSTRUCTION-KEY.md) · [Source-use index](../pal-rh/CORPUS-ROUTES.md) · [Machine results](2026-11-25-pal-construction-results.json)

## What passed

Two clean project builds on Dust with the same stock dependency cache reproduced the challenge and solution exports for **the half-unit odd-row displacement theorem** byte for byte. Against its separately written Mathlib-only statement, Linux Lake Comparator 4.36.0 exited 0. Its Lean paranoid kernel, nanoda and Lean default kernel all accepted the inert solution export. This theorem is unconditional and quantifies over **every finite rational fit** hitting row two. The reference exercise's placeholder exists solely in its isolated challenge environment. The solution compiles separately and contains the proof. [Reference statement](../pal-rh/checks/odd/OddChallenge.lean) · [Submitted proof](../pal-rh/checks/odd/OddSolution.lean)

For the canonical **bare RH** target, the actual partial theorem takes a `FiniteCertificates` premise. We exported it under the expected declaration name and submitted it to the independent official challenge bytes with the release's permitted axiom set. The judge exited 1 at statement comparison with `Challenge and solution theorem statement do not match: 'riemannHypothesis'`. No bare RH positive result is claimed. The full mathematical obligation is explicit in the [construction module](../pal-rh/PALRH.lean).

| Export under test | Size in bytes | SHA-256 |
| --- | ---: | --- |
| Odd-row exercise, independent challenge | 10,668,974 | `05b57722f8663e0f6bdf7813c41005b944ef3ea49d0cf839c8abe06034240643` |
| Odd-row exercise, actual solution | 16,645,114 | `486075dcf2267fbb51d37d7810b8e7a13301af021969fab1529af6fc247f0245` |
| Canonical public RH challenge | 350,862,311 | `bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9` |
| Conditional PAL solution used for the RH rejection | 375,402,722 | `74f6f141e521ec0cf05c4303c954e67f869387059d3393b1e69c82f8883e8ef5` |

## Reproduce

From `pal-rh/`, use Lean 4.33.1 and the committed Lake manifest. Run `lake exe cache get`, then `lake build`. The first clean Windows build used the official cache interpreter to populate the same library files because the portable C compiler kit omitted development headers. `lake build` itself ran normally. The second project started with an empty project build directory and shared the pinned stock package cache. The source compiler commit was `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The Mathlib commit was `0df444a360eaa60ab8c11dca51a86af692955474`.

Run the following from the repository root. Use Python 3.10 or later; exporting additionally requires the pinned toolchain and internet access to the two hash-checked exporter sources. The trial judge uses Linux, its normal sandbox, and the named kernel executables on PATH. The exporter uses Lean 4.33.1 while `/path/to/judge/lake` designates the compatible 4.36.0 judge.

```
python receipt-archives/check_pal_prime_refits.py
python receipt-archives/export_pal_check.py odd /path/to/exports
/path/to/judge/lake comparator --config pal-rh/checks/odd/compare.json --challenge-from-export /path/to/exports/odd-challenge.ndjson --solution-from-export /path/to/exports/odd-solution.ndjson

python receipt-archives/export_pal_check.py partial /path/to/exports
python receipt-archives/judge_pal_rh.py /path/to/challenge.ndjson /path/to/exports/partial.ndjson --lake /path/to/judge/lake
```

For `challenge.ndjson`, decompress the independently published reference. Its hash is checked by the judge wrapper before Lake is launched. The `partial` command is a deliberately mismatched control. Once there is a proved `pal-rh/PALSolution.lean`, the exporter’s `final` mode and the same RH command with `final.ndjson` exercise the genuine goal. Rebuild our final export independently and preserve that result alongside the independent comparison. The comparator configuration is narrowed from the five-theorem release to the one RH declaration Pang requested. [Reference files and original replay](https://math.mit.edu/~drew/grh/) · [Exporter revision](https://github.com/leanprover/lean4export/tree/15f6055e299ad5b89345e533cc2192f4cc00f659)

The scalar-route obstruction is standalone. From `pal-rh/` run `lake env lean ../receipt-archives/PALPrimeEvents.lean`. Its arithmetic assertions compare the individual visible contributions of the actual primes 3 and 5. The two claims and the seven project modules at this checkpoint were also replayed with the pinned bundled `leanchecker`. The matrix limits in the [fresh-prime paper](../pal-rh/fresh-prime-transfer.md) are self-reviewed mathematics on paper. The finite tables have a [separate rational replay](check_pal_prime_refits.py).
