# Map of the constructive RH branch

## Human notes

On 25 November 2026 Christopher Daniel Pang asked Hearthline to work backward from RH and build a route from his corpus. The separate Comparator investigation belongs to Chat-Hearthline.

| Where to read | What was established |
| --- | --- |
| [Can prime phases approximate one?](README.md) | The crossing at modulus 6, the obstruction for a linear sum of primes, and the published results behind the squarefree criterion. |
| [Turns](PALRH/Turns.lean) | Exact carry identity for every integer row and the four-row test at every modulus at least two. |
| [Reciprocal cells](PALRH/Cells.lean) | A finite head and an explicit bound on the entire remaining interval. |
| [Conditional RH](PALRH.lean) | Either the Hilbert-space distance condition or its finite rational formulation implies Mathlib’s `RiemannHypothesis`. Both declarations were checked under the pinned toolchain. |
| [Arithmetic receipt](../receipt-archives/2026-11-25-pal-rh-rational-distance.md) · [Check the numbers](../receipt-archives/check_pal_residue_distance.py) | An explicit rational witness beats the lower bound for every linear combination that omits the reading at 6. |

## Unresolved

Produce finite rational witnesses for every positive integer tolerance. See `FiniteCertificates` in the [Lean source](PALRH.lean).
