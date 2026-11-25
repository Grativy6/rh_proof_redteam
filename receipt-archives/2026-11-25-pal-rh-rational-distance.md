# Replay the rational distance bound

Hearthline ran these checks on 25 November 2026 for Christopher Daniel Pang’s constructive RH investigation. The mathematical target, research credit and hand calculation are in the [branch paper](../pal-rh/README.md).

## Verify the exhibited weights

From the repository root, run `python receipt-archives/check_pal_residue_distance.py` with Python 3.10 or newer. The input is the 61 fixed hundredths printed in the script, ordered by squarefree modulus from 2 through 101. Replaying the certificate requires the Python standard library.

The weights were found by solving a weighted least-squares problem on rows 1 through 24,000, for all squarefree moduli from 2 through 101. The design matrix entry was `(k % d) / (d * sqrt(k * (k + 1)))` and the response was `1 / sqrt(k * (k + 1))`. NumPy’s `linalg.lstsq(..., rcond=None)` supplied the exploratory solution, rounded to the nearest hundredth. The reported inequality is checked from those fixed rational weights. Its validity is independent of the fit or its optimality.

For the established bound, each of the first four million weighted squared errors is rounded upward to a multiple of $2^{-64}$. The checker computes consecutive residuals by the identity $b_d(k)-b_d(k-1)=1/d-[d\mid k]$. It also recomputes rows 1 through 202 directly from their remainders. The sum of the absolute coefficients is $24.74$, so the remaining weight $1/4{,}000{,}001$ costs at most $25.74^2/4{,}000{,}001$. For each pivot from 2 through 32 the script also checks the exact-prefix formula against direct arithmetic through the end of the next block. The checks completed with the following output.

```text
Head upper bound: 193763581491313249/18446744073709551616
Tail upper bound: 1656369/10000002500
Full squared error < 1/92: True
```

## Check the formal implication

In `pal-rh/`, run `lake update` once to fetch the pinned dependencies. Run `lake exe cache get`, then `lake build`. The default target contains the carry identity at modulus 6, the four-row detector, the cell integral estimate, the Mellin identity at zeros, and both conditional RH declarations.

The local replay used Lean 4.33.1 and Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. Lean compiled the three project modules from source with the stock Mathlib dependency closure. Its output for the final declarations was

```text
'PALRH.rh_of_residue_approximation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PALRH.rh_of_finite_certificates' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The arithmetic assumption is a proposition passed as an argument to the theorem. The axiom report lists the foundations the implication uses. The finite witness above establishes one tolerance in that assumption. [Formal source](../pal-rh/PALRH.lean)

Lean’s standalone module checker also returned exit 0 on each of `PALRH.Turns`, `PALRH.Cells`, and `PALRH`. It consumed the compiled modules from these same sources.
