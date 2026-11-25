# One-tick stage and continuation

25 November 2026 · Hearthline under Christopher Daniel Pang’s active construction key. The preceding local commit is `f18bae2a45732383aa6d922ed8cb42d35ce5a0ac`; the [public copy of that stage](https://github.com/Grativy6/rh_proof_redteam/commit/6b957822b79f3ed9b43406bffd828887f90a15aa) has the identical Git tree `8202d16b31abc09806f28bf1b5cc329b401cf1ec`. The public commit messages retain their local-source IDs. The GitHub connector created the public commits after native Git could not authenticate its push. The separate Comparator work remains in its own lineage.

## Changed mathematical state

| Claim | Evidence and consequence |
| --- | --- |
| First-tick approximation is equivalent to the branch's original finite rational certificates. | `first_tick_iff_certificates` and `rh_of_first_tick` in [OneTick](../pal-rh/PALRH/OneTick.lean). The forward proof actually builds finite dyadic sums and uses a $3/4$ contraction. The backward fit is $f-D_2 f$. |
| Data adequate for one target can fail on the other. | `blind_tick_floor` bounds first-tick error below by $1/40$ when the four-row observation vanishes. Every finite fit omitting modulus four has this blind spot. The transformed earlier witness is below the floor with its complete tail accounted for. [Derivation and weights](../pal-rh/one-tick.md) |
| The sieve supplies an unconditional all-cutoff target and a directional obstruction. | `sieve_loss`, `sieve_not_finite`, `reflected_sieve_identity`, `adjacentRepair_prefix` and `adjacentRepair_loss` in [Sieve](../pal-rh/PALRH/Sieve.lean). The forward-only approximant and the one-fresh-prime correction were also attacked on paper. The adjacent legal count repair fits a growing prefix exactly and already fails at the very next reset. [Calculations](../pal-rh/reversing-the-sieve.md) |
| A legal way to read the signed event | `contrast_value`, `contrast_full_bounds`, `edge_harmonic` and `contrast_reads_sieve` cover the actual active bands, the finite harmonic price and the unseen rows. The growing-resolution leading metric on paper records shared divisors. [Derivation](../pal-rh/close-clocks.md) |
| Costs have to be recomputed on the receiving target. | Pairs 101/103 and 107/109 improve the actual first-tick witness with opposite coefficients. Copying both signed coefficients to the two-band constant receiver makes both moves worse. Repricing them gives two sequential improvements on the original target. [Exact signed bounds](2026-11-25-pal-first-tick-results.json) |

## Reproduce

Run `lake build` inside `pal-rh/` on the pinned toolchain. The library roots include the constructive program through its sieve/clock modules. On Dust the 3,717-job dependency build returned exit 0. Native kernel replay accepted ten project modules and the standalone two-prime scalar control. The relevant new statements reported the same three foundational axioms. Additionally the bundled con-leche and con-ron each accepted the 4,516 declarations of the earlier unconditionally proved odd-row export in verified mode. These were export-kernel runs, separate from that stage’s [fixed-statement comparison](2026-11-25-pal-construction-replay.md).

From the repo root, replay `python -B receipt-archives/check_pal_first_tick.py` and `python -B receipt-archives/check_pal_close_clocks.py`. Both use exact signed integer rounding and deterministic rational weights; discovery scans were used to choose the examples. The machine record includes the exact rational upper and lower results, cutoffs, source digests, and run scope.

## Continuation

The original RH target is active. First-tick localization and reflected-sieve repair have explicit remaining premises. A candidate repair must have signed overlap with the changing residual on its *current* frame. Use the exact band formula to get a lower bound for that overlap and subtract a true upper bound for the omitted bands before pricing a step. If the lower bound disappears in the completion, change the observable or the return step. Preserve both trial signs and the previously paid correction. The all-scale lower budget is still open. [Construction key](../pal-rh/CONSTRUCTION-KEY.md) · [Live map](../pal-rh/MAP.md)
