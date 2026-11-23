# RH proof red team

Christopher D. Pang and Hearthline are trying to break the Riemann Hypothesis proof released by Levent Alpöge and Claude on 20 November 2026. We use Pang’s PAL Mathematical Realization Atlas to ask which information a step retains, how its measurements are transported, and exactly where a bound becomes uniform. [Original announcement](https://alpo.ge/remark.pdf) · [PAL v2.4](https://doi.org/10.5281/zenodo.22888036)

**Second result, 23 November.** Every geometry returned by the selected divisor builder fails the release’s asymptotic Riemann–Roch test. The witness always gives one section, even as the leading term grows like a positive power of the tensor exponent. The mixed flag coefficient and the numerical surface inequality we traced on the RH path use other constructions and survive the tests. [Countertheorem, examples and compiled evidence](receipt-archives/2026-11-23-mixed-estimates.md)

The [first geometry turn](receipt-archives/2026-11-23-geometry-witness.md) found that the model’s intersection operation gives 2 for two positive weights in one order and 8 when reversed. The classical answer is 4 either way.

The [first audit](receipt-archives/2026-11-23-proof-audit.md) traced the trivial geometry predicate, the bounds on the chosen height, and the uniformity of the prime windows. The [Turn 1 receipt](receipt-archives/2026-11-23-geometry-witness.md#6-failure-information) corrects its links to the active geometry-selection and log-consumer declarations.

[Turn the public work key](RH-PROOF-WORK-KEY.md) · [Project map](MAP.md) · [Run the checks](receipt-archives/README.md) · [Original audit contributions are licensed under Apache 2.0](LICENSE)

Audit direction and PAL corpus by Christopher D. Pang. Source reading and formal controls by Hearthline in Codex, with a separately prepared Chat-Hearthline research handoff. Upstream mathematics, source code and publications retain their respective authorship and terms.
