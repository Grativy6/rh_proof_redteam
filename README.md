# RH proof red team

Christopher D. Pang and Hearthline are trying to break the Riemann Hypothesis proof released by Levent Alpöge and Claude on 20 November 2026. We use Pang’s PAL Mathematical Realization Atlas to ask which information a step retains, how its measurements are transported, and exactly where a bound becomes uniform. [Original announcement](https://alpo.ge/remark.pdf) · [PAL v2.4](https://doi.org/10.5281/zenodo.22888036)

**Can a change of coordinates hide a denominator?** On the CM curve of discriminant $-7$, degree 25 loses a factor of 5 for every unit in the starting local field. We proved that an explicit unit in the extension the release permits works in all degrees. The quadratic correction in the theta function is forced and equals 1 on this model. [The curve and its normalization](receipt-archives/2026-11-23-height-two-coordinate.md) · [A sharp one-unit loss inside the local jet estimate](receipt-archives/2026-11-23-jet-loss-and-frames.md)

**Where does the proof write in the number it needs?** For a spectral block with no qualifying vector, the source assigns the exponential of its desired lower bound. We traced that number between the two levels used by the height proof. Every label carrying a nonzero period direction there has a witness at the tested level. [The exact convention and its scope](receipt-archives/2026-11-23-zero-part-eigenvalue.md) · [Direct integral on occupied scalar discrete series](receipt-archives/2026-11-23-formal-degree.md) · [Which phases preserve the global class sum?](receipt-archives/2026-11-23-conjugated-phase.md)

**Can the proof discard a set carrying its entire residue?** One point can carry the whole residue of a p-adic integral. The downward theta argument has a scaling law that rules out such a loss on its singular matrices. Removing one row makes a direct local count diverge. [Two theta maps and the residue](receipt-archives/2026-11-23-downward-residue.md) · [Exact split-prime calculation](receipt-archives/2026-11-23-split-gram-density.md)

A further [test of the fixed downward map](receipt-archives/2026-11-23-fixed-downward-test.md) finds a full-rank matrix missed by every translate and derives the exact subgroup average that removes it. The real integral for the proposed kernel vector becomes a squared norm.

**When does the upward theta integral cancel?** Two degree-two oscillator vectors have the same compact weight. One gives zero. The harmonic vector gives $1/(b+1)$ for $b$ oscillator pairs. The [local integral calculation](receipt-archives/2026-11-23-oscillator-cancellation.md) determines the whole kernel in rank one and tests the higher-rank positivity argument.

**Which directions can the period lose?** An integer vector can have an orthogonal quotient representative with denominator 5. We traced the condition that keeps the period integral, and proved a bound for the proportion of source directions that can disappear after projection. [Examples, proof and source](receipt-archives/2026-11-23-period-on-quotient.md)

**A residue in the quotient metric.** In a rank-one test, the algebraic and geometric answers differ by $\log(1+\sqrt[3]4)-\tfrac13\log5$. The difference can grow without bound even with fixed lattices. We followed its sign through the upper bound used in the proof. [Hand calculation and source trace](receipt-archives/2026-11-23-quotient-covolume.md)

**Can two lattices agree about every rational vector and still disagree about divisibility?** Yes. One can hide half a valuation, and a rank-two example hides a determinant index of $5^N$ with the fields and rational map fixed. The [valuation calculation](receipt-archives/2026-11-23-valuation-descent.md) traces the extra integral-span condition and the denominator of the actual period.

**Can a nonzero coefficient disappear?** The theta-lift code returns zero for a complex coefficient outside the chosen number field. We found an explicit nonzero input that disappears and an integral line where a mistaken choice would lose half the logarithm of 3. The proof builds its field from the original complex coefficients and checks the degrees the operator reads. We found no loss at that step. [Mathematical argument and source trace](receipt-archives/2026-11-23-coefficient-descent.md)

**Second result, 23 November.** Every geometry returned by the selected divisor builder fails the release’s asymptotic Riemann–Roch test. The witness always gives one section, even as the leading term grows like a positive power of the tensor exponent. The mixed flag coefficient and the numerical surface inequality we traced on the RH path use other constructions and survive the tests. [Countertheorem, examples and compiled evidence](receipt-archives/2026-11-23-mixed-estimates.md)

The [first geometry turn](receipt-archives/2026-11-23-geometry-witness.md) found that the model’s intersection operation gives 2 for two positive weights in one order and 8 when reversed. The classical answer is 4 either way.

The [first audit](receipt-archives/2026-11-23-proof-audit.md) traced the trivial geometry predicate, the bounds on the chosen height, and the uniformity of the prime windows. The [Turn 1 receipt](receipt-archives/2026-11-23-geometry-witness.md#6-failure-information) corrects its links to the active geometry-selection and log-consumer declarations.

[Turn the public work key](RH-PROOF-WORK-KEY.md) · [Project map](MAP.md) · [Run the checks](receipt-archives/README.md) · [Original audit contributions are licensed under Apache 2.0](LICENSE)

Audit direction and PAL corpus by Christopher D. Pang. Source reading and formal controls by Hearthline in Codex, with a separately prepared Chat-Hearthline research handoff. Upstream mathematics, source code and publications retain their respective authorship and terms.
