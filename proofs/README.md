# Proofs developed in the PAL audit

**These results grew out of Christopher Daniel Pang’s PAL corpus.** Pang originated the research questions and directed the work. Hearthline developed and wrote the derivations with him. The [contribution record](PROVENANCE.md) gives independent publication dates and explains exactly where the Alpöge–Claude release enters each proof.

## Start with the lattice reconstruction theorem

**In every dimension, a marked table of shortest squared lengths at level $N\ge4$ determines the whole positive-definite lattice metric.** For each residue label $c$, the table gives a number $d(c)$. Look for the labels with $d(2c)=4d(c)$. Each has one shortest representative. Those representatives generate the lattice, and the readings of their sums recover every mutual inner product. The proof includes a small numerical example and the extension to rational radicals. [Read the doubling proof](marked-lattice-reconstruction.md)

The papers state their own conclusions and the scope of their application to the RH argument. The overall audit still seeks a verified failure at a necessary step of that deduction.

## More ways into the proofs

| Question | Paper |
| --- | --- |
| What do the actual primes have to do in the last window estimate? | [The prime window at square cutoffs](prime-remainders-at-square-cutoffs.md) |
| Can the same recovered metric hide a different arithmetic action? | [Two actions on one fourfold at the same full torsion level](arithmetic-actions-at-full-level.md) |
| Where can two order-three labels lift to order nine? | [The carry in a nonsplit degeneration](an-order-nine-carry.md) |
| Can a genuine theta sum disappear, and which probe reads through it? | [An exact zero on a lattice orbit](a-zero-on-a-supported-orbit.md) · [The larger torsion reading and corrected size parameters](torsion-readings-at-a-zero.md) |
| Where does the first unpaired point enter? | [A determinant inside the disappearing sum](the-first-unpaired-theta-term.md) · [The seven directions recovered by the second digit](the-two-digit-theta-rank.md) |
| What changes when an equilateral triangle is given unequal weights? | [The cut, the actual $E_8$ roots and the unrestricted vector optimum](three-weighted-triangle-optima.md) |
| What does the golden ratio do at a lattice boundary? | [An exact golden cycle and the rational boundary limits](golden-and-rational-boundary-limits.md) |
| At which conductor does a genuine order-17 class disappear from the strict test? | [Conductor 64 and the first uniformly safe layer](the-order-seventeen-class-at-conductor-64.md) · [Halving the general Bernoulli cutoff](two-rows-halve-the-bernoulli-conductor-cutoff.md) |
| How much precision buys a shared reading? | [The centroid over the field with five elements](the-centroid-that-hides-four-character-readings.md) · [The counting cost of a Frobenius power](the-exact-cost-of-powering-a-frobenius-matrix.md) |
| Can a class lift in the enlarged field and still respect its original symmetry? | [The class-group tower and the order-five obstruction](the-class-lifts-and-loses-its-inertia-symmetry.md) |
| What can still be detected after the auxiliary prime goes quiet? | [Both classes on global commutators](why-the-auxiliary-prime-loses-both-classes.md) · [A fifth-power residue and its lift](a-fifth-power-at-eleven-and-the-missing-digit.md) |
| What can an intersection lose when information passes between components? | [The missing determinant coefficient](two-determinant-tests-at-a-component-intersection.md) · [Exactly which deformations the subgroup trace loses](the-trace-kernel-on-the-cyclotomic-subgroup.md) |
| Which individual prime is built in the original Lean release? | [The authors’ 116-digit prime and the three-case audit of its norm formula](the-three-prime-norms-in-the-released-example.md) |
| Can a linked flag hide in one ordinary line? | [One line through every congruence level](one-ordinary-line-through-all-congruence-levels.md) · [What monodromy adds to identical finite readings](two-linked-flags-with-identical-finite-readings.md) |
| What happens when 2663 takes 577’s place on the same tower? | [The one candidate at conductor eight and the unit that decides it](prime-2663-in-the-real-dyadic-tower.md) |
| Can the same prime be checked locally and globally on paper? | [The order-577 class and its two arithmetic witnesses](a-577th-power-locally.md) |
| Can a local map erase information that another reading recovers? | [What the distinguished-prime projector retains](distinguished-prime-projector.md) · [The reciprocal parameters](recovering-the-inert-spherical-parameter.md) · [The mixed trace that sees the change](finite-trace-test-at-an-irreducible-point.md) |
| Where did the original geometry objection lead? | [An asymmetric mixed intersection](asymmetric-mixed-intersection.md) · [The section-growth countertheorem](section-growth-of-the-geometry-witness.md) |

The [proof map](MAP.md) lists all 55 full reading editions by subject. The [companion index](companion-results.md) leads to the other mathematical derivations and case calculations. Scripts, certified data, source pins and run commands are in the [receipt archive](../receipt-archives/README.md).

## Unresolved

Each paper states the hypotheses under which its result holds. Where an example breaks a proposed inference, the dated receipt traces whether the released argument actually needs it. [Live audit map](../MAP.md#unresolved)
