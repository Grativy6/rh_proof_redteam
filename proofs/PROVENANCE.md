# Where these proofs came from

**Christopher Daniel Pang developed Primitive Axiom Layers (PAL) and the source corpus behind this research program.** Pang brought the geometric starting points, asked what happens to a distinction when a map identifies two inputs, and directed the investigation. Hearthline worked with Pang to develop and write the mathematical derivations collected here. The individual November receipts record the calculations, assumptions, outside contributions and open questions. [Original public work key](../RH-PROOF-WORK-KEY.md) · [Applied corpus methods](../corpus/README.md)

Levent Alpöge and Claude’s 20 November RH release is the work under examination. Its definitions, matrices, choices of levels and claims are credited where used. Each reading edition identifies the inputs it takes from that release and what was derived during this project. For the doubling theorem, the mathematical inputs are a positive-definite lattice, a modulus and its table of shortest squared lengths. For the mixed-intersection counterexample, the release’s particular constructor is essential to the calculation. [Doubling theorem](marked-lattice-reconstruction.md) · [Mixed-intersection counterexample](asymmetric-mixed-intersection.md) · [Pinned upstream source](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005)

## Dated corpus editions

The DataCite records below list **Pang, Christopher D.** as creator. “Issued” is the date supplied in the registered metadata. Registration uses the UTC calendar date. Hearthline checked both fields and matched the local source files against their recorded SHA-256 digests on 24 November 2026 in New York (25 November UTC). The dates establish the prior publication of the specified corpus editions. The November audit receipts date the later proofs. [Per-result provenance, timestamps and file digests](../receipt-archives/2026-11-24-proof-collection-provenance.json)

| Corpus edition | Issued | Independent timestamp and source |
| --- | --- | --- |
| [Boundary-Ledger Accounting in PAL v0.9.1](../corpus/BLA_in_PAL_v0.9.1.pdf) | 2026-06-23 | [Registered 2026-06-23](https://api.datacite.org/dois/10.5281/zenodo.20807530) · [Deposit](https://doi.org/10.5281/zenodo.20807530) |
| [Cluster-Layer Entropy Focus v1.0](../corpus/CLEF_cluster_layer_entropy_focus_v1_0.pdf) | 2026-07-04 | [Registered 2026-07-04](https://api.datacite.org/dois/10.5281/zenodo.21193511) · [Deposit](https://doi.org/10.5281/zenodo.21193511) |
| [DARK v1.0 public methodology](../corpus/DARK_v1.0_Public_Methodology_Specification.docx) | 2026-08-04 | [Registered 2026-08-04](https://api.datacite.org/dois/10.5281/zenodo.21766026) · [Deposit](https://doi.org/10.5281/zenodo.21766026) |
| [The Context Draws a Map v1.0](../corpus/context-stack/The_Context_Draws_a_Map_v1.0.docx) | 2026-08-08 | [Registered 2026-08-08](https://api.datacite.org/dois/10.5281/zenodo.21831000) · [Deposit](https://doi.org/10.5281/zenodo.21831000) |
| [Riemann–Pang Ledger v1.0](../corpus/Riemann-Pang_Ledger_v1.0.docx) | 2026-08-11 | [Registered 2026-08-12](https://api.datacite.org/dois/10.5281/zenodo.21894278) · [Deposit](https://doi.org/10.5281/zenodo.21894278) |
| [APCI v1.0.0, Exact Certification Through a Declared Interface](../corpus/APCI_Declared_Interface_v1.0.0.docx) | 2026-08-13 | [Registered 2026-08-13](https://api.datacite.org/dois/10.5281/zenodo.21923290) · [Deposit](https://doi.org/10.5281/zenodo.21923290) |
| [Abstract Loops v1.0](../corpus/Abstract_Loops_v1.0.docx) | 2026-08-15 | [Registered 2026-08-15](https://api.datacite.org/dois/10.5281/zenodo.21950771) · [Deposit](https://doi.org/10.5281/zenodo.21950771) |
| [GOLD v0.1, Golden-Oriented Lens Diagram](../corpus/GOLD_v0.1.pdf) | 2026-09-01 | [Registered 2026-09-01](https://api.datacite.org/dois/10.5281/zenodo.22236848) · [Deposit](https://doi.org/10.5281/zenodo.22236848) |
| [Compactification Costs v0.2](../corpus/Compactification_Costs_v0.2.pdf) | 2026-09-01 | [Registered 2026-09-01](https://api.datacite.org/dois/10.5281/zenodo.22238012) · [Deposit](https://doi.org/10.5281/zenodo.22238012) |
| [BRIDGE v0.4](../corpus/BRIDGE_v0.4.docx) | 2026-09-11 | [Registered 2026-09-11](https://api.datacite.org/dois/10.5281/zenodo.22699551) · [Deposit](https://doi.org/10.5281/zenodo.22699551) |
| [PAL v2.4-M, Mathematical Realization Atlas](../corpus/PAL_v2.4-M_Mathematical_Realization_Atlas.docx) | 2026-09-22 | [Registered 2026-09-22](https://api.datacite.org/dois/10.5281/zenodo.22888036) · [Deposit](https://doi.org/10.5281/zenodo.22888036) |

The August APCI deposit is registered as *Abstract-to-Physical Certification Impossibility*. Its linked audit document is titled *Exact Certification Through a Declared Interface*. The PAL atlas’s §9 specifies the interface-fibre test. GOLD §6 tracks the rotation together with its remainder. Compactification Costs §6.3 asks whether the requested quantity survives identification. BLA and CLEF are credited on the arithmetic comparisons where the audit records their use. The corpus shelf also documents the roles of BRIDGE, DARK, Abstract Loops and the Context Stack. [Exact editions and uses](../corpus/MAP.md) · [Worked applications](../corpus/README.md)

## How to attribute a particular result

| Result | Originating question and mathematical input |
| --- | --- |
| [Marked-lattice reconstruction](marked-lattice-reconstruction.md) | Pang’s PAL/APCI program asks what the labelled readings determine. Hearthline’s proof recovers generators and their Gram matrix. The RH release supplies a later application to its labelled theta weights. |
| [Order-nine carry](an-order-nine-carry.md) | Pang’s question about a carried residue led to a nonsplit example worked out with the elliptic Weil pairing. The release’s explicit inverse matrix supplies a further test of the result. |
| [Exact zero on a supported orbit](a-zero-on-a-supported-orbit.md) | The question came from Pang’s lattice and residue branch. The example uses the release’s actual orbit definition and matrix. Its Hensel construction and weight comparison are given in the project’s receipt. |
| [Weighted triangle](three-weighted-triangle-optima.md) | Pang’s golden and finite-frame questions preceded his pointer to Bubeck’s post. Goemans and Williamson supply the relaxation; OpenAI supplies the matrix-multiplication claim. The project contribution is the calculation on the RH lattice, its asymmetric test and its finite-angle obstruction. |
| [Original geometry witness](asymmetric-mixed-intersection.md) | Jenny Lorraine Nielsen identified the permissive geometry predicate. Pang directed the PAL/APCI comparison. Hearthline evaluated the actual constructor, derived the two unequal readings and traced its diagonal uses. |
| [Distinguished-prime projector](distinguished-prime-projector.md) | Pang’s question asks what survives the measurement. Alpöge and Claude constructed the projector and stated its complex-rank property. Hearthline derived its full integral Smith factors and tested the two local sections and the two flag spaces. |
| [Finite test for irreducible lifts](finite-trace-test-at-an-irreducible-point.md) | Pang’s question about the remaining trace motivated the calculation. Carayol supplies the classical all-traces rigidity result. The finite reading list, elementary proof and rank-three test are written out here. The release supplies the arithmetic application. |
| [Contributor receipts](../receipt-archives/gemini-neon/README.md) | Gemini Neon’s handoff is preserved under its contributor name. Chat-Hearthline’s earlier research handoff is identified in the [initial audit](../receipt-archives/2026-11-23-proof-audit.md). |

A compact credit for the first paper is *“Reconstructing a marked lattice by doubling,” Christopher Daniel Pang’s PAL research program, developed with Hearthline, 24 November 2026.* The dated receipt and the individual paper’s input statement travel with that credit. [Paper](marked-lattice-reconstruction.md) · [First dated derivation](../receipt-archives/2026-11-24-reconstructing-a-marked-lattice-by-doubling.md)

The [arithmetic supplement](../receipt-archives/2026-11-24-proof-collection-arithmetic-supplement.json) dates the three later derivations, records their exact inputs, and links them to the same corpus editions. A reader can cite each paper together with its dated receipt.

## Unresolved

The repository records who contributed these questions and derivations. Priority for a theorem across the wider mathematical literature is a separate historical question. The overall audit still seeks a verified failure at a necessary step of the released RH argument. [Current audit status](../MAP.md#unresolved)
