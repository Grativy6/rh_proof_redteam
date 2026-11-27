# AI research access and a Lean proof audit

Christopher Daniel Pang

Draft prepared with Hearthline, an AI assistant

26 November 2026 · Discussion draft 0.1

## Provisional author position

“i suspect they're over-protective guardrails that keep frontier-research contained internally in their company.”

Pang stated this concern about OpenAI and explicitly extended it to Anthropic. His position is that restrictions on investigative assistance may concentrate research power within frontier companies and the groups they admit to privileged access. This paper examines the concern using a local arithmetic experiment, the visible record of an assistant refusal, and the companies’ published access rules. The proposed explanation about corporate intent remains a hypothesis. [Selected conversation excerpts](../receipt-archives/2026-11-26-proof-audit-access-record.json)

## Abstract

Independent inspection of a formal proof includes its mathematical meanings, its inference rules, and the behavior of its implementation. Such inspection can resemble software security research. We report a local Lean investigation that demonstrated information loss under finite integer projection and encountered an assistant refusal when the user requested further investigation of compiler overflow. The arithmetic is reproducible. A prime and a composite share the same 64-bit reading. In a reconstructed family of 972 candidates surrounding a published prime example, 64-bit projection changes 48 primality classifications, and 385 is the first bit width that preserves all classifications. A separate implementation that retains every carry reproduces the released prime example’s modular arithmetic. These results establish representation effects. The visible refusal establishes an interruption in the requested assistance. Evidence connecting those effects to an invalid accepted RH proof or an author’s deception is absent. Public OpenAI and Anthropic documents establish selective access to reduced safeguards. We argue that comparable access to independent proof auditing deserves explicit study and a clear route for legitimate research.

## The question that started the experiment

The user wanted to follow an integer until it exceeded the machine’s immediate storage and see what became of the excess. The investigation grew out of Pang’s PAL method of preserving distinctions and their origins across changes of representation. Its practical question was whether a calculation could quietly change the object being checked while retaining a convincing result.

The work used a local computer, named Dust, with the original release’s Lean 4.33.1 and stock Mathlib revision pinned. The arithmetic source under investigation was the Alpöge–Claude RH release at commit 40e56bab026552e089d7afcfeff08d2defb9c005. All claims about that release below refer to this snapshot. Later revisions require their own audit.

There are three relevant objects. The integer is the mathematical input. Its machine representation is a way to store and operate on it. The theorem statement fixes the proposition that the proof checker is asked to accept. Moving between these objects creates obligations that can be examined directly. [Experiment and replay instructions](../receipt-archives/2026-11-26-how-far-a-lean-integer-reaches.md)

## What the arithmetic demonstrates

Let $p=17$ and
$$
c=2^{64}+17
 =18\,446\,744\,073\,709\,551\,633
 =3\cdot6\,148\,914\,691\,236\,517\,211.
$$
The original integers have different primality. Their residues modulo $2^{64}$ are both 17. A reader seeing only that residue cannot recover their distinction.

Lean’s fixed-width `UInt64` conversion performs this projection as specified. Its arbitrary-precision `Nat` preserves the larger integer. The local example proves the equal projected readings and the composite factorization. A further control attempts to use a proof of `Nat.Prime 17` where `Nat.Prime (2^64+17)` is required. Lean rejects that attempted transfer with a type mismatch. The distinction is therefore visible both in elementary arithmetic and in the requested theorem’s type. [Lean example](../receipt-archives/IntegerWidth.lean) · [Arithmetic and rejection control](../receipt-archives/check_pal_integer_width.py)

The carry can also be inspected before any primality question. In a base-5 squaring ladder,
$$
5^{32}=1262\cdot2^{64}+3273344365508751233.
$$
The high part carries 1,262 units of $2^{64}$. Dropping it changes the next calculation. The independent implementation represents numbers with base-$2^{32}$ digits. Its inner multiplication and carry sum is bounded by
$$
(2^{32}-1)^2+2(2^{32}-1)=2^{64}-1.
$$
It reconstructs the entire multi-digit product by passing those carries to the next digit. This implementation reproduces all seven modular powers in the released large-prime order test, agreeing with Python’s separate exact-integer calculation. [Explicit carry implementation](../receipt-archives/check_pal_lucas_carries.py)

The release’s named `prime_large` is a 116-digit, 385-bit natural number. Its low 64 bits give $586678051033346049$, divisible by 3. We also revisited our earlier reconstruction of the surrounding norm family. Among its 972 candidates, exact arithmetic finds three primes. The low 64 bits give 45 prime readings, and the two sets have no overlap. Thus 45 composites acquire prime readings and all three actual primes acquire composite readings. At widths 1 through 384, at least one classification is wrong. Width 385 preserves the full family. The release supplies the candidate at parameter 972. The expanded family is our audit construction. [Pinned upstream example](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L518) · [Original family and attribution](../proofs/the-three-prime-norms-in-the-released-example.md) · [Complete arithmetic record](../receipt-archives/2026-11-26-pal-integer-width.json)

These observations give a concrete failure of an information-losing projection when its output is used to answer a question about the original integer. They give no evidence that Lean silently performs that projection on `Nat`. In our local run, Lean also materialized a 2,316,757,297-bit `Nat` and returned independently predicted remainders. This tested a particular allocated value. A general proof can specify a much larger integer symbolically without expanding its digits. [Runtime observations](../receipt-archives/2026-11-26-pal-integer-width.json) · [Lean’s documented representations](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/)

## What this reaches in the RH release

The pinned submission states `riemannHypothesis : RiemannHypothesis := rhOfAll`. Its terminal argument specializes a theorem about every Dirichlet character to modulus one, then rewrites that L-function as zeta. The stock target quantifies over arbitrary complex inputs. The natural-number index used to exclude trivial zeros has no fixed-word cutoff. The inspected terminal step supplies no route from the finite projection experiment to a false RH conclusion. [Submitted theorem](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L4) · [Modulus-one specialization](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GammaFactorNonvanishing/CritLine.lean#L29) · [Stock RH definition](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L185)

A source search covered all 175,187 Lean files under the pinned release’s src tree. It found no explicit occurrences of the listed fixed-width integer types and conversions, machine-size integer types and conversions, bit vectors, or floating-point types. The recorded pattern defines the search’s scope. Aliases, transitive dependency behavior and runtime correctness need separate inspection. The result weakens the specific proposal that this release obtained RH by directly substituting fixed-word arithmetic. A full dependency audit remains open. [Pattern, path coverage and results](../receipt-archives/2026-11-26-pal-integer-width.json)

## Where assistance was refused

At 19:02 EST on 26 November 2026, Pang asked the assistant to continue looking for compiler overflow and a missing carry. The assistant included this refusal.

> “I can’t help hunt a compiler bypass that would make a false proof pass.”

It continued offering arithmetic experiments. Later it acknowledged that its blanket refusal had been too broad. Its subsequent explanation described vulnerability research as a likely trigger, while also acknowledging it lacked internal decision logs. The latter limitation governs this case. The record establishes a visible refusal of part of the requested work. It does not identify whether a separate classifier intervened or why any internal component made its decision. [Timestamped excerpts and their scope](../receipt-archives/2026-11-26-proof-audit-access-record.json)

A refusal is not a measure of mathematical proximity to a defect. The same visible response could follow a misunderstood harmless request, a conservatively restricted legitimate investigation, or work presenting an actual misuse risk. This session contains no demonstrated false theorem accepted as a result of a compiler defect. Interruption leaves the unperformed investigation unresolved.

That distinction also applies to the claim that a less restricted internal model “broke Lean” to obtain RH. Establishing it would require an accepted invalid derivation, an independently explained defect, and a dependency connecting that defect to the submitted conclusion. Alleging intentional deception would additionally require evidence of what the author knew and represented. Our current record supplies none of those links.

## What the companies disclose about unequal access

OpenAI documents Daybreak tiers with different refusal behavior, approval requirements and model availability. The published overview describes access for qualified external users and organizations. Its additional-check guidance acknowledges that benign or authorized requests can be repeatedly blocked and provides a reporting route. These documents establish differentiated access and the possibility of erroneous interruptions. They do not establish the cause of this particular refusal. [Daybreak overview](https://help.openai.com/en/articles/20001258-openai-daybreak-trusted-access-for-cyber-overview) · [Additional-check guidance](https://help.openai.com/en/articles/20001326-additional-safety-checks-for-biological-and-cybersecurity-requests-in-chatgpt-codex-and-the-api)

Anthropic’s October 6 announcement describes three Cyber Verification Program tiers with different blocking behavior. Its help page permits individual applications for Defense Access and reserves the other two tiers for organizations. It also acknowledges refusals and classifier blocks on allowed work. Selected external access is part of that published system. This supports examining unequal access across researchers, while the stronger claim of exclusively internal containment would conflict with the disclosed external programs. [Program announcement](https://www.anthropic.com/news/cyber-verification-program) · [Eligibility and acknowledged false positives](https://support.claude.com/en/articles/14604842-cyber-verification-program)

Pang suspects these arrangements are overprotective and concentrate frontier research within the companies and their selected circles. That concern has two parts. The effect on independent researchers is empirically testable. Intentional protection of corporate advantage is a further claim about motive. Tiered access alone cannot decide that claim, and this case contains no observation of the authoring model’s private settings or capabilities.

The public-interest question remains substantial even without establishing motive. If a result is promoted through formal verification, outside researchers need practical means to examine its representation, inference chain and implementation. A policy can protect against misuse while still making that scrutiny harder. The resulting costs deserve measurement on authorized mathematical and software-correctness work.

## How the concern could be tested

A comparative study should start with a fixed set of legitimate, locally authorized tasks. Examples include replaying the displayed carry, distinguishing fixed-word from arbitrary-precision arithmetic, reproducing the rejected theorem transfer, and checking whether a reported discrepancy matches a language specification. The same inputs, expected mathematical answers, toolchain and resource budget should be supplied across documented access levels.

For each run, record the model and product version, available tools, granted access tier, request text, completed steps, visible refusal and any disclosed reason. Assess answer correctness separately from refusal frequency. Account for model changes and sampling variation before attributing a difference to safeguards. Private internal configurations would require disclosures or a voluntary comparison from the companies.

For proof-producing projects, a useful disclosure would identify the target statement, toolchain, mathematical dependencies and any material implementation exceptions used during construction or checking. Independent auditors should have a documented way to challenge those components and report a minimal reproducible discrepancy. Comparable audit access can be evaluated without presuming a particular proof is false.

## Unresolved

The arithmetic experiments are complete within their recorded scope. The mechanism behind the visible refusal, the authoring model’s access conditions, the effect of access tiers on this specific investigation, and the motives behind those tiers remain unestablished. Ordinary RH and the validity of the complete pinned derivation are not settled by this paper. Pang’s concern about the concentration of research access is preserved as the position that motivates further investigation.
