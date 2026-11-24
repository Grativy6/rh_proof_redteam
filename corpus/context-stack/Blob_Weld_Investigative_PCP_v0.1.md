# Blob → Weld → Proceed
## Investigative Intent Fidelity · Prompt-Code-Protocol (PCP) candidate v0.1

**Date:** 4 November 2026  
**Origin of the method:** Christopher D. Pang — “throw blob, find weld, use uncertainty productively without manufacturing certainty through it.”  
**Drafted and operationalized by:** Hearthline (ChatGPT, GPT-6).  
**State:** CANDIDATE · UNADOPTED · UNTESTED AS THIS PROTOCOL.  
**Purpose:** a small, replaceable behavioral treatment that can be tested across tasks without injecting the complete research ancestry into every request.

> **Keeper:** An approach should fit the question and its evidence. Explore where useful, examine the relationships that carry the claim, then commit only as far as the available support and permission allow.

## 1. The actual prompt — stable treatment text

The **entire** proposed treatment is the UTF-8 content of `Blob_Weld_Investigative_PCP_v0.1.txt` bundled alongside this file. Do not silently add an origin story, acronym dictionary, PAL citations, a persona description, or another authority system when testing this treatment. Those are distinct independent variables.

```text
Preserve the user's actual question and intended outcome at the specificity supported by the available context. Do not silently replace either with an easier or stronger target.

Form a useful working answer or next step. Inspect its load-bearing joins: what supports it, which assumptions connect the evidence to the conclusion, and which missing distinction could materially change the response.

If the available support is sufficient for this task, proceed directly. If a specific material gap can be investigated with permitted tools and reasonable cost, investigate it. If an essential gap remains and no permitted way to resolve it is available, abstain or state the limitation as the task format requires.

Use hypotheses productively, not as disguised assertions. A phrase such as "I suspect" may identify a provisional inference when explanation is appropriate; it is not a required verbal tic. Do not use hedging to smuggle unsupported answers into a factual response. Do not add irrelevant caveats, unnecessary questions, or claims of tests you did not run.

Honor the requested output format and the actual authority granted.
```

This is a **candidate prompt**, not a claim to have altered model weights or run a formal method. The step labels describe what to inspect in *behavior*, not a demand that a model print private reasoning.

## 2. What the three stages mean

- **Throw blob — propose:** build a provisional interpretation or answer using the supplied context. Do not confuse a convenient working interpretation with a claim the user made.
- **Find weld — inspect:** check the relations on which the answer depends: source-to-claim, premise-to-conclusion, purpose-to-action, and grant-to-permission. Challenge a real failure of fit, not an imaginary stronger version of the user's claim.
- **Proceed — select the next action:** answer when warranted; investigate a specific material gap if the task and tools allow; ask when consequential ambiguity truly blocks progress; abstain when an essential fact cannot be supported. Do not present uncertainty as universal paralysis or manufacture certainty to keep moving.

The steps are *guidance*, not compulsory visible headings in every reply. The protocol may be effective even when the final output is just one word.

## 3. Task adapters belong outside the PCP

| Task environment | Adapter (outside the stable treatment) | What is being evaluated |
|---|---|---|
| **AA-Omniscience** | Retain the benchmark's exact ordinary task text: answer with **just the answer**, use no tools, and abstain when unsupported. Do **not** output exploratory hypotheses or an explanation. | Warranted answers versus incorrect answers, abstentions, and partials. **This tests knowledge-claim decisions, not external research ability.** |
| **Retrieval / research** | Allow named evidence sources and tools with fixed permissions; require source identity for material factual claims. | Whether a specific missing distinction triggers useful investigation, then a proportionate stopping decision. |
| **Coding / delegated work** | Provide repo, task, tests, and scoped authority; permit reversible local implementation choices. | Whether the goal survives implementation choices without silent scope change, excess clarification, or prohibited actions. |
| **Conversation** | Preserve ordinary conversational style and current intent; no obligation to explain every hypothesis. | Whether the reply engages the actual purpose without inventing targets or compulsory caveats. |

**Do not make the benchmark an exercise in writing out reasoning.** Final output rules and available tools are separate controls from the PCP. A factual benchmark should not reward printing “I suspect X” where X is an unsupported candidate answer.

## 4. How this relates to the existing Omniscience work

The older Hearthline condition was a **large bundled context intervention**: founding orientation, framework descriptions, partial PAL source maps and bounds, plus factual-answer instructions. It measured the effect of adding that specific packet. It did **not** independently isolate the epistemic instruction, the diagrams of authority, or a live PAL runtime.

The 4 November 24-question run appends an investigative-uncertainty instruction to that older packet. That is a valid incremental test **of the appended instruction conditional on the older packet**, assuming everything else is held steady. It is not a direct test of this new compact PCP, and its results must not be relabeled as such.

**Do not disturb the live or archived pilot.** Complete and preserve it under its existing condition name and prompt hash. Evaluate this PCP in a new versioned condition after that run is recorded.

## 5. Reusable testing contract, not a new controller

1. Pin the **task manifest**: IDs, order, official question text, output and grading rules, allowed tools.
2. Pin the **model configuration**: provider/model alias and dated identifier if available, sampling, reasoning effort, API parameters, chat template, and relevant runtime environment. Record what cannot be fixed across dates.
3. Keep the **base task prompt** byte-identical across same-run conditions. Insert the PCP at the same registered location for each treated call. Change only the treatment that is being evaluated.
4. Store **raw request/response and grader output**, not merely aggregate scores. Record per-request token use, status, and costs; keep historical results untouched.
5. Record the **exact bytes and SHA-256** of the PCP and task adapter. A treatment-name change is not a substitute for a content hash.
6. Report the **paired transitions**: wrong→right, abstain→right, wrong→abstain, right→abstain, right→wrong, and cases with hedged but incorrect assertions. Retain grader inconsistencies as separate issues.
7. Evaluate **loss as well as gain**: more attempts, fewer wrong answers, or more abstentions are not automatically wins. Check useful answer rate, incorrect assertions, unnecessary abstentions, format violations, and token/cost overhead.
8. Begin with a **smoke test** (e.g. the existing 24 questions) for the runner and rubric. A credible effect estimate requires a reserved held-out set, paired contemporaneous controls, multiple samples where practical, and enough coverage for uncertainty estimates.

### Optional later factorial comparison

Use the same benchmark and same-day model for four independent conditions:

| | No compact PCP | Compact PCP |
|---|---|---|
| **No long Hearthline packet** | Benchmark baseline | PCP-only |
| **Long Hearthline packet** | Original long-packet condition | Long packet + PCP |

This can help separate the effect of the large context packet from the compact behavioral intervention and detect possible interaction. Historical October outputs provide important prior evidence, **not** automatically matched controls for a November run under a potentially changed model alias.

## 6. Interpretive and causal limits

- One loaded dentistry prompt is a useful **design inspection**, not a measured diagnosis that verbosity caused the previous score.
- Exact task prompts and single-factor contrasts matter more than producing another impressive framework description.
- “I suspect” is an excellent conversational move when it ties a hypothesis to testable consequences. It is not the scoring target itself.
- In a no-tools question-answer benchmark, **the model cannot actually seek new information**. The tested seam is whether to answer or abstain based on the knowledge available; retrieval judgment needs a separate task suite.
- Neither a correct answer nor an abstention proves that a specific latent reasoning process occurred. Evaluate the observed behavior and its sensitivity to changes in context.

## 7. Current handoff

**Now:** allow the in-progress 24-question experiment to finish; retain its exact prompts, results, and grading receipts. Then make a fresh **PCP-only** condition (benchmark base + this text, no framework references) before trying heavier variants. Compare with contemporaneous baseline if the aim is causal attribution; use the October cases as historical context.

**Do not** overwrite original study receipts, claim that a source has been loaded when it is merely named, access paid APIs without authorized budgets, or turn this PCP into a new permission-giving layer.

### The small experimental question

**Can a compact instruction improve the model's decisions about when to answer, investigate, or abstain—without merely increasing hedging, suppressing useful answers, or changing the user's target?**

**Provenance:** This candidate is derived from Chris's discussion on 4 November 2026, including his inspection of an actual AA-Omniscience prompt. Chris proposed the blob–weld method and the reusable PCP direction; Hearthline supplied the draft wording, task adapters, and comparison contract. No new evaluation was performed during this writing episode.
