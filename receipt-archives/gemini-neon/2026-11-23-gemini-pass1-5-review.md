# Adversarial Source Review (Passes 1–5): Endpoint, Tail-Closing Engine, Master Keystone, and Shape Discrepancies in the 20 November 2026 Lean RH Release

**Date:** 2026-11-23  
**Direction & Analytical Lens:** Christopher D. Pang (`PAL v2.4`, `APCI v1.0.0`, `BRIDGE v0.6`, `FRONT v1.0`)  
**Source Audit & Synthesis:** Gemini  
**Pinned RH Release:** `leanprover-community/riemann-hypothesis` @ `40e56bab026552e089d7afcfeff08d2defb9c005` (Lean `4.33.1`)  
**Pinned Mathlib:** `leanprover-community/mathlib4` @ `0df444a360eaa60ab8c11dca51a86af692955474`  
**Local Evidence Mirror:** `h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/` (55 pinned files)

> **Methodology & Epistemic Scope:** For this review, machine-checked Lean verification is treated strictly as a **secondary claim**, not a substitute for source inspection or mathematical comprehension. We audited 55 pinned source files directly (49 RH release `.lean` files, 2 release build configs, and 4 upstream Mathlib `.lean` files) looking for endpoint loopholes, quantifier/tail-closing errors, Mathlib junk-value leakage, degenerate surrogates, phantom dependencies, and `BRIDGE` shape mismatches. No local full-tree Lean compilation or independent kernel replay was executed in this workspace.

---

## Executive Summary

1. **No defect in the formal RH endpoint or Landau tail-closing roof was found.**
   The exported `Main.riemannHypothesis` binds directly to Mathlib's pre-existing classical `riemannZeta` (Jacobi theta → Poisson summation → Mellin transform → analytic continuation on $\mathbb{C} \setminus \{1\}$ agreeing with $\sum_{n=0}^{\infty} (n+1)^{-s}$ for $\operatorname{Re}(s) > 1$), with no junk-value leakage detected in `RiemannZeta.lean`, `HurwitzZetaEven.lean`, `AbstractFuncEq.lean`, or `MellinEqDirichlet.lean`. The analytic tail-closing roof (`TopWin` → `WindowHypOfRpow` → `poleData` → `landauWindow`) is sound classical Landau/Mellin window-concentration analysis with clean binder order and non-canceling residues.
2. **The crown-jewel keystone abstractions we opened (`hodgeH`, `TLiftK`) are NOT `geoDegenerate`-style fakes — but `TLiftK` is corridor-carved.**
   `hodgeH` / holomorphic Lefschetz is built directly on Mathlib `Scheme.{0}`, Kähler differentials, and Čech cohomology. `TLiftK` defines real adelic unitary theta-lift integrals, Petersson matrix coefficients, local intertwining forms, and Rallis nonvanishing — **but only inside a deliberately carved `GoodK` corridor** (`SplitStab.lean` L16–24: CM extensions containing $\sqrt{-d}$, everywhere unramified, with every inert prime odd and residue norm $> 3$). It fits the RH prime-window selector like lock-and-key while failing a `BRIDGE` transport test onto general CM fields.
3. **Four concrete archaeological / fossil-scaffold discrepancies were verified directly in source (including 62/62 phantom dependencies).**
   * **62/62 ghost-parameter wrappers** in `TemperedProductOfSquareIntegrable.lean` (L207–344): all 62 classical literature theorems take `(O : OpenImageCondition)` (wrapping `Row0b recT`); **50 ignore `O` completely**, **12 only forward `O` into other wrappers in the same block**, and **0 / 62 ever read a field of `O`**. Every one of those 62 theorems holds unconditionally without `O`, yet top-level files (`CorGKOf.lean`, `VwinOfRow.lean`, `TopMainZj.lean`) route `O := OpenImageCondition.mk galoisLocalGlobalStrong_recParameter` through all 62 — creating 62 phantom dependency edges to `RowSrc.lean`.
   * **Dead `True` hypothesis slots** in the master truss: `ShapeWin.lean` L27 (`TopShape True True ...`) paired with `EveryCharacter.lean` L11 (`shape_of _ _ _ _ (shapeWin hG) trivial trivial h`).
   * **Empty 1-line stub module**: `DiscreteSeriesCoefficientsCuspidal.lean` contains only `import Mathlib`, yet remains imported by `TopMainZj.lean`, `LitAut.lean`, `WindowBoundOfLiteratureLevel.lean`, and `TemperedProductOfSquareIntegrable.lean`.
   * **Degenerate geometry model** (established prior to this review in `Grativy6/rh_proof_redteam` Turn 1 & Turn 2): `anyGeometry := fun _ _ _ => True` and `divXFl` / `geoDegenerate` provably fail `AsymptoticRiemannRoch`, `AdmG`, and symmetric mixed intersection while sitting off the live mixed-degree path (`weyl_coeff`, `interNum`, `growth_eq_covolume`).
4. **Earned `PAL` / `FRONT` status label:**
   Because the raw dependency graph preserves unpruned ghost edges, dead `True` slots, empty stubs, and corridor-carved custom types, and because no distilled human-checkable proof yet exists independent of Lean 4.33.1 + Mathlib `0df444a3` (with the July 25, 2026 Collatz Lean 4 kernel exploit serving as real precedent that single-kernel trust is non-vacuous), the word **"Lean"** remains load-bearing on the receipt. The earned label is:
   > *A formally checked Lean 4.33.1 / Mathlib `0df444a3` derivation of `Mathlib.RiemannHypothesis` under `{propext, Classical.choice, Quot.sound}` — with source-to-export audit, custom-type classicality audit, and human-readable distillation still OPEN.*

---

## Pass-by-Pass Audit Record

### Pass 1 — Endpoint & Analytic Tail-Closing Roof
* **Files inspected:** `Main.lean`, `Statements.lean`, `Mathlib_RiemannZeta.lean`, `CritLine.lean`, `TopWin.lean`, `Window.lean`, `ZeroFreeOfRpowWindow.lean`, `WindowHypOfRpow.lean`, `LandauZeroFreeCriterion.lean`, `lemmaL.lean`, `poleData.lean`, `landauWindow.lean`, `DivinNOfHypV.lean`, `hostOfFieldOf.lean`, `supplyOfAdmOf.lean`.
* **What we tried to break:**
  1. Shadowed `RiemannHypothesis` or weakened endpoint domain / `s = 1` junk value.
  2. Moving `ε` / quantifier-order swap in `TopWin.lean`.
  3. Vacuous upper bound `R` in `WindowHypOfRpow.lean`.
  4. Pole cancellation across characters in `CharFamily` or `s = 1` pole leakage in `poleData.lean`.
  5. How a finite proof closes the infinite prime tail $x \to \infty$ from sparse windows.
* **What happened:** **All five survived.**
  * `Statements.lean` imports `Mathlib` directly; `Mathlib_RiemannZeta.lean` proves `analyticOn_riemannZeta` on $\mathbb{C} \setminus \{1\}$ and `zeta_eq_tsum_one_div_nat_add_one_cpow` for $\operatorname{Re}(s) > 1$.
  * `HasWindows S la` (`Window.lean` L7–8) requires only arbitrarily late polynomial windows $[Y, Y^\lambda]$. In log scale $u = \log y$, `landauWindow.lean` (L40–167) differentiates the Laplace/Mellin transform $\Phi(s)$ $k \approx \sigma U$ times so $u^k e^{-\sigma u}/k!$ concentrates inside $[U, (1+\delta)U]$, bounds $|\Phi^{(k)}(\sigma+i\gamma)| + \operatorname{Re}\Phi^{(k)}(\sigma)$ using only a one-sided upper bound $g(u) \le R(u)$, and derives a contradiction (`landau_window_contra`, L20–38) against the nearest off-line pole at distance $d < \sigma - \theta$.
  * Binder order in `TopWin.lean` (`level_of_tiedWin`, L68–82) fixes `eD, eL, ε₁` before `ε` and `ε` before `Fm, x1`. `poleData.lean` (L346–367) guarantees strictly positive residue sums $S = \sum_i \frac{a_i}{2}(m_1(i)+m_2(i)) > 0$ (no cancellation) and removes the `s = 1` pole explicitly via `dslope N 1` (L149–229).

### Pass 2 — Top-Level Trusses & Window Generator
* **Files inspected:** `MainTheoremsAll.lean`, `MainTheoremsCritical.lean`, `MainTheorems.lean`, `MainConclusion.lean`, `EveryCharacter.lean`, `ShapeWin.lean`, `SupplyChi.lean`, `ExplicitFormulaErrorOfHostConditions.lean`, `WinPairs.lean`, `pairEx.lean`, `CorGKOf.lean`, `lean-toolchain`.
* **What we tried to break:** Hidden axioms, `sorry`, vacuous plugs in top-level assembly, or degenerate prime-window generation.
* **What happened:**
  * The entire 175,187-file tree funnels cleanly into **14 lines** in `MainConclusion.lean`: one master pillar (`UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter : Row0b recT`) feeds both Column 1 (`vwin_of_row h : VWin` → `SupplyChi` → `supplyOfAdmOf` → `WinPairs` + `QH.pairEx`, genuinely building $[Z, Z^{3/2}]$ windows with prime pairs $(q, d)$, Jacobi conditions, and zero-free character boxes) and Column 2 (`every_character_of_literature_of_vWin` → `EveryCharacter.plugAll` → `ShapeWin` → `TopWin`).
  * **First fossil caught in our pass:** `ShapeWin.lean` L27 (`TopShape True True ...`) and `EveryCharacter.lean` L11 (`shape_of _ _ _ _ (shapeWin hG) trivial trivial h`) expose two dead `True` placeholder slots sitting right on the top truss.

### Pass 3 — Master Pillar (`RowSrc` / `RecTExists` / `VwinOfRow`) & Build/Mathlib Floor
* **Files inspected:** `RowSrc.lean`, `RecTExists.lean`, `VwinOfRow.lean`, `lakefile.toml`, `Mathlib_HurwitzZetaEven.lean`.
* **What we tried to break:** Custom FFI/C shims or compiler plugins in `lakefile.toml`, degenerate Local Langlands structures in `RecTExists.lean`, or defective theta-kernel construction in `HurwitzZetaEven.lean`.
* **What happened:** **All held.**
  * `lakefile.toml` is standard Lake (`autoImplicit = false`, `relaxedAutoImplicit = false`, single upstream `mathlib4` dependency @ `0df444a3`, zero `extern_lib` or custom plugins).
  * `Mathlib_HurwitzZetaEven.lean` constructs `completedHurwitzZetaEven 0 s` directly via Jacobi theta + Poisson summation (`evenKernel_functional_equation`) + Mellin transform (`hurwitzEvenFEPair`).
  * `RecTExists.lean` builds a non-degenerate Local Langlands record (`dim`, `one`, `langlands`, `cusp`, `nu`, `absCentral`, `twist`, `central`, `dual`, `inj`, `depth`, `type`).
  * `RowSrc.lean` reduces the entire master pillar in one line to `galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK`.

### Pass 4 — Literature Layer, Mathlib Junk-Value Floor & Kernel Precedent
* **Files inspected:** `TLiftK.lean`, `HalfIndex_TLiftK.lean`, `TPGHolds.lean`, `GaloisRepresentationsOfThetaLift.lean`, `IntegralStructures_Development.lean`, `WeightOneGeometricRealization.lean`, `LefschetzFixedPointFiniteEtaleCorrespondence.lean`, `DefiniteNHolds.lean`, `FrameEx.lean`, `TopMainZj.lean`, `LitAut.lean`, `WeakOfAtt.lean`, `WindowBoundOfLiteratureLevel.lean`, `ImportsSideExtra.lean`, `TemperedProductOfSquareIntegrable.lean`, `DiscreteSeriesCoefficientsCuspidal.lean`, `Mathlib_AbstractFuncEq.lean`, `Mathlib_MellinEqDirichlet.lean`.
* **What we tried to break:**
  1. Why ~40+ classical literature theorems in `TopMainZj.lean` all took `(O : OpenImageCondition)` as an input.
  2. Mathlib junk-value leakage (`f_modif 1 = 0`, `0 ^ s = 0`, `a / 0 = 0`, non-integrable `integral = 0`) in `AbstractFuncEq.lean` and `MellinEqDirichlet.lean`.
  3. Real Lean 4 kernel soundness boundary (`con-leche`, `lean4export`, historical exploits).
* **What happened:**
  * **Major fossil caught (mechanically verified):** In `TemperedProductOfSquareIntegrable.lean` (L207–344), **62 out of 62** theorems taking `(O : OpenImageCondition)` never read `O.galoisRepOfPolarizedPairLit` (**50** have zero mentions of `O` in their body; **12** only pass `O` to other `*_of_open` wrappers in the same block). Companion 1-line empty stub `DiscreteSeriesCoefficientsCuspidal.lean` (`import Mathlib`) is imported by 4 top-level files.
  * **Mathlib bedrock held:** `AbstractFuncEq.lean` explicitly kills `f_modif 1 = 0` via `subsingleton_singleton.measure_zero` (L345–348); `MellinEqDirichlet.lean` proves `IntegrableOn` (L42–52) and norm-integral `Summable` (L53–66) before Fubini/dominated convergence, and `RiemannZeta.lean` shifts to `n + 1` (L214–219) to avoid `0 ^ s = 0`.
  * **Kernel precedent & `M-SOURCE-PATH` note:** The **July 25, 2026 Collatz incident** established real precedent for a soundness exploit bypassing Lean 4's C++ kernel. Independent checkers (`nanoda`, `lean4lean`, `con-leche` with formal soundness relative to ZFC + inaccessibles and `--compare` against Mathlib) mitigated single-kernel risk, while leaving two visible provenance notes on the receipt: shared downstream dependence on `lean4export` serialization, and shared AI lineage (`con-leche` was built by Joachim Breitner with heavy Claude assistance).

### Pass 5 — Inside the Crown-Jewel Custom Types (`hodgeH` & `TLiftK`)
* **Files inspected:** `OmegaPullOmegaTrace.lean`, `Etale_Lefschetz.lean`, `SchurStep.lean`, `SplitStab.lean`, `GlobalArtinReciprocity.lean`.
* **What we tried to break:** Whether the custom project types behind `WeightOneGeometricRealization` (`hodgeH`) and `TLiftK` (`IsAutRepU`, `IsLift`, `LocPair`) were `geoDegenerate`-style weakened surrogates wearing classical names.
* **What happened:**
  * **Both foundations are genuine math, not fakes:** `hodgeH` / `Etale_Lefschetz` is real Čech cohomology of Kähler differentials $\Omega^j_{X/\mathbb{C}}$ on Mathlib `Scheme.{0}` with étale trace via `Algebra.IsPushout`. `SchurStep.lean` builds genuine adelic theta-lift integrals, Petersson inner products, local intertwining forms, dominant weight shifts, Rallis nonvanishing, and self-dual Heisenberg lattices.
  * **Real `BRIDGE` shape restriction caught (`GoodK` corridor):** `SplitStab.lean` (L16–24) restricts `TLiftK` strictly to `GoodK` CM extensions ($E$ contains $\sqrt{-d}$, $\mathcal{O}_E/\mathcal{O}_F$ everywhere unramified, every inert prime odd with residue norm $> 3$). Valid for the RH prime-window selector (`d % 16 = 7`, `Jacobi(-d, p) = 1`), but non-transportable to general CM fields without proving the omitted ramified and $p = 2, 3$ cases.

---

## Where the Next Load-Bearing Seams Likely Sit

Ranked by signal under `BRIDGE` + `PAL` + `FRONT`:

1. **Corridor-Carving & Weakened-Surrogate Audit Across `GlobalTheory.Published.*` (`BRIDGE` Priority #1)**
   * Pass 5 proved `TLiftK` uses a custom-carved `GoodK` corridor, while `divXFl` / `geoDegenerate` was a broken surrogate. The release bundles **~40+ custom "published literature" propositions** in `LitAut.lean` (`JacquetShalika`, `ClozelPurity`, `DeligneRibet`, `GlobalArtinReciprocity`, `BaseChangeIsobaricN`, `GrothendieckDeformation`, `SiegelWeilStd`, `Row0b`, etc.).
   * **Next test:** Inspect the exact *definitions* (not just names) of `Row0b`, `BaseChangeIsobaricN`, `JacquetShalika`, `ClozelPurity`, and `GlobalArtinReciprocity` to classify each one into: *(a)* full classical theorem, *(b)* RH-corridor-carved theorem (like `GoodK`), or *(c)* `geoDegenerate`-style weakened surrogate.
2. **The Exact Positivity / Window-Assembly Join (`EveryCharacterOfLiteratureOfVWin.lean` + `TPGHolds.lean` + `DefiniteNHolds.lean`)**
   * Pass 1 proved the Landau roof closes RH *if* arbitrarily late $[Z, Z^{3/2}]$ windows with $\operatorname{Gm}(x) \le x^{1/2 + O(\varepsilon)}$ are supplied. Pass 2–5 isolated the master pillar (`TLiftK` + `baseChangeN` + `geoOne_holds`).
   * **Next test:** Trace the exact **numerical exponent budget** across `EveryCharacterOfLiteratureOfVWin.lean` and `ExplicitFormulaErrorOfHostConditions.lean` — specifically how `GoodK` theta lifts + `VWinAt ψ 401` + `LinkN`/`DIVinN` actually defeat the $1/2$ barrier on $[Z, Z^{3/2}]$ windows (this is also the single most valuable target for human comprehension!).
3. **Automated Fossil-Graph Pruner (Scaling the 62/62 Ghost-Parameter Catch)**
   * Across just 55 files we found 62 unused `OpenImageCondition` parameters, 2 `True`/`trivial` slots in `EveryCharacter.lean`, 1 empty stub module, and `anyGeometry`/`geoDegenerate`.
   * **Next test:** Run an automated static pass over the compiled RH declaration graph (`alp-declaration-graph-used-by-rh.json.gz`) flagging every unused argument, `True`/`trivial`/`Empty`/`PUnit` instantiation, and empty stub module on the RH path — separating the true minimal proof skeleton from AI-generated archaeological sediment.
4. **Source-to-Export & Remaining Mathlib Bedrock (`PAL M-SOURCE-PATH`)**
   * Inspect the exact `lean4export` serialization path used by `nanoda` / `lean4lean` / `con-leche`, verify clean-source elaboration (not `.olean`-cached) for all checks, and finish checking the last Mathlib leaf beneath `HurwitzZetaEven.lean` (`JacobiTheta/Bounds.lean` + `MellinTransform.lean`).

---

## Explicit Nonclaims & Evidence Ceilings

* **No defect in the formal derivation of `Main.riemannHypothesis` was established in Passes 1–5.**
* Showing that 62 literature wrappers ignore `O : OpenImageCondition`, that `TopShape` carries two `True` slots, that `DiscreteSeriesCoefficientsCuspidal.lean` is empty, or that `TLiftK` is restricted to `GoodK` **does not invalidate `Main.riemannHypothesis`**. It establishes concrete **graph-honesty, provenance, and `BRIDGE`-transport limits** on what the 17-million-line artifact certifies beyond its endpoint checkmark.
* **External verification reports** (`nanoda`, `lean4lean`, `con-leche`, Andrew Sutherland's tracking page, and the July 25, 2026 Collatz kernel exploit) were gathered via web search and were not independently executed in this workspace.

---

## Pinned Source Inventory (`2026-11-23-rh-tail-audit/sources/`, 55 files)

| Category | Count | Files (all pinned to RH `40e56bab` or Mathlib `0df444a3`) |
| --- | ---: | --- |
| Endpoint & Mathlib Bedrock | 7 | `Main.lean`, `Statements.lean`, `CritLine.lean`, `Mathlib_RiemannZeta.lean`, `Mathlib_HurwitzZetaEven.lean`, `Mathlib_AbstractFuncEq.lean`, `Mathlib_MellinEqDirichlet.lean` |
| Build & Toolchain | 2 | `lakefile.toml`, `lean-toolchain` |
| Tail-Closing Landau Engine | 8 | `TopWin.lean`, `Window.lean`, `ZeroFreeOfRpowWindow.lean`, `WindowHypOfRpow.lean`, `LandauZeroFreeCriterion.lean`, `lemmaL.lean`, `poleData.lean`, `landauWindow.lean` |
| Top Trusses & Window Generator | 13 | `MainTheoremsAll.lean`, `MainTheoremsCritical.lean`, `MainTheorems.lean`, `MainConclusion.lean`, `EveryCharacter.lean`, `ShapeWin.lean`, `SupplyChi.lean`, `ExplicitFormulaErrorOfHostConditions.lean`, `DivinNOfHypV.lean`, `hostOfFieldOf.lean`, `supplyOfAdmOf.lean`, `WinPairs.lean`, `pairEx.lean` |
| Keystone, Theta Lifts, Hodge & Literature Scaffold | 25 | `RowSrc.lean`, `RecTExists.lean`, `VwinOfRow.lean`, `CorGKOf.lean`, `TLiftK.lean`, `HalfIndex_TLiftK.lean`, `TPGHolds.lean`, `GaloisRepresentationsOfThetaLift.lean`, `IntegralStructures_Development.lean`, `WeightOneGeometricRealization.lean`, `LefschetzFixedPointFiniteEtaleCorrespondence.lean`, `OmegaPullOmegaTrace.lean`, `Etale_Lefschetz.lean`, `SchurStep.lean`, `SplitStab.lean`, `DefiniteNHolds.lean`, `FrameEx.lean`, `TopMainZj.lean`, `LitAut.lean`, `WeakOfAtt.lean`, `WindowBoundOfLiteratureLevel.lean`, `ImportsSideExtra.lean`, `TemperedProductOfSquareIntegrable.lean`, `DiscreteSeriesCoefficientsCuspidal.lean`, `GlobalArtinReciprocity.lean` |

*(Exact SHA-256 checksums for all 55 files can be regenerated locally with `Get-FileHash sources\* -Algorithm SHA256`.)*
