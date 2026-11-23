# RH Release Adversarial Tail & Endpoint Audit

**Date:** 2026-11-23  
**Workspace:** `h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/`  
**Pinned RH release:** `leanprover-community/riemann-hypothesis` @ `40e56bab026552e089d7afcfeff08d2defb9c005`  
**Pinned Mathlib:** `leanprover-community/mathlib4` @ `0df444a360eaa60ab8c11dca51a86af692955474`

## 1. Local Source Inventory (`sources/`)

| Local File | Upstream Path | Role in Chain |
| --- | --- | --- |
| `Main.lean` | `src/Main.lean` | Exports `riemannHypothesis : RiemannHypothesis := rhOfAll` |
| `Statements.lean` | `src/Statements.lean` | Imports `Mathlib`; defines `RiemannZetaZerosOnLine`, GRH statements |
| `Mathlib_RiemannZeta.lean` | `Mathlib/NumberTheory/LSeries/RiemannZeta.lean` | Defines `riemannZeta`, `RiemannHypothesis`, Dirichlet series & analytic continuation |
| `CritLine.lean` | `src/Formalism/GammaFactorNonvanishing/CritLine.lean` | Specializes `EveryCharacter` to `χ = 1 (mod 1)` + reflection |
| `TopWin.lean` | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean` | Quantifier binder order from windowed Chebyshev bound to `ZeroFreeLevel` |
| `Window.lean` | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Window.lean` | Defines `HasWindows`, `FormBAt`, `LandauWinAt` |
| `ZeroFreeOfRpowWindow.lean` | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean` | Entry point from `Gm F y ≤ C * y ^ θ` on `[Y, Y^(1+δ)]` to `ZeroFree F θ` |
| `WindowHypOfRpow.lean` | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/WindowHypOfRpow.lean` | Converts pointwise power bound on `[Y, Y^(1+δ)]` into integral `WindowHyp` |
| `LandauZeroFreeCriterion.lean` | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean` | Defines `gm`, `zeroSet`, `PoleData`, `WindowHypU`, `GmLevel` |
| `lemmaL.lean` | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/lemmaL.lean` | Combines `poleData`, `landau_window`, and `Re(s) ≥ 1` nonvanishing |
| `poleData.lean` | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean` | Constructs meromorphic Laplace/Mellin transform `Φ` with nonzero poles at `zeroSet F` |
| `landauWindow.lean` | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean` | **Core tail-closing contradiction**: concentrates `u^k e^{-σu}/k!` on `[U, (1+δ)U]` |
| `DivinNOfHypV.lean` | `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean` | Converts `HypV` / `VVle` finiteness into `DIVinN` |
| `hostOfFieldOf.lean` | `src/Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean` | Uniform threshold `x0` assembly (7 thresholds maxed before scale `s` enters) |
| `supplyOfAdmOf.lean` | `src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean` | Supplies `HostExW (3/2)` windows from `VWinAt ψ 401` and `admitted` |

## 2. Adversarial Checks Performed (Pass 1)

### Attack A — Endpoint Definition / Shadowing (`Main.lean` → `Statements.lean` → `Mathlib_RiemannZeta.lean`)
* **Question:** Does `Main.riemannHypothesis` secretly refer to a weakened or shadowed zeta function?
* **Result:** **SURVIVED (airtight).** `Statements.lean` imports `Mathlib` directly. `Mathlib_RiemannZeta.lean` proves `analyticOn_riemannZeta` on `{1}ᶜ`, `zeta_eq_tsum_one_div_nat_add_one_cpow` for `1 < re s`, functional equation, and residue 1 at `s = 1`. By uniqueness of analytic continuation, this is Riemann's 1859 zeta function.

### Attack B — Tail-Closing Logic (`TopWin.lean` → `WindowHypOfRpow.lean` → `poleData.lean` → `landauWindow.lean`)
* **Question:** How does a finite proof close the infinite tail `x → ∞`, and can a loophole (moving `ε`, vacuous upper bound `R`, pole cancellation across characters, or `s = 1` pole) break it?
* **Result:** **SURVIVED (airtight).**
  1. **No moving threshold:** In `TopWin.lean` (`level_of_tiedWin`, L68–82), `eD, eL, ε₁` are fixed before `ε` is chosen from `min (s.re - 1/2) (1/2)`, and `ε` is fixed before `Fm` and `x1`.
  2. **One-sided upper bound is genuinely sufficient:** `landau_window_key` + `landau_window_ineq` uses Landau's positivity trick (`|Φ^(k)(σ+iγ)| + Re(Φ^(k)(σ)) ≤ 2 ∫ u^k R(u) e^{-σu} du`), where `u^k e^{-σu}/k!` concentrates exponentially inside `[U, (1+δ)U]` for `k ≈ σU` (`landau_tails`).
  3. **No pole cancellation:** `poleData.lean` (L346–367) sums `F.a i / 2 * (m1 i + m2 i)` with `F.a i > 0` and `m1 i, m2 i : ℕ` (at least one `≥ 1`), guaranteeing strictly nonzero residue at every `ρ ∈ zeroSet F` (and strictly positive real residue if `ρ ∈ ℝ`).
  4. **Pole at `s = 1` properly removed:** For `χ = 1`, `poleData_char` multiplies by `(s - 1)` and divides via `dslope N 1` (L149–229).

## 3. Next Live Adversarial Targets
1. **Trust boundary / kernel & axioms:** Verify `#print axioms Main.riemannHypothesis` and independent kernel replay (`nanoda` / `lean4lean` / `con-leche`) from clean source (ruling out `native_decide`, `Lean.ofReduceBool`, `@[implemented_by]`, or Lean 4.33.1 kernel bugs).
2. **Where the windows actually come from:** Trace `supplyOfAdmOf.lean` (`VWinAt ψ 401`, `QH.pairEx`, `ChebyshevInequalityOnWindows`) downward to see the exact arithmetic engine that produces arbitrarily late windows `[Y, Y^(3/2)]` with `Gm ≤ x^(1/2 + O(ε))`.

---

## 4. Pass 2 — Trusses & Master Columns (`Main.lean` down to `RowSrc.lean`)

### Additional Downloaded Files (`sources/`)
* `MainTheoremsAll.lean`, `MainTheoremsCritical.lean`, `MainTheorems.lean`, `MainConclusion.lean`
* `EveryCharacter.lean`, `ShapeWin.lean`, `SupplyChi.lean`, `ExplicitFormulaErrorOfHostConditions.lean`
* `WinPairs.lean`, `pairEx.lean`, `CorGKOf.lean`, `lean-toolchain` (`leanprover/lean4:v4.33.1`)

### The Complete Top-Level Structural Spine
```
Main.lean (riemannHypothesis : RiemannHypothesis)
  └─ MainTheorems.lean (rhOfAll := Formalism.VW.rh_of_every allChi)
       └─ MainConclusion.lean (everyCharacter := everyCharacter_of_row galoisLocalGlobalStrong_recParameter)
            ├─ Pillar 0 (Single Master Foundation):
            │    galoisLocalGlobalStrong_recParameter : Row0b (IsRecT)   [RowSrc.lean]
            │    + recTExists                                            [RecTExists.lean]
            ├─ Column 1 (Window / Sha-Bound Generator):
            │    vwin_of_row h : VWin                                    [VwinOfRow.lean]
            │      └─ supplyChi → supplyOfAdm → winPairs + QH.pairEx    [SupplyChi, WinPairs, pairEx]
            │           Produces arbitrarily late windows [Z, Z^(3/2)] with prime pairs (q, d),
            │           Jacobi conditions, character boxes (GoodQ/GoodD), and Sha/VVle bounds.
            └─ Column 2 (Automorphic / Divisibility / Green Engine):
                 every_character_of_literature_of_vWin                   [EveryCharacterOfLiteratureOfVWin.lean]
                   └─ UpperTheory.Top.plugAll (hG : Green) (hV : VWin) h [EveryCharacter.lean]
                        └─ shapeWin hG → LinkN / LinkDIV / LinkIrr / LinkG / LinkAlt [ShapeWin.lean]
                             └─ TopWin.level_of_tiedWin → ZeroFreeOfRpowWindow → landauWindow
```

### Pass 2 Adversarial Findings
1. **No hidden axioms, `sorry`, or vacuous shortcuts** in any top-level assembly file (`Main` → `MainTheorems` → `MainConclusion` → `EveryCharacter` → `ShapeWin` → `SupplyChi` → `WinPairs` → `pairEx`).
2. **Dead placeholder slots visibly exposed:** `EveryCharacter.lean` L11 literally passes `trivial trivial` into `TopShape True True ...` (`ShapeWin.lean` L27) — confirming directly in source why decorative `True` predicates (`anyGeometry`, unused `TopShape` slots) carry zero logical load while real weight sits in `Green`, `VWin`, `LinkN`, and `galoisLocalGlobalStrong_recParameter`.
3. **Single deepest load-bearing column identified:** Almost everything funnels through `galoisLocalGlobalStrong_recParameter` (`RowSrc.lean`) → `vwin_of_row` (`VwinOfRow.lean`) + `every_character_of_literature_of_vWin`.

---

## 5. Pass 3 — Master Pillar (`RowSrc` / `RecTExists` / `VwinOfRow`) & Build/Mathlib Floor

### Additional Downloaded Files (`sources/`)
* `RowSrc.lean`, `RecTExists.lean`, `VwinOfRow.lean`, `lakefile.toml`, `Mathlib_HurwitzZetaEven.lean`

### Pass 3 Adversarial Findings
1. **Master Pillar (`RowSrc.lean`):**
   * `galoisLocalGlobalStrong_recParameter : UpperTheory.GalStar.Row0b recT` is proved in one line by `galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK` (ThetaParseval / ThetaKernels).
   * `RecTExists.lean` constructs a complete, non-degenerate Local Langlands record (`dim`, `one`, `langlands`, `cusp`, `nu`, `absCentral`, `twist`, `central`, `dual`, `inj`, `depth`, `type`) from `artEx`, `cuspEx`, and `exists_isLExt` — zero `True` placeholders or axioms.
   * `VwinOfRow.lean` feeds `Row0b (IsRecT)` + `baseChangeN` (`DefiniteNHolds.lean`) into `automorphic_window_of_inputs` to produce `VWin`.
2. **Build & Trust Boundary (`lakefile.toml`):**
   * Clean standard Lake configuration (`autoImplicit = false`, `relaxedAutoImplicit = false`, `--tstack=400000`, `maxHeartbeats = 4000000`).
   * **Single dependency:** upstream `leanprover-community/mathlib4` @ `0df444a360eaa60ab8c11dca51a86af692955474`. Zero custom C/FFI shims, zero `extern_lib`, zero custom plugins.
3. **Mathlib Floor (`Mathlib_HurwitzZetaEven.lean`):**
   * Classical Jacobi theta kernel + Poisson summation (`evenKernel_functional_equation`) + Mellin transform (`hurwitzEvenFEPair`) -> `completedHurwitzZetaEven 0 s` -> `riemannZeta`. Textbook 1859 Riemann construction, zero junk-value loopholes.

### Bottom-Line Status After Passes 1–3
* **Roof (Endpoint + Landau Tail-Closer):** Airtight.
* **Trusses (`Main` → `MainConclusion` → `EveryCharacter` → `ShapeWin` → `WinPairs` → `pairEx`):** Airtight (with two visible dead `True` slots in `EveryCharacter.lean` L11 carrying zero logical load).
* **Master Pillar (`RowSrc` / `RecTExists` / `VwinOfRow`):** Non-degenerate, reduces cleanly to `galoisRepresentations_of_thetaLift tLiftK` + `baseChangeN`.
* **Build & Mathlib Floor (`lakefile.toml` + `HurwitzZetaEven`):** Airtight.
* **Only remaining unverified surface (external to reading source files):** Running an independent kernel (`nanoda` / `lean4lean` / `con-leche`) from clean source and printing `#print axioms Main.riemannHypothesis` to rule out any hidden `native_decide` / `Lean.ofReduceBool` / `@[implemented_by]` or Lean 4.33.1 kernel bug deep in the 175k files.

---

## 6. Pass 4 — Deep Shape-Mismatch Audit (`BRIDGE` Lens: Keystone, Literature Scaffold, Mathlib Junk Values, Kernel Precedent)

### Additional Downloaded Files (`sources/`)
* **Keystone & Literature Scaffold:** `TLiftK.lean`, `HalfIndex_TLiftK.lean`, `TPGHolds.lean`, `GaloisRepresentationsOfThetaLift.lean`, `IntegralStructures_Development.lean`, `WeightOneGeometricRealization.lean`, `LefschetzFixedPointFiniteEtaleCorrespondence.lean`, `DefiniteNHolds.lean`, `FrameEx.lean`, `TopMainZj.lean`, `LitAut.lean`, `WeakOfAtt.lean`, `WindowBoundOfLiteratureLevel.lean`, `ImportsSideExtra.lean`, `TemperedProductOfSquareIntegrable.lean`, `DiscreteSeriesCoefficientsCuspidal.lean`
* **Mathlib Bedrock:** `Mathlib_AbstractFuncEq.lean`, `Mathlib_MellinEqDirichlet.lean`

### Concrete Discrepancies, Corner Cases & Shape Findings

1. **Ghost-Dependency Fossil Across ~40 Classical Theorems (`TemperedProductOfSquareIntegrable.lean` L207–344):**
   * `OpenImageCondition` wraps `RowT` (`Row0b recT`).
   * ~40 classical literature theorems (`elliptic_main_theorem_cm_of_open`, `hecke_tate_functional_equation_of_open`, `global_artin_reciprocity_of_open`, `jacquet_shalika_of_open`, `clozel_purity_of_open`, `deligne_ribet_of_open`, `grothendieck_deformation_of_open`, `bernstein_zelevinsky_finiteness_of_open`, `poitou_tate_normalised_of_open`, etc.) formally accept `(O : OpenImageCondition)` and **completely ignore `O` in their bodies**, delegating directly to unconditional internal theorems (`PositivityTheory.*`, `GlobalTheory.*`).
   * Companion dead artifacts spotted: `DiscreteSeriesCoefficientsCuspidal.lean` is a 1-line empty stub (`import Mathlib`) still imported by `TopMainZj.lean`, `LitAut.lean`, `WindowBoundOfLiteratureLevel.lean`, and `TemperedProductOfSquareIntegrable.lean`.
   * **Shape verdict (`BRIDGE` / `FRONT`):** Does not break formal soundness, but proves the dependency graph preserves unpruned scaffolding fossils that actively mislead human inspection of what depends on what.

2. **The Live `BRIDGE` Seam Inside the Heavyweight Pillars (`TLiftK`, `Lefschetz`, `Row0b`, `Published.*`):**
   * On the surface, `HalfIndex_TLiftK.lean` (L12–24: unitary theta lifts from $U_E(n)$ to $U_E(d)$ on CM fields) and `LefschetzFixedPointFiniteEtaleCorrespondence.lean` (L8–15: holomorphic Lefschetz fixed-point formula on Hodge cohomology $H^{a,b}(Z)$) have rich, classical-looking signatures — **not** trivial `True` predicates.
   * **However**, every single one is stated over **project-internal custom types** (`Spc`, `UA`, `IsAutRepU`, `IsLift`, `hodgeH`, `IsProjOver`, `CuspSub`, `WD`, `IsRecT`) rather than Mathlib types.
   * Under a `BRIDGE` test (changing intent from "derive `Main.riemannHypothesis`" to "reuse `hodgeH` / `TLiftK` / `GlobalTheory.Published.*` as classical math"), none of those custom types are self-certifying by name — just as `DV.Geo` / `divXFl` failed `AsymptoticRiemannRoch`, any subtle weakening in `hodgeH`, `IsAutRepU`, or `IsLift` would be invisible to `Main.riemannHypothesis`'s kernel check while breaking classical transport!

3. **Mathlib Bedrock Junk-Value Audit (`Mathlib_AbstractFuncEq.lean`, `Mathlib_MellinEqDirichlet.lean`):**
   * Checked `f_modif 1 = 0` (`AbstractFuncEq.lean` L244–250, L345–348): explicitly discharged via `subsingleton_singleton.measure_zero`.
   * Checked `0 ^ s = 0` / `a / 0 = 0` (`MellinEqDirichlet.lean` L91–116): explicitly bypassed in `Mathlib_RiemannZeta.lean` L214–219 (`n + 1`), and `hasSum_mellin` explicitly proves `IntegrableOn` (L42–52) and norm-integral `Summable` (L53–66) before swapping sum and integral.
   * **Verdict:** No junk-value leakage found in the Mellin-to-Dirichlet bedrock.

4. **Kernel Soundness Precedent & Trust-Root Audit (`PAL M-SOURCE-PATH`):**
   * **Real precedent:** The **July 25, 2026 Collatz incident** demonstrated a genuine soundness exploit bypassing Lean 4's C++ kernel.
   * **Mitigation & residual seam:** Independent checkers (`nanoda`, `lean4lean`, `con-leche`) were run; `con-leche` handles mutual/nested inductives directly via positivity analysis and has a formal soundness proof relative to ZFC + inaccessibles, plus `--compare` against Mathlib. Residual `M-SOURCE-PATH` notes: external checkers sit downstream of `lean4export` serialization, and `con-leche` itself was developed with heavy Claude assistance (shared AI provenance with the RH author stack, though independently audited by Joachim Breitner / Lean FRO).

---

## 7. Pass 5 — Inside `hodgeH`, `TLiftK` / `IsLift`, and Corridor-Carved Shapes

### Additional Downloaded Files (`sources/`)
* `OmegaPullOmegaTrace.lean`, `Etale_Lefschetz.lean`, `SchurStep.lean`, `SplitStab.lean`, `GlobalArtinReciprocity.lean`

### Pass 5 Findings
1. **`hodgeH` & `Lefschetz` (`OmegaPullOmegaTrace.lean`, `Etale_Lefschetz.lean`) — Genuine, NOT a `geoDegenerate` Surrogate:**
   * Built directly on Mathlib's `AlgebraicGeometry.Scheme.{0}`, `IsAffineOpen`, `Module.Finite`, `Algebra.Etale`, `Algebra.IsPushout`, `KaehlerDifferential`, and Čech cohomology (`cohOn`, `coh.pushforwardEquiv`, `cohOn.pi_res_bijective_of_disjoint`).
   * Zero `True`-placeholder or degenerate-module shortcuts detected.
2. **`TLiftK` / `IsLift` (`SchurStep.lean`, `SplitStab.lean`) — Genuine Adelic Theta Lift, BUT Corridor-Carved (`GoodK`):**
   * `SchurStep.lean` L22–128 defines the genuine adelic theta-lift integral (`∫ g in M.dom, theta om Φ g h * star (φ g) ∂M.μ`), Petersson matrix coefficients (`mc`), local intertwining forms (`LocPair`), dominant weight shift (`IsLiftWt`), and Rallis nonvanishing (`Rallis`, `SchurStep`, `NonVan`).
   * **Real `BRIDGE` shape restriction (`SplitStab.lean` L16–24):** `TLiftK` does **not** hold for arbitrary CM extensions; it is restricted strictly to `GoodK` extensions:
     * `HasK E`: $E$ contains $\sqrt{-d}$ for some $d > 0$,
     * `Algebra.Unramified (𝓞 F) (𝓞 E)`: everywhere unramified,
     * `inert`: every inert prime $v$ satisfies $2 \notin v$ and $|k_v| > 3$ (sidestepping ramified and small-residue-field $p = 2, 3$ cases).
   * Fits the RH prime-window generator (`d % 16 = 7`, `Jacobi(-d, p) = 1`) like lock-and-key, but is not transportable outside `GoodK` without proving the omitted ramified/dyadic/triadic cases.
3. **Complete Fossil-Scaffold Catalog (Passes 1–5):**
   * `anyGeometry` / `geoDegenerate` (`divXFl` fails `AsymptoticRiemannRoch` & `AdmG`; off-path in RH graph)
   * `TopShape True True ... trivial trivial` (`EveryCharacter.lean` L11, `ShapeWin.lean` L27)
   * `OpenImageCondition` ghost argument accepted and ignored by ~40 classical theorems (`TemperedProductOfSquareIntegrable.lean` L207–344)
   * Empty 1-line stub `DiscreteSeriesCoefficientsCuspidal.lean` (`import Mathlib`) still imported by 4 top-level files

---

## Pass 6 — Attack on First Indispensable Bridge (2026-11-23)

Full receipt: [`2026-11-23-gemini-pass6-bridge-attack.md`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/2026-11-23-gemini-pass6-bridge-attack.md) (22 additional pinned files downloaded; 92 files total in `sources/`).

* **Verdict: No break found on the Pass 6 bridge.** Every attack either failed against an explicit mathematical defense or isolated a classical-naming restriction that does not break downstream RH inferences:
  1. **Classical Meaning (Q1 / Q4):**
     * `GlobalArtinReciprocity` (`ExistsUniqueHcharOfFiniteOrder.lean` L25–80): **full classical strength** (survived).
     * `BaseChangeIsobaricN` (`BaseChangeIsobaricNOf.lean` L21–46, L74–132): **genuinely weaker than full classical base change** — restricted to everywhere-unramified CM extensions `Unr E`, and imposes zero local base-change matching at ramified inert places (`local_subquotient` at L127–128). **Defeated on RH impact:** live consumers stay strictly inside `Unr E` and inspect only split and unramified inert places.
     * `Row0` / `Row0b` (`GaloisLocalGlobalOfLocalGlobalCompatibility.lean` L84–88, L157–191): **genuinely weaker than full local–global compatibility** — exact Weil–Deligne equality only when `Tor y ∧ y.mono0`, plus inertia-only charpoly agreement under `IsQp ∧ TmW ∧ Sqf ∧ mono0`. **Defeated on RH impact:** `WeakOfAtt.lean` L49–53, L98–113 (`PlainRec` / `ARead`) pushes local components into `Tor ∧ mono0` via solvable base change and extracts equality strictly via `k.tor h2 h3`.
  2. **Quantifier Coverage (Q2):**
     * **`GoodK` corridor — ATTACK DEFEATED:** `ExistsQuadraticCMExtSplitAt.lean` L12–156 constructs $Q = Y(\sqrt{-p_1 p_2})$ with $-p_1 p_2 \equiv 1 \pmod{8c}$ ($2 \mid c, 3 \mid c$, all bad/ramified places dividing $c$) for arbitrary CM fields $Y$ and finite bad sets $T$, automatically guaranteeing `HasK Q`, everywhere-unramified $Q/Q^+$, and `InertOK Q.K` ($|k_v| \ge 5$). `LimOddOfLimFinOdd.lean` L46–51 (`joinUp_holds`) patches back down to $E$ (`patchOne`) and descends local–global compatibility (`sphDown`) since $w_0$ splits completely in $Q/E$.
     * **Character parity & windows — ATTACK DEFEATED:** `ZeroFreeAllOfTopG.lean` L26–34 covers `Q := fun _ => True` (all primitive characters); `charsA.lean` L14 (`toE_iod`) + `RunBaseDimensionLeRankAddGenusTerm.lean` L48–74 confirm `sgc0 = iod` (inertia at fresh auxiliary prime $d$, NOT complex conjugation `art(-1)`), so both even and odd Dirichlet characters enter `Xp`; `Imprimitive.lean` L5–35 covers all imprimitive characters; `supplyOfAdmOf.lean` L56–135 supplies arbitrarily late `[Y, Y^(3/2)]` windows.
  3. **Numerical Exponent Bridge (Q3) — ATTACK DEFEATED:**
     * Independently reconstructed `ChBalance.lean` (exact signs, $-(1+\gamma)a$, $+a\frac{L'}{L}(1,\chi_{\mathrm{chC}})$, ramified $p=d$ weight 1 vs. inert weight 2), `ChCore.lean` (conductor-uniform `LipW` via $\frac{d}{dw}(A\cdot\ell(\psi)) = 0$, `Shares` coset overweighting $\frac{4-3}{3o+1} = \frac{1}{3o+1}$), `ChTop.lean` (`ErrX5at → x^((e_D+e_L+3)ε) ErrText`), `proposition_size_bound` (re-derived exact constant $4+2+8+8+4 = \mathbf{26}$ and fraction $\frac{21}{8} + \frac{3}{8} = 3$), and `CoreGm.lean` (final $+1$ from `1 + 4 o ≤ x^ε` yielding $x^{1/2 + (e_D + e_L + 7)\varepsilon}$).
  4. **Next Load-Bearing Seams (Pass 7):**
     * **Bridge 7A:** Arakelov/Hida slope-to-`ASK` construction of `FamP` (`ShapeWin.lean`, `QuotientSlopeBoundsWith`, `each_unit_bound_statement`, `BNBounds`, `ErrWindows`).
     * **Bridge 7B:** `VWin` simultaneous Selmer/Sha bound `VVle ≤ √b` (`DivinNOfHypV.lean`) + pointwise auxiliary character bounds `H.BoundedCharsPointwise` across `[Y, Y^(3/2)]` windows (`WindowBoundOfLiteratureLevel.lean`, `supplyOfAdmOf.lean`).
