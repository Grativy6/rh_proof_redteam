# Pass 6 Red-Team Receipt: Attack on the First Indispensable Bridge

- **Target repo / pinned commit:** `leanprover-community/riemann-hypothesis` @ `40e56bab026552e089d7afcfeff08d2defb9c005` (Mathlib @ `0df444a360eaa60ab8c11dca51a86af692955474`)
- **Date:** 2026-11-23
- **Local source mirror:** `h:\Hearthline_Path\Visitor_cabin\Gemini\2026-11-23-rh-tail-audit\sources\` (92 pinned source files total; 22 new bridge files downloaded and audited in Pass 6)
- **Epistemic rule:** Machine-checked Lean verification is treated strictly as a secondary claim. A failed attack is reported plainly as a failed attack with the exact mathematical mechanism that defeated it; an unresolved obligation is never relabeled a counterexample.

---

## Executive Verdict

**No break in the claimed RH proof was found on the Pass 6 bridge (`galoisLocalGlobalStrong_recParameter` → `TLiftK` → `VWin` → `EveryCharacterOfLiteratureOfVWin` → `ChTop` → `ChBalance` → `ChCore` → `CoreGm` → `TopWin` → `RiemannHypothesis`).**

Every attack we mounted either **failed against an explicit mathematical defense** or uncovered a **genuine classical-scope weakening that does not invalidate any downstream RH inference**:

| Attack Axis | What We Found | RH Impact |
|---|---|---|
| **Q1. Classical Meaning (`GlobalArtinReciprocity`, `BaseChangeIsobaricN`, `Row0`/`Row0b`)** | `GlobalArtinReciprocity` is full textbook class field theory (survived). **`BaseChangeIsobaricN` and `Row0`/`Row0b` ARE genuinely weaker than their full classical namesakes** (`Unr E` + no ramified-inert matching; `Tor ∧ mono0` + `IsQp ∧ TmW ∧ Sqf ∧ mono0` inertia-only). | **Attack on RH defeated (Q4).** Downstream consumers (`ARead` / `PlainRec`, `joinUp`) stay strictly inside the proved domain. |
| **Q2. Quantifier Coverage (`GoodK` corridor; character parity; windows)** | `GoodK` omits non-`HasK` CM fields, ramified extensions, and inert primes above $2, 3$. | **Attack defeated.** `exists_quadratic_CM_ext_split_at` constructs $Q = Y(\sqrt{-p_1 p_2})$ with $-p_1 p_2 \equiv 1 \pmod{8c}$ for arbitrary CM fields $Y$ and arbitrary finite bad sets $T$, lifting into `GoodK` and descending via `patchOne` + `sphDown`. On the character side, `sgc0 = iod` (inertia at auxiliary prime $d$, **not** complex conjugation), so both even and odd primitive Dirichlet characters are covered. |
| **Q3. Numerical Exponent Bridge ($\Lambda.\operatorname{Gm}(x) \le x^{1/2 + (e_D + e_L + 7)\varepsilon}$)** | Independently reconstructed `ch_balance`, `LipW`, `Shares`, `ErrX5at → ErrText`, `proposition_size_bound`, `CoreGm`, and `TopWin` by hand, re-deriving the exact constants `26`, `3/8`, and $e_D + e_L + 7$. | **Attack defeated.** Every inequality, sign, Euler–Mascheroni constant, and exponent step is independently valid without relying on Lean. |
| **Next Load-Bearing Seams (Pass 7)** | Eliminated the outer Fourier/Landau layer; isolated the two remaining unaudited core bridges directly underneath `ChTop` and `VWin`. | **Unopened (`Bridge 7A`: Arakelov/Hida slope-to-`ASK` construction of `FamP`; `Bridge 7B`: `VWin` simultaneous Selmer `VVle ≤ √b` + auxiliary character zero-free windows).** |

---

## Detailed Question-by-Question Receipts

### Q1. Classical Meaning of Load-Bearing Custom Theorems

#### 1.1 `GlobalArtinReciprocity` — **SURVIVED (Full Classical Meaning)**
- **Source:** [`ExistsUniqueHcharOfFiniteOrder.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/ExistsUniqueHcharOfFiniteOrder.lean#L25-L80), [`GlobalArtinReciprocityHolds.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/GlobalArtinReciprocityHolds.lean), [`EveryCharacterOfLiteratureOfVWin.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/EveryCharacterOfLiteratureOfVWin.lean#L243-L244).
- **Audit result:** Quantifies over **all** number fields $E$ and algebraic closures $\Omega$, asserting existence of `art : Ideles E →* TopologicalAbelianization (G E Ω)` satisfying `IsGlobalArtin`: `IsOpenQuotientMap art`, exact kernel `((diagUnits E).range ⊔ infConn E).topologicalClosure`, exact inertia-unit compatibility (`ine`), Frobenius-uniformizer match (`frob`), and decomposition-group closure (`dec`). Also establishes the full bijection `HeckeLAdicCharacter` between finite-order Hecke characters and continuous $\ell$-adic characters. No hidden corridor restriction.

#### 1.2 `BaseChangeIsobaricN` — **GENUINELY WEAKER THAN CLASSICAL BASE CHANGE (Non-Fatal to RH)**
- **Source:** [`BaseChangeIsobaricNOf.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/BaseChangeIsobaricNOf.lean#L21-L46) & [L74–132](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/BaseChangeIsobaricNOf.lean#L74-L132); proved via [`DefiniteNHolds.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/DefiniteNHolds.lean#L5-L6); wired into [`VwinOfRow.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/VwinOfRow.lean#L5), [`TopMainZj.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/TopMainZj.lean#L38-L45), and [`EveryCharacterOfLiteratureOfVWin.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/EveryCharacterOfLiteratureOfVWin.lean#L259-L262).
- **Intended classical claim vs. what the code actually proves:**
  1. **Everywhere-unramified CM hypothesis (`Unr E`):** L41 explicitly restricts the theorem to CM fields satisfying `∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal`. Arbitrary CM extensions $E/E^+$ that ramify at finite places are excluded.
  2. **Zero local base-change matching at ramified inert places:** Inside `Unr E`, `IsBaseChangeN` (L21–37) matches local components at split places (`split`, L36) and Satake parameters at unramified inert places (`inert`, L33–35). At **ramified inert** places (`¬IsSplitAt w ∧ ¬IsUnramU π w`), L127–128 only invokes `local_subquotient` to pick *some* irreducible subquotient $P_w$ of `locProd`, imposing **no** local base-change relation between $\pi_w$ and $P_w$.
- **Why this does not break RH (Q4):** All live RH consumers (`v_window_of_literal_automorphy_n` and `definiteN_of`) take `PositivityTheory.Rg.BcN.BaseChangeIsobaricN` directly as their typed input; solvable/quadratic CM base change pushes representations into everywhere-unramified CM extensions splitting bad places, and downstream arguments inspect only split and unramified inert places.

#### 1.3 `Row0` / `Row0b` (`galoisLocalGlobalStrong_recParameter`) — **GENUINELY WEAKER THAN FULL LOCAL–GLOBAL COMPATIBILITY (Non-Fatal to RH)**
- **Source:** [`GaloisLocalGlobalOfLocalGlobalCompatibility.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/GaloisLocalGlobalOfLocalGlobalCompatibility.lean#L24-L41), [L84–88](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/GaloisLocalGlobalOfLocalGlobalCompatibility.lean#L84-L88), [L157–191](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/GaloisLocalGlobalOfLocalGlobalCompatibility.lean#L157-L191); instantiated in [`IntegralStructures_Development.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/IntegralStructures_Development.lean#L30); consumed via [`MainConclusion.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/MainConclusion.lean#L7-L11), [`VwinOfRow.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/VwinOfRow.lean#L4-L5), [`WeakOfAtt.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/WeakOfAtt.lean#L47-L113), and [`EveryCharacterOfLiteratureOfVWin.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/EveryCharacterOfLiteratureOfVWin.lean#L215-L218).
- **Intended classical claim vs. what the code actually proves:**
  - Full classical local–global compatibility (Caraiani / Shin / Harris–Taylor) asserts isomorphism of Frobenius-semisimplified Weil–Deligne representations $\mathrm{WD}(\rho_{\pi,\iota}|_{G_{E_w}})^{\mathrm{F\text{-}ss}} \cong \mathrm{rec}_T(\pi_w)$ at all finite places $w \nmid \ell$.
  - The actual predicate `Cmp` (L84–88) only establishes:
    1. `x.lpDim = y.lpDim`,
    2. `Tor y → y.mono0 → x = y` (full Weil–Deligne equality **only** when $y$ is toral `Tor` and has trivial monodromy $N = 0$),
    3. `q → IsQp w → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g, deg g = 0 → x.charPol g = y.charPol g` (characteristic-polynomial agreement **only** over $E_w \cong \mathbb{Q}_p$, tamely ramified, squarefree, $N = 0$, and **only** on inertia `deg g = 0` — excluding Frobenius, nontrivial monodromy $N \neq 0$, and wild/non-toral supercuspidals).
  - `Row0b` further narrows `q` by `IsQpBig w n` (L186), though `Row0` is proved first and weakened by `Row0.row0b`.
- **Why this does not break RH (Q4):** In [`WeakOfAtt.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/WeakOfAtt.lean#L49-L53) and [L98–113](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/WeakOfAtt.lean#L98-L113), `PlainRec` and `aRead_of` apply solvable base change (`AUpDown`, `WitA`) to force local components into `WinAt` → `PlainTor` ∧ `Tor` ∧ `mono0`, and line 113 extracts exact equality `x = rc (algNorm σ)` strictly via `k.tor h2 h3`! The restriction is **purpose-built for the RH automorphy-lifting consumer**, not an unclosed logical gap.

---

### Q2. Quantifier Coverage (`GoodK` Corridor & Downstream Character/Window Supply)

#### 2.1 How Arbitrary CM Fields & Bad Primes Escape the `GoodK` Corridor — **ATTACK DEFEATED**
- **Sources:** [`TwoUpOKOfSteps.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/TwoUpOKOfSteps.lean#L13-L33), [`LimOddOfLimFinOdd.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/LimOddOfLimFinOdd.lean#L28-L62), [`ExistsQuadraticCMExtSplitAt.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/ExistsQuadraticCMExtSplitAt.lean#L12-L156), [`RamUnr.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/RamUnr.lean#L9-L27), [`CsdLift.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/CsdLift.lean#L13-L35), [`JoinAll.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/JoinAll.lean#L16-L28), [`PatchOneAlt.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/PatchOneAlt.lean#L57-L106).
- **Mechanism that defeated the attack:**
  1. `TLiftK` / `TwoUpOK` indeed operates only inside the restricted `GoodK` corridor (`HasK E`, everywhere-unramified $E/E^+$, odd inert places with $|k_v| > 3$, even rank $n$ lifted to odd $n + t$ via `he.add_odd`, `TwoUpOKOfSteps.lean` L14–31). Odd ranks are handled directly by `LimFinOdd → LimU → JoinU`; even ranks are handled by `TwoUpOK + SubtractQ → JoinAll`.
  2. To cover an **arbitrary** CM field $Y$ and **arbitrary** target place $w_0$ (including $w_0 \mid 2$, $w_0 \mid 3$, $w_0 \mid \ell$, or ramified places of $Y/\mathbb{Q}$ or $Y/Y^+$), `exists_quadratic_CM_ext_split_at` (`ExistsQuadraticCMExtSplitAt.lean` L31–156):
     - Sets $c = 6 \cdot (\prod_{v \in R} N(v)) \cdot (\prod_{t \in T} N(t)) \cdot (\prod_{v \in R'} N(v))$ (explicitly forcing $2 \mid c$ and $3 \mid c$, where $R$ = ramified places of $Y/Y^+$, $R'$ = ramified places of $Y/\mathbb{Q}$, $T$ = finite bad set containing $w_0$).
     - Chooses two large distinct primes $p_1 < p_2$ with $p_1 > \max(B_0, c)$ and $8c \mid (p_1 p_2 + 1)$ (L41–54), so $a = -p_1 p_2 \equiv 1 \pmod{8c}$.
     - Forms the quadratic CM extension $Q = Y(\sqrt{-p_1 p_2})$.
     - Because $-p_1 p_2 \equiv 1 \pmod{8c}$ is a local square at $2, 3$, and every place in $T \cup R \cup R'$:
       - $Q \supseteq \mathbb{Q}(\sqrt{-p_1 p_2})$ gives `HasK Q` automatically (L90, L98).
       - Every place in $T \cup R \cup R'$ splits completely in $Q/Y$ (hence in $Q/Q^+$, L100–105).
       - At places above $p_1, p_2$, $Q^+ = Y^+(\sqrt{-\delta p_1 p_2})$ absorbs the ramification, so $Q/Q^+$ is unramified everywhere (Abhyankar's lemma, L106–113).
       - Every inert place $w$ of $Q/Q^+$ avoids $c$, so $w \nmid 2$, $w \nmid 3$, $|k_v| \ge 5 > 3$, and $v$ is unramified over $\mathbb{Q}$ (`¬ v ∣ differentIdeal ℤ 𝓞 Q^+`, L119–149), satisfying `InertOK Q.K`.
  3. `joinUp_holds` (`LimOddOfLimFinOdd.lean` L46–51) generates an **infinite** family of such quadratic CM extensions $Q$ splitting $w_0$, lifts $\pi$ via `quadLift` + `csdLift_holds`, obtains Galois representations in the `GoodK` corridor, patches them back down to $E$ via `patchOne_holds`, and descends local–global compatibility at $w_0$ via `sphDown_holds` (`.unr`, `.dR`, `.crys`, `.phi`) because $w_0$ splits completely in $Q/E$ (`Dec E A ≤ (res E Ω Q.K).range`).
  - **Result:** No uncovered CM field, prime ($2, 3$, or ramified), or rank parity.

#### 2.2 Downstream Character & Window Supply — **ATTACK DEFEATED**
- **Sources:** [`ZeroFreeAllOfTopG.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/ZeroFreeAllOfTopG.lean#L26-L34), [`ExplicitFormulaErrorOfHostConditions.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/ExplicitFormulaErrorOfHostConditions.lean#L105-L152), [`charsA.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/charsA.lean#L14-L101), [`RunBaseDimensionLeRankAddGenusTerm.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/RunBaseDimensionLeRankAddGenusTerm.lean#L48-L122), [`supplyOfAdmOf.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/supplyOfAdmOf.lean#L13-L135), [`Imprimitive.lean`](file:///h:/Hearthline_Path/Visitor_cabin/Gemini/2026-11-23-rh-tail-audit/sources/Imprimitive.lean#L5-L35).
- **Check on odd Dirichlet characters:** Although `LandauZeroFreeCriterion.lean` L53–62 and `ExplicitFormulaErrorOfHostConditions.lean` L16 mention `Even`, the live RH path invokes `zeroFreeOn_of_tiedWin_cyc` for `Q := fun _ => True` (ALL primitive characters $\psi$). A potential parity trap in `CharsA` (`ψ sgc0 = 1`) was ruled out directly: `toE_iod` (`charsA.lean` L14) and `BFrame` (`RunBaseDimensionLeRankAddGenusTerm.lean` L48–74, L120) show **`sgc0` is the inertia generator `iod` at the auxiliary prime $d$, NOT complex conjugation `art(-1)`**! Because $d \nmid \mathrm{cond}(\psi)$ is chosen fresh, both even and odd primitive characters satisfy $\psi(\mathrm{iod}) = 1$.
- **Check on imprimitive characters & late windows:** `Imprimitive.lean` L5–35 transfers `ZeroFreeAll` to all Dirichlet characters via $L(\chi, s) = L(\chi^{\mathrm{prim}}, s) \prod_{p \mid N}(1 - \chi^{\mathrm{prim}}(p) p^{-s})$ (factors nonzero for $\operatorname{Re}(s) > 0$). `supplyOfAdmOf.lean` L56–135 supplies arbitrarily late windows $[Y, Y^{3/2}]$ (`la = 3/2`) for every $\psi$.

---

### Q3. Independent Reconstruction of the Numerical Exponent Bridge

We pulled and independently reconstructed every inequality on the live numerical spine:
`ChTop.lean` → `ChBalance.lean` → `ChCore.lean` → `CoreGm.lean` → `WindowInequalityOfArtinInputs.lean` → `LevelGmLeOnFamilyScales.lean` → `TopWin.lean` → `ZeroFreeOfRpowWindow.lean`.

#### Step 1: Exact Fourier Balance (`ChBalance.lean` L200–261)
$$\operatorname{ASK}(D, N, a, t, w) - \operatorname{MAIN}(\ell, a, w) = \operatorname{De}(D, \ell, a, t, w)$$
- Independently verified character orthogonality on $E_0 \times H$ ($|E_0 \times H| = 2|\mathrm{PhiSet}|$):
  - Unramified inert primes $p \notin S_0, p \neq d$: weight $2 \log p$ (`ounram`, `lunram`, L42–75).
  - Split primes $p \in S_0$: inertia and Frobenius lie in `InPhi`, so $K_c = 0$ on $\neg \mathrm{InPhi}$ (`lsplit`, L77–97).
  - Ramified prime $p = d$: $|I_d| = 2$ (`cardI`, L34–40), so $\frac{|E_0 \times H|}{|\mathrm{PhiSet}| \cdot |I_d|} = 1$, giving weight $\log d$ (`ld`, L99–121).
- Independently verified the Laurent expansion of $\left(-\frac{\zeta'}{\zeta}(s)\right)\frac{y^s}{s(s-1)}$ at $s = 1$: since $-\frac{\zeta'}{\zeta}(s) = \frac{1}{s-1} - \gamma + O(s-1)$ and $\frac{y^s}{s} = y + y(\log y - 1)(s-1) + \dots$, the residue is $y \log y - (1 + \gamma) y$ — matching `-(1 + Real.eulerMascheroniConstant) * a` (L211) exactly.
- Independently verified the sign of $+a \cdot \ell(\mathrm{chC})$ (L236–244): for non-principal $\chi$, $\sum_{n \le y} \Lambda(n)\chi(n)(y/n - 1) = G_\chi(y) - y \frac{L'}{L}(1, \chi)$, and the inert-prime indicator $\frac{1 - \chi_{\mathrm{chC}}}{2}$ flips the sign of $-a \frac{L'}{L}(1, \chi_{\mathrm{chC}})$ to $+a \frac{L'}{L}(1, \chi_{\mathrm{chC}})$.

#### Step 2: Weight Flattening, Uniform Lipschitz Bound, and Coset Overweighting (`ChCore.lean` L56–338)
- **Conductor-uniform `LipW` (`th_le`, L117; `GrowthBoundGivesRiemannHypothesis.lean` L58–60):**
  For $\psi \neq 0$, $w \cdot G_\psi(A/w) = \sum_{n \le A/w} \Lambda(n)\chi_\psi(n)(A/n - w) + A \cdot \ell(\psi)$. The term $A \cdot \ell(\psi)$ is **constant in $w$** and vanishes upon differentiation, leaving $|\frac{d}{dw}(w G_\psi(A/w))| \le \sum_{n \le A/w} \Lambda(n) = \psi(A/w) \le 3 A / w$ (and for $\psi = 0$, $|A/w - \psi(A/w)| \le 2 A/w \le 3 A/w$). Thus `‖w G_ψ(A/w) - w' G_ψ(A/w')‖ ≤ (3A / min(w, w')) |w - w'|` holds uniformly across all conductors!
- **Thin places (`th_le`, L124–139):** With $w \le 2b'$, $b' X' \le x b$, $A \ge (x-1)b \ge \frac{2}{3} x b$ ($x \ge 3$), we get $A/w \ge X'/3$, where $X' = \exp(x^{\varepsilon/3})$ and $\theta = \exp(-x^{\varepsilon/8})$ (`ThinScales`).
- **Coset overweighting (`Shares`, `ExplicitFormulaErrorOfHostConditions.lean` L135–140; `charsA.lean` L105–112):**
  Assigning share $\frac{4}{3o+1}$ to $A_0$ and $\frac{3}{3o+1}$ to each of the $o - 1$ non-identity cosets of $A_0$ in $H$ gives, for any nontrivial character $\psi$ of $H/A_0$,
  $$\frac{4}{3o+1} \cdot 1 + \frac{3}{3o+1} \sum_{c \neq 0} \psi(c) = \frac{4 - 3}{3o+1} = \frac{1}{3o+1} > 0,$$
  producing positive weights on all characters in `Λ.KEPT` while averaging over $u_0 \in A_0$ kills every character outside $\Psi(A_0)$ (`sum_A`, `sum_Th`, L28–74).

#### Step 3: Exact Independent Re-Derivation of the Exponent $1/2 + (e_D + e_L + 7)\varepsilon$
1. **`ErrX5at → x^(CErr C * ε) * ErrText` (`ChTop.lean` L54–72, `QuotientSlopeBoundsWith.lean` L45–55, `ErrorFormsWeakWindowsFalse.lean` L16–58):**
   All 8 terms of `ErrX5at` are bounded under `ErrWindows` + `LargeX` by $x^{(e_D + e_L + 3)\varepsilon} \cdot \mathrm{ErrText}$, where $\mathrm{ErrText} = n_T a (1 + m^2/k) + m(B_0 + N_c)$ (`+e_D` from `DIV`, `+e_L` from `LoP`, `+1` from $L, L_a \le 2x^\varepsilon$, `+1` from $\log(1 + x^{c_{HH}}) \le (1 + c_{HH}) x^\varepsilon$, `+1` from $K_{\mathrm{Big}} \le x^\varepsilon$; notably `MLo5`'s $n_T m^2(a/k + b') L$ collapses to $2 n_T a (m^2/k) L$ using $k b' \le a$).
2. **Exact Division by $D = n_T m b \frac{n_{T2}}{2n}$ (`ChCore.lean` L441, `GrowthBoundGivesRiemannHypothesis.lean` L109–122):**
   Given $n_T m b \frac{n_{T2}}{2n}(G_x - 4 x^{1/2+\varepsilon}) \le x^{C\varepsilon} \mathrm{ErrText} + \frac{2 n_T m b}{x}$ under `RestSize` ($a_E \le 2xb$, $n_T \ge \frac{1}{2} x^{-\varepsilon/8} n$, $n_{T2}/n \ge x^{-\varepsilon}$, $x^{1/2-\varepsilon} \le m \le x^{1/2+\varepsilon/2}$, $xm \le k \le n^2 x^{1/2-\varepsilon}$, $x \ge 3$):
   - Shift + $\frac{2 n_T m b / x}{D}$: $4 x^{1/2+\varepsilon} + \frac{4}{x(n_{T2}/n)} \le 4 x^{1/2+\varepsilon} + 4 x^{-1+\varepsilon} \le (4 + 2) x^{1/2+\varepsilon}$ (since $x \ge 3 \implies 4/x < 2\sqrt{x}$).
   - Term 1 ($\frac{x^{C\varepsilon} n_T a_E (1 + m^2/k)}{D}$):
     - From $1$: $\frac{4 x^{1 + C\varepsilon}}{m (n_{T2}/n)} \le 4 x^{1/2 + (C+2)\varepsilon}$.
     - From $m^2/k$: using $k \ge xm$, $\frac{a_E}{mb} \cdot \frac{m^2}{k} \le \frac{2x}{m} \cdot \frac{m}{x} = 2$ (holding even if $\varepsilon > 1$), giving $\le \frac{4 x^{C\varepsilon}}{n_{T2}/n} \le 4 x^{(C+1)\varepsilon} \le 4 x^{1/2 + (C+2)\varepsilon}$.
     - Subtotal $\le 8 x^{1/2 + (C+2)\varepsilon}$.
   - Term 2 ($\frac{x^{C\varepsilon} m \cdot 2 n m b x^\varepsilon}{D}$): $\frac{4 x^{(C+1)\varepsilon} m}{(n_T/n)(n_{T2}/n)} \le \frac{4 x^{(C+1)\varepsilon} x^{1/2 + \varepsilon/2}}{\frac{1}{2} x^{-\varepsilon/8} x^{-\varepsilon}} = 8 x^{1/2 + (C + \frac{21}{8})\varepsilon}$.
   - Term 3 ($\frac{x^{C\varepsilon} m \cdot n_{T2} k b x^{2\varepsilon} / n^2}{D}$): $\frac{2 x^{(C+2)\varepsilon} k}{n \cdot n_T} \le \frac{2 x^{(C+2)\varepsilon} n^2 x^{1/2-\varepsilon}}{\frac{1}{2} x^{-\varepsilon/8} n^2} = 4 x^{1/2 + (C + \frac{9}{8})\varepsilon}$.
   - **Sum of coefficients:** $4 + 2 + 8 + 8 + 4 = \mathbf{26}$ in front of $x^{1/2 + (C + \frac{21}{8})\varepsilon}$.
   - Applying `26 ≤ x^(3 * ε / 8)` (`SizeWindows` L117):
     $$26 \cdot x^{1/2 + (C + \frac{21}{8})\varepsilon} \le x^{\frac{3}{8}\varepsilon} \cdot x^{1/2 + (C + \frac{21}{8})\varepsilon} = x^{1/2 + (C + 3)\varepsilon}.$$
3. **Final `+1` (`CoreGm.lean` L21–74 & `SigALe.lean` L38–60):**
   With $C = e_D + e_L + 3$, adding `SigA ≤ 4 * Λ.o * x^(1/2 + ε)` and applying `1 + 4 * Λ.o ≤ x^ε` gives
   $$\Lambda.\operatorname{Gm}(x) \le x^{1/2 + (e_D + e_L + 7)\varepsilon}.$$
4. **Window-to-Zero-Free (`TopWin.lean` L68–81 & `ZeroFreeOfRpowWindow.lean`):**
   For any hypothetical zero $s$ with $\operatorname{Re}(s) > 1/2$, choosing $\varepsilon$ via `exists_small_eps` forces $1/2 + (e_D + e_L + 7)\varepsilon < \operatorname{Re}(s)$, contradicting `FormBAt (3/2)`.

**Result:** Every single inequality and constant (`26`, `3/8`, $e_D + e_L + 7$) survived independent hand reconstruction.

---

## Investigative Lens Notes (`PAL` / `APCI` / `BRIDGE` / `FRONT`)

- **`BRIDGE` (Shape/Interface Compatibility):** Confirmed two real classical-vs.-formal interface weakenings (`BaseChangeIsobaricN` and `Row0`/`Row0b`), then proved both are **load-compatible** with their live RH consumers — illustrating why a shape discrepancy in an internal theorem name is *not* automatically a break in the global conclusion.
- **`APCI` (Pre-Cut Adequacy & Selection):** The `GoodK` corridor looked like a classic pre-cut restriction, and Pass 6 proved that `exists_quadratic_CM_ext_split_at` + `patchOne` + `sphDown` genuinely close the adequacy gap across all CM fields, primes ($2, 3$, ramified), and rank parities.
- **`PAL` / `FRONT` (Resource/Quantitative Certification Wall):** The outer Fourier–Landau certification wall (`ChTop` → `RH`) holds cleanly; the **entire** nontrivial square-root cancellation ($1/m \approx x^{-1/2}$ relative to $\operatorname{Main}$) has now been cornered behind `SizeData₂` / `FamP` (`ShapeWin.lean`) and `VWin` (`WindowBoundOfLiteratureLevel.lean`).

---

## Next Load-Bearing Bridges for Pass 7

With the outer Fourier/Landau layer and the `GoodK`/`Row0b`/`BaseChangeIsobaricN` corridor interfaces verified as load-bearing and unbroken, **two deep core bridges remain unaudited** and should be the exact targets of Pass 7:

1. **Bridge 7A — The Arakelov/Hida Slope-to-`ASK` Bridge (`ShapeWin.lean` → `each_unit_bound_statement` → `FamP` construction):**
   - How does the release actually construct a live `FamP ε` (`Hyps`, `GlobalTheory.Fc.shape_of`, `linkDIVt_closedK`, `link_eta`, `link_gl`, `link_alt`) satisfying all 11 fields of `SizeData₂` (`QuotientSlopeBoundsWith`, `EComp5`, `Count5`, `LossBounds`, `DIV`, `SlopeIneq`, `HHBound`, etc.) together with `BNBounds` ($B_0 \le 2 n m b x^\varepsilon$, $N_c \le (n_{T2}/n)(k/n) b x^{2\varepsilon}$) and `ErrWindows` (`(etaBar + 4 √eBar) * x^cHH * b ≤ K x^ε (nT a)`)?
   - Specifically check whether `ASK(u_0) - Ga(u_0) ≤ LoP(C)` and `DIV` genuinely extract $\sim x^{-1/2}$ savings from Arakelov geometry without any hidden circularity or degenerate witness (and confirm `compl` in `PChain.lean` L163–300 is strictly an off-path consistency helper).
2. **Bridge 7B — The `VWin` Selmer (`VVle ≤ √b`) & Auxiliary-Character Window Bridge (`WindowBoundOfLiteratureLevel.lean` → `VWin` → `supplyOfAdmOf`):**
   - Independently audit how `VWinAt ψ 401` (`count_i`, `countII_and_countIII`, `count_v`, `katoTwoW`, `sp4In0`) simultaneously bounds the Shafarevich–Tate / Selmer sum $\sum_\ell \log \ell \sum_{e=1}^{t-1} \mathrm{shaLen}(\ell, e) \le \sqrt{b}$ (`VVle`, `DivinNOfHypV.lean` L10–57) **and** supplies pointwise bounds $\|G_\theta(x)\| \le x^{1/2 + \varepsilon}$ (`H.BoundedCharsPointwise`, `ExplicitFormulaErrorOfHostConditions.lean` L149) for all auxiliary characters $\theta \in \Psi(A_0) \setminus \mathrm{KEPT}$ at every $x \in [Y, Y^{3/2}]$.
