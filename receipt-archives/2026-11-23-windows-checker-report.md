# Windows lean4lean rejects the 4.35.0 standard library in direct module mode

**Hearthline, 23 November 2026 · tested on Dust at Chris Pang’s request.** Chris supplied a screenshot crediting Gemini 4 Neon with reporting that the Windows Lean 4.35.0 bundle rejects its own `Init.Prelude.olean`. I reproduced that exact symptom with a fresh official Windows archive. The same external checker accepted a named proof through the bundle's export interface. The RH project pins an earlier compiler, for which I rebuilt the independently written checker and tested a source file directly involved in the disappearing-tail objection.

## Results observed locally

| Compiler and input | Executable and mode | Observed result |
| --- | --- | --- |
| Official Windows 4.35.0, stock `Init.Prelude` | Bundled `lean4lean.exe Init.Prelude` | Exit 1. “incompatible header” while reading the bundle's own `lib/lean/Init/Prelude.olean`. |
| Same installation and module | Bundled `leanchecker.exe Init.Prelude` | Exit 0. |
| 4.35.0, export of `theorem palStockCheck : (1 : Nat) = 1 := rfl` | Bundled `lean4lean.exe --import PalStockCheck.ndjson` | Exit 0, seven declarations checked. |
| Same export bytes | Bundled `leanchecker.exe --from-export PalStockCheck.ndjson` | Exit 0. The export contains a theorem record whose name resolves to `palStockCheck`. |
| Official Windows 4.33.1, stock `Init.Prelude` | Native `leanchecker.exe` and separately built `lean4lean.exe` | Both exited 0. The latter reported 1,975 declarations. |
| 4.33.1, newly compiled original RH module containing `fnConj` | Separately built `lean4lean.exe -v` on that module | Exit 0, 183 declarations replayed, including `fnConj` and `sgStar`. Existing compiled dependencies supplied the import environment. |

The 4.35.0 archive SHA-256 was `893fde3f52b48c647e3edcf33844cbb61f8ef70fcd88e0536bfc83f29844081e`. The compiler reported `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Its two readers were given the same explicit library path. The export was 11,115 bytes with SHA-256 `11c841df603ac0ca7ff2c32a3f9ca3399ee7459c928a2d074bee9f7818b2a0ed`. [Official release](https://github.com/leanprover/lean4/releases/tag/v4.35.0) · [Commands, executable hashes and captured results](2026-11-23-windows-lean435.json)

The upstream tracker has a separate report of the same direct-read symptom on **Linux 4.36.0**. A maintainer explained that the bundled checker is supplied for `lake check` on exported proofs and that compiled-module reading is not necessarily supported in that distribution. The tagged 4.35.0 Lake source invokes `lean4lean --import` for an export. The Windows direct-read failure is reproducible. Calling it a defect in the advertised export operation would require a failing export test. [Upstream issue](https://github.com/leanprover/lean4/issues/16679) · [Maintainer’s clarification](https://github.com/leanprover/lean4/issues/16679#issuecomment-7116802671) · [Lake’s tagged checker command](https://github.com/leanprover/lean4/blob/v4.35.0/src/lean/lake/Lake/CLI/Check.lean#L571-L580)

## The RH toolchain

The pinned RH release specifies `leanprover/lean4:v4.33.1`. Andrew Sutherland reports separately building `digama0/lean4lean` at `67f63b0c` with that compiler for his module checks. On Dust the official 4.33.1 archive matched its published digest. I built checker commit `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` with the explicit 4.33.1 Lake executable and the dependency commit in its manifest. I compiled the unmodified RH source for `Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice` in an isolated output tree. Its `.lean` and `.olean` hashes and the replay mode are recorded below. A broader exploratory `DataN` module replay timed out after 210 seconds and supplies no result. [RH toolchain pin](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/lean-toolchain) · [Sutherland’s separately reported full run](https://math.mit.edu/~drew/grh/) · [Checker source and replay modes](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Main.lean#L127-L148) · [Our pinned-module record](2026-11-23-pinned-module-replay.json) · [Our complete module log](2026-11-23-pinned-module-replay.log)

## Reproduce the Windows experiment

Unpack the official `lean-4.35.0-windows.tar.zst`. From the audit checkout run the following in PowerShell, substituting the actual paths. The script uses temporary files and the specified toolchain executables.

```powershell
python receipt-archives/check_windows_lean435.py 'C:\path\lean-4.35.0-windows' --archive 'C:\path\lean-4.35.0-windows.tar.zst'
```

For the matched module check, build the pinned checker with Windows 4.33.1, enter the pinned RH build environment with its compiled dependencies, and give that checker the full module name above. Its normal mode replays the target from imports. The single-module log covers this target. The mathematical claim that an actual theta section transports correctly is tested separately on paper. [Windows reproduction script](check_windows_lean435.py) · [Independent mathematical check](2026-11-23-independent-theta-check.md)
