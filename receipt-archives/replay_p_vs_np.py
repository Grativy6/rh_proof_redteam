"""Recompile the APCI P/NP double feature from pinned definitions, then test the three bare goals."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from urllib.request import urlopen

ROOT = Path(__file__).resolve().parent
PIN = "86a2f58a4d7a3a0637d15d5b2ce627592b54b956"
UPSTREAM = {
    "FormalConjecturesForMathlib.Computability.BitstringEncoding":
        "2f9fb7cb92e9b7a0fd4f16cec9f7b911d08ae28c155440b980546d10a13b8764",
    "FormalConjecturesForMathlib.Computability.Complexity":
        "aca88dff2908a54d4995ce5a7e65066fca64fb291d834b349c630903ae325bd5",
}
PROBE = """
import Lean
import PvsNPDoubleFeature
open Lean Elab Command in
run_cmd do
  if (← getEnv).contains `ComplexityTheory.P_ne_NP then
    throwError "Imported the upstream open-conjecture declaration"
  for n in [`Hearthline.Punchline.iProvedPEqualsNP, `Hearthline.Punchline.iProvedPNotEqualsNP,
            `Hearthline.Punchline.atLeastOneHeadline, `Hearthline.Punchline.noDoublePrize] do
    let axs ← collectAxioms n
    for a in axs do
      unless #["propext", "Classical.choice", "Quot.sound"].contains a.toString do
        throwError "Unexpected axiom {a} in {n}"
"""


def call(args, work, env, reject=None):
    completed = subprocess.run(args, cwd=work, env=env, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
    if reject is not None:
        if completed.returncode != 1 or "type mismatch" not in completed.stdout.lower() or reject not in completed.stdout:
            raise RuntimeError(f"Expected explicit type mismatch for {reject}.\n{completed.stdout}")
        print(completed.stdout.strip(), flush=True)
    elif completed.returncode:
        raise RuntimeError(f"{args} returned {completed.returncode}\n{completed.stdout}")
    return completed.stdout



EXPORT_PIN = "15f6055e299ad5b89345e533cc2192f4cc00f659"
EXPORT_FILES = {"Export.lean": "1c60d571dc24bfb99e7cbb218d8d489919bbc871238f6db9c76248521fbea998",
                "Main.lean": "bd8e350903f1382b25fe767f9086dd9882000f01085f7046ea06545e7848842a"}
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
# Lean 4.36's comparator-from-export test names these primitives for comparison in both exports.
PRIMITIVES = """propext Quot.sound Classical.choice Quot Quot.mk Quot.lift Quot.ind
Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor
Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String
String.mk Char optParam autoParam semiOutParam outParam""".split()
WRITTEN = [
    ("iProvedPEqualsNP", "(P = NP) = (P = NP)", "rfl"),
    ("iProvedPNotEqualsNP", "(P ≠ NP) = (P ≠ NP)", "rfl"),
    ("atLeastOneHeadline", "P = NP ∨ P ≠ NP", "Classical.em _"),
    ("noDoublePrize", "¬ (P = NP ∧ P ≠ NP)", "fun h => h.2 h.1"),
]


def pinned_bytes(repository, revision, path, expected):
    with urlopen(f"https://raw.githubusercontent.com/{repository}/{revision}/{path}", timeout=25) as stream:
        data = stream.read()
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError(f"Source hash mismatch for {repository}/{path}")
    return data


def write_exports(lean, work, env, destination):
    destination = destination.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    exporter = work / "exporter"
    exporter.mkdir(exist_ok=True)
    for name, digest in EXPORT_FILES.items():
        (exporter / name).write_bytes(pinned_bytes("leanprover/lean4export", EXPORT_PIN, name, digest))
    env = dict(env, LEAN_PATH=str(exporter) + os.pathsep + env["LEAN_PATH"])
    call([lean, "-j", "2", "-o", "Export.olean", "Export.lean"], exporter, env)

    def export(module, names, output):
        args = [lean, "-j", "2", "--run", "Main.lean", module, "--", *names, *PRIMITIVES]
        # Finish the export in the scratch directory before replacing its destination.
        temp_output = work / (module + ".ndjson")
        with temp_output.open("wb") as out:
            subprocess.run(args, cwd=exporter, env=env, stdout=out, check=True)
        shutil.copyfile(temp_output, output)

    def qualified(items):
        return ["Hearthline.Punchline." + entry[0] for entry in items]

    export("PvsNPDoubleFeature", qualified(WRITTEN), destination / "double-feature.ndjson")
    # Placeholder bodies here specify the two independent challenge statements. They are never
    # imported by the submitted solution, whose separate export allows only AXIOMS above.
    challenges = {"AsWritten": WRITTEN, "BareYes": [(WRITTEN[0][0], "P = NP", "by sorry")],
                  "BareNo": [(WRITTEN[1][0], "P ≠ NP", "by sorry")]}
    for label, items in challenges.items():
        module = "Challenge" + label
        challenge = ("import FormalConjecturesForMathlib.Computability.Complexity\n"
                     "namespace Hearthline.Punchline\nopen ComplexityTheory\n"
                     + "".join(f"theorem {name} : {ty} := {body}\n" for name, ty, body in items)
                     + "end Hearthline.Punchline\n")
        (work / (module + ".lean")).write_text(challenge, encoding="utf-8")
        call([lean, "-j", "2", "-o", module + ".olean", module + ".lean"], work, env)
        export(module, qualified(items), destination / (module + ".ndjson"))
        (destination / (module + ".lean")).write_text(challenge, encoding="utf-8")
        config = {"challenge_module": module, "solution_module": "PvsNPDoubleFeature",
                  "theorem_names": qualified(items), "permitted_axioms": AXIOMS,
                  "external_kernels": {"nanoda": ["nanoda_bin"]}}
        (destination / (label + ".json")).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
    print("Wrote the four exports and three comparison challenges.", flush=True)


def judge_exports(folder, binaries):
    folder, binaries = folder.resolve(), binaries.resolve()
    env = dict(os.environ, PATH=str(binaries) + os.pathsep + os.environ.get("PATH", ""),
               LEAN_SYSROOT=str(binaries.parent))
    for label in ("AsWritten", "BareYes", "BareNo"):
        args = [binaries / "lake", "comparator", "--config", label + ".json",
                "--challenge-from-export", "Challenge" + label + ".ndjson",
                "--solution-from-export", "double-feature.ndjson"]
        run = subprocess.run(args, cwd=folder, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             encoding="utf-8", errors="replace")
        expected = 0 if label == "AsWritten" else 1
        marker = "Your solution is okay!" if expected == 0 else "theorem statement do not match"
        if run.returncode != expected or marker not in run.stdout:
            raise RuntimeError(f"{label} returned {run.returncode}\n{run.stdout}")
        print(f"{label} (exit {run.returncode}): {run.stdout.strip()}", flush=True)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--lean-bin", required=True, type=Path, help="Lean 4.33.1 bin directory")
    cli.add_argument("--packages", type=Path, help="Matched Lake packages or restored binary libraries; otherwise use the inherited LEAN_PATH")
    cli.add_argument("--lean4lean", type=Path, help="Independent checker built for Lean 4.33.1")
    cli.add_argument("--exports", type=Path, help="Write the solution export, fixed challenges and comparator configs to this directory")
    cli.add_argument("--judge-bin", type=Path, help="Run the sandboxed Linux comparator (tested with Lean 4.36.0); requires --exports")
    args = cli.parse_args()
    if args.judge_bin and not args.exports:
        cli.error("--judge-bin requires --exports")
    bin_dir = args.lean_bin.resolve()
    suffix = ".exe" if os.name == "nt" else ""
    lean = bin_dir / ("lean" + suffix)
    native = bin_dir / ("leanchecker" + suffix)
    second = args.lean4lean.resolve() if args.lean4lean else None
    with tempfile.TemporaryDirectory(prefix="apci-p-np-") as temp:
        work = Path(temp)
        search = [str(work)]
        if args.packages:
            for dep in sorted(args.packages.resolve().iterdir()):
                if dep.is_dir():
                    lake = dep / ".lake/build/lib/lean"
                    search.append(str(lake if lake.is_dir() else dep))
        else:
            search.extend(s for s in os.environ.get("LEAN_PATH", "").split(os.pathsep) if s)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(search), LEAN_SYSROOT=str(bin_dir.parent),
                   PATH=str(bin_dir) + os.pathsep + os.environ.get("PATH", ""))
        version = call([lean, "--version"], work, env)
        if "version 4.33.1," not in version:
            raise ValueError(version)
        for mod, expected in UPSTREAM.items():
            rel = mod.replace(".", "/") + ".lean"
            data = pinned_bytes("google-deepmind/formal-conjectures", PIN, rel, expected)
            dest = work / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
        (work / "APCILeanAudit").mkdir()
        shutil.copyfile(ROOT.parent/"corpus/Interface.lean", work/"APCILeanAudit/Interface.lean")
        for mod in ("IUsedLeanToProveRH", "PvsNPDoubleFeature"):
            shutil.copyfile(ROOT/(mod+".lean"), work/(mod+".lean"))
        modules = ["APCILeanAudit.Interface", *UPSTREAM, "IUsedLeanToProveRH", "PvsNPDoubleFeature"]
        for mod in modules:
            path = Path(mod.replace(".", "/"))
            output = call([lean, "-j", "2", "-o", path.with_suffix(".olean"), path.with_suffix(".lean")], work, env)
            call([native, mod], work, env)
            if second:
                call([second, "-v", mod], work, env)
            print(f"Passed {mod}", flush=True)
            if mod == "PvsNPDoubleFeature":
                print(output.strip(), flush=True)
        (work / "Guard.lean").write_text(PROBE, encoding="utf-8")
        call([lean, "Guard.lean"], work, env)
        for target, term, witness in (
            ("P = NP", "iProvedPEqualsNP", "iProvedPEqualsNP"),
            ("P ≠ NP", "iProvedPNotEqualsNP", "iProvedPNotEqualsNP"),
            ("P = NP ∧ P ≠ NP", "⟨iProvedPEqualsNP, iProvedPNotEqualsNP⟩", "iProvedPEqualsNP"),
        ):
            text = f"import PvsNPDoubleFeature\nopen ComplexityTheory Hearthline.Punchline\nexample : {target} := {term}\n"
            (work / "BareGoal.lean").write_text(text, encoding="utf-8")
            call([lean, "BareGoal.lean"], work, env, reject=witness)
        if args.exports:
            write_exports(lean, work, env, args.exports)
            if args.judge_bin:
                judge_exports(args.exports, args.judge_bin)


if __name__ == "__main__":
    main()
