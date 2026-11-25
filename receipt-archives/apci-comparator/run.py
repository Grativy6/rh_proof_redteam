#!/usr/bin/env python3
"""Compile reviewed APCI fixtures and record comparison and kernel results.

This runner never disables Comparator's sandbox. Direct component checks are
explicitly separate and are suitable only for these self-authored math fixtures.
It does not install dependencies, execute arbitrary supplied commands, or publish.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile
import time

HERE = Path(__file__).resolve().parent
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
QUOT = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
PRIMITIVES = """Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble
Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List
eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam""".split()
LEAN_PIN = "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9"
MATHLIB_PIN = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def verdict(returncode, output):
    if returncode == 0 and "Your solution is okay!" in output:
        return "accepted"
    if returncode == 1 and ("theorem statement do not match" in output or
                           "Const does not match between challenge" in output):
        return "rejected-comparison"
    if returncode == 1 and "Illegal axiom detected:" in output:
        return "rejected-axioms"
    if "bwrap:" in output and ("Operation not permitted" in output or
                                "Permission denied" in output):
        return "blocked-sandbox"
    return "unclassified-failure"


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--lean-bin", type=Path, required=True)
    cli.add_argument("--mathlib", type=Path, help="Prepared, trusted Mathlib v4.36.0 checkout/cache")
    cli.add_argument("--output", type=Path, required=True,
                     help="Fresh output, or an empty directory created by the bounded runner")
    args = cli.parse_args()
    bins, out = args.lean_bin.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    for name in ["summary.json", "commands.json", "core-replay.tar.xz", "logs"]:
        if (out / name).exists():
            raise ValueError(f"Refusing to overwrite {out / name}")
    logs = out / "logs"
    logs.mkdir()
    env = dict(os.environ, PATH=str(bins) + os.pathsep + os.environ.get("PATH", ""),
               LEAN_SYSROOT=str(bins.parent), LEAN_ABORT_ON_PANIC="1")
    env.pop("COMPARATOR_BWRAP", None)
    env.pop("LEAN_PATH", None)
    records = []

    def call(label, argv, cwd, run_env=env, stdout_file=None, require=False, timeout=180):
        started = time.time()
        argv = [str(x) for x in argv]
        timed_out = False
        try:
            if stdout_file is None:
                result = subprocess.run(argv, cwd=cwd, env=run_env, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, timeout=timeout)
                data = result.stdout
            else:
                with open(stdout_file, "wb") as stream:
                    result = subprocess.run(argv, cwd=cwd, env=run_env, stdout=stream,
                                            stderr=subprocess.PIPE, timeout=timeout)
                data = result.stderr
            code = result.returncode
        except subprocess.TimeoutExpired as error:
            timed_out = True
            code = None
            data = (error.stderr if stdout_file is not None else error.output) or b""
        log = logs / (label + ".log")
        log.write_bytes(data)
        rec = {"label": label, "argv": argv, "cwd": str(cwd), "exit_code": code,
               "status": "timeout" if timed_out else "exited",
               "elapsed_seconds": round(time.time() - started, 6),
               "log": str(log.relative_to(out)), "log_sha256": digest(log)}
        if stdout_file is not None:
            rec["stdout_sha256"] = digest(stdout_file)
            rec["stdout_bytes"] = Path(stdout_file).stat().st_size
        records.append(rec)
        write_json(out / "commands.json", records)
        if timed_out or (require and code):
            raise RuntimeError(f"{label} {'timed out' if timed_out else f'exited {code}'}; see {log}")
        return rec, data.decode("utf-8", "replace")

    _, version = call("lean-version", [bins / "lean", "--version"], HERE, require=True)
    if "version 4.36.0," not in version or LEAN_PIN not in version:
        raise ValueError(f"Unexpected Lean build: {version}")
    source = bins.parent / "src/lean/lake/Lake/CLI/Check.lean"
    text = source.read_text()
    block = text.split("def primitiveTargets", 1)[1].split("def builtinTargets", 1)[0]
    actual_primitives = re.findall(r"^\s*``([A-Za-z0-9_.]+),?\s*$", block, re.M)
    if actual_primitives != PRIMITIVES:
        raise ValueError("Export primitive list differs from the installed Comparator")
    driver_text = (HERE / "CompareExports.lean").read_text()
    if re.findall(r"``([A-Za-z0-9_.]+)", driver_text) != PRIMITIVES:
        raise ValueError("Direct driver primitive list differs from Comparator")

    provenance = {"lean": version.strip(), "lean_commit": LEAN_PIN,
                  "expected_lean_release_sha256": "2b7ab1ed8b92d2e6abfaf41344823b510064dbc9c0260cac73eb496ab2dea6eb",
                  "tool_files": {}, "mathlib_commit": None}
    for path in [bins / "lean", bins / "lake", bins / "leanexport", bins / "leanchecker",
                 bins / "nanoda_bin", source,
                 bins.parent / "src/lean/lake/Lake/Check/Compare.lean",
                 bins.parent / "src/lean/lake/Lake/Check/Axioms.lean"]:
        provenance["tool_files"][str(path.relative_to(bins.parent))] = digest(path)

    math_env = dict(env)
    if args.mathlib:
        mathlib = args.mathlib.resolve()
        _, pin = call("mathlib-pin", ["git", "rev-parse", "HEAD"], mathlib, require=True)
        if pin.strip() != MATHLIB_PIN:
            raise ValueError("Mathlib checkout is not the pinned v4.36.0 revision")
        _, status = call("mathlib-state", ["git", "status", "--porcelain", "--untracked-files=no"],
                         mathlib, require=True)
        if status.strip():
            raise ValueError("Mathlib has tracked changes")
        _, lean_path = call("mathlib-lean-path", [bins / "lake", "env", "printenv", "LEAN_PATH"],
                            mathlib, require=True)
        paths = [str((mathlib / p).resolve()) for p in lean_path.strip().split(os.pathsep) if p]
        math_env["LEAN_PATH"] = os.pathsep.join(paths)
        provenance["mathlib_commit"] = MATHLIB_PIN
        provenance["mathlib_manifest_sha256"] = digest(mathlib / "lake-manifest.json")
        shutil.copyfile(mathlib / "lake-manifest.json", out / "mathlib-manifest.json")

    cases = json.loads((HERE / "core/cases.json").read_text())
    for case in cases:
        case["family"] = "core"
    if args.mathlib:
        for label, stage in [("Hole", "none"), ("True", "comparison"), ("Bare", "comparison")]:
            cfg = json.loads((HERE / "rh" / (label + ".json")).read_text())
            cases.append({"id": "rh-" + label.lower(), "family": "rh", **cfg,
                          "expected": "accepted" if stage == "none" else "rejected",
                          "expected_stage": stage})

    results, kernels = [], {}
    with tempfile.TemporaryDirectory(prefix="apci-comparator-reviewed-fixtures-") as tmp:
        work = Path(tmp)
        exports, configs = work / "exports", work / "configs"
        exports.mkdir()
        configs.mkdir()
        driver_dir = work / "driver"
        driver_dir.mkdir()
        for name in ["CompareExports.lean", "lakefile.toml", "lean-toolchain"]:
            shutil.copyfile(HERE / name, driver_dir / name)
        call("build-component-driver", [bins / "lake", "build", "compare_exports"],
             driver_dir, require=True)
        component_exe = driver_dir / ".lake/build/bin/compare_exports"
        provenance["component_driver_binary_sha256"] = digest(component_exe)
        for family in ["core"] + (["rh"] if args.mathlib else []):
            dest = work / family
            dest.mkdir()
            for path in (HERE / family).glob("*.lean"):
                shutil.copyfile(path, dest / path.name)
        built, exported = set(), {}

        def environment(family):
            e = dict(math_env if family == "rh" else env)
            e["LEAN_PATH"] = str(work / family) + os.pathsep + e.get("LEAN_PATH", "")
            return e

        def compile_module(family, module):
            if (family, module) in built:
                return
            if family == "core" and module != "APCI":
                compile_module("core", "APCI")
            call("compile-" + family + "-" + module,
                 [bins / "lean", "-j", "2", "-o", module + ".olean", module + ".lean"],
                 work / family, environment(family), require=True)
            built.add((family, module))

        def export_module(family, module, theorem_names, definition_names):
            key = (family, module, tuple(theorem_names), tuple(definition_names))
            if key in exported:
                return exported[key]
            compile_module(family, module)
            target = exports / (family + "-" + module + "-" + str(len(exported)) + ".ndjson")
            targets = list(dict.fromkeys(QUOT + theorem_names + AXIOMS + PRIMITIVES + definition_names))
            call("export-" + target.stem, [bins / "leanexport", module, "--", *targets],
                 work / family, environment(family), stdout_file=target, require=True)
            exported[key] = target
            return target

        def check_kernels(export_path):
            key = digest(export_path)
            if key in kernels:
                return key
            native, _ = call("native-" + export_path.stem,
                             [bins / "leanchecker", "--silent", "--from-export", export_path], work)
            nanoda_config = configs / (export_path.stem + "-nanoda.json")
            write_json(nanoda_config, {"export_file_path": "exports/" + export_path.name, "use_stdin": False,
                       "permitted_axioms": AXIOMS, "unpermitted_axiom_hard_error": False,
                       "num_threads": 2, "nat_extension": True, "string_extension": True})
            second, _ = call("nanoda-" + export_path.stem,
                             [bins / "nanoda_bin", nanoda_config], work)
            kernels[key] = {"export": export_path.name, "native_exit_code": native["exit_code"],
                            "nanoda_exit_code": second["exit_code"],
                            "nanoda_config": str(nanoda_config.relative_to(work)),
                            "nanoda_config_sha256": digest(nanoda_config),
                            "scope": "direct checks of reviewed fixture export; no process isolation claim"}
            return key

        control_names = ["MathematicalControl.constant_trace_collision",
                         "MathematicalControl.identity_cannot_decode",
                         "MathematicalControl.constant_answer_decodes"]
        control = export_module("core", "MathematicalControl", control_names, [])
        control_key = check_kernels(control)
        if kernels[control_key]["native_exit_code"] or kernels[control_key]["nanoda_exit_code"]:
            raise RuntimeError("Mathematical control did not pass both direct kernel checks")

        for case in cases:
            label, family = case["id"], case["family"]
            theorems = case.get("theorem_names", ["claim"])
            definitions = case.get("definition_names", [])
            cfg = {"challenge_module": case["challenge_module"],
                   "solution_module": case["solution_module"], "theorem_names": theorems,
                   "permitted_axioms": AXIOMS, "external_kernels": {"nanoda": ["nanoda_bin"]}}
            if definitions:
                cfg["definition_names"] = definitions
            config = configs / (label + ".json")
            write_json(config, cfg)
            challenge = export_module(family, cfg["challenge_module"], theorems, definitions)
            solution = export_module(family, cfg["solution_module"], theorems, definitions)
            official, official_text = call("comparator-" + label,
                [bins / "lake", "comparator", "--config", config,
                 "--challenge-from-export", challenge, "--solution-from-export", solution], work)
            status = verdict(official["exit_code"], official_text)
            component, component_text = call("components-" + label,
                [component_exe, config, challenge, solution], work)
            expected_exit = 0 if case["expected"] == "accepted" else 1
            expected_marker = "stage=complete;" if expected_exit == 0 else "stage=" + case["expected_stage"] + ";"
            component_matches = component["exit_code"] == expected_exit and expected_marker in component_text
            official_matches = status in (["accepted", "blocked-sandbox"] if expected_exit == 0
                                         else ["rejected-" + case["expected_stage"]])
            solution_key = digest(solution)
            if case["expected_stage"] == "axioms":
                kernel_scope = "not run: solution intentionally uses an unpermitted axiom"
                kernel_matches = True
            else:
                check_kernels(solution)
                kernel_result = kernels[solution_key]
                kernel_matches = (kernel_result["native_exit_code"] == 0 and
                                  kernel_result["nanoda_exit_code"] == 0)
                kernel_scope = "passed" if kernel_matches else "unexpected direct kernel failure"
            row = {"id": label, "expected": case["expected"], "expected_stage": case["expected_stage"],
                   "comparator_status": status, "comparator_exit_code": official["exit_code"],
                   "components_exit_code": component["exit_code"], "components_output": component_text.strip(),
                   "matches_expected_at_observed_stages": component_matches and official_matches and kernel_matches,
                   "direct_kernel_status": kernel_scope,
                   "challenge_export": challenge.name, "challenge_sha256": digest(challenge),
                   "solution_export": solution.name, "solution_sha256": solution_key,
                   "config": str(config.relative_to(work)), "config_sha256": digest(config)}
            results.append(row)
            print(f"{label}: {status}; component exit {component['exit_code']}", flush=True)
            write_json(out / "summary.json", {"provenance": provenance, "cases": results,
                       "direct_kernel_checks": kernels, "mathematical_control": control_key})

        core_results = [row for row in results if not row["id"].startswith("rh-")]
        core_kernels = {key: value for key, value in kernels.items() if value["export"].startswith("core-")}
        replay = {"cases": core_results, "direct_kernel_checks": core_kernels,
                  "instructions": "Run Comparator from this directory with each case's config and exports. The recorded host could not start bwrap; do not disable it to manufacture acceptance."}
        write_json(work / "replay.json", replay)
        with tarfile.open(out / "core-replay.tar.xz", "w:xz", preset=1) as archive:
            for directory in [exports, configs]:
                for path in sorted(directory.iterdir()):
                    if path.name.startswith("rh-"):
                        continue
                    archive.add(path, arcname=str(path.relative_to(work)))
            archive.add(work / "replay.json", arcname="replay.json")
        summary = {"provenance": provenance, "cases": results, "direct_kernel_checks": kernels,
                   "mathematical_control": control_key,
                   "all_observed_stages_match_expected": all(r["matches_expected_at_observed_stages"] for r in results),
                   "full_acceptance_observed": any(r["comparator_status"] == "accepted" for r in results),
                   "core_replay_sha256": digest(out / "core-replay.tar.xz"),
                   "rh_export_retention": "Exact hashes are recorded; regenerate RH exports from the pinned source/cache with run.py. The public replay archive contains only the compact Boolean fixtures.",
                   "scope": "Finite regression fixtures. Direct components are not a sandboxed Comparator acceptance. No RH proof or universal Comparator correctness claim."}
        write_json(out / "summary.json", summary)
        if not summary["all_observed_stages_match_expected"]:
            raise RuntimeError("Unexpected finite-test outcome; review the recorded logs")


if __name__ == "__main__":
    main()
