"""Export a fixed PAL exercise or the actual solution from its pinned Lake project.

Run lake build first. The exported .ndjson files go in the named output
directory. Each exercise compiles its Mathlib-only challenge separately.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from replay_p_vs_np import EXPORT_FILES, EXPORT_PIN, PRIMITIVES, pinned_bytes

MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
LEAN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
PROJECT = Path(__file__).resolve().parents[1] / "pal-rh"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("kind", choices=["odd", "fourths", "partial", "final"])
    parser.add_argument("output", type=Path)
    parser.add_argument("--project", type=Path, default=PROJECT)
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    project = args.project.resolve()
    output = args.output.resolve()
    build = project / ".lake/build/lib/lean"
    if not (build / "PALRH.olean").is_file():
        parser.error("Build the pinned PALRH project first.")
    pinned = subprocess.check_output(["git", "-C", str(project / ".lake/packages/mathlib"),
                                      "rev-parse", "HEAD"], text=True).strip()
    if pinned != MATHLIB:
        parser.error("The installed Mathlib revision differs from the construction key.")
    # Request only the compiler and package search path from Lake's environment.
    probe = "import json,os,shutil; print(json.dumps([shutil.which('lean'), os.environ['LEAN_PATH']]))"
    raw = subprocess.check_output([args.lake, "env", sys.executable, "-c", probe], cwd=project, text=True)
    lean_name, paths = json.loads(raw.strip().splitlines()[-1])
    lean = Path(lean_name).resolve()
    libs = [str((project / x).resolve()) for x in paths.split(os.pathsep) if x]
    packages = (project / ".lake/packages").resolve()
    dep_libs = [x for x in libs if Path(x).is_relative_to(packages)]
    if not dep_libs or str(build.resolve()) not in libs:
        parser.error("Lake did not supply both the project and stock dependency libraries.")
    env = dict(os.environ, PATH=str(lean.parent) + os.pathsep + os.environ.get("PATH", ""))
    version = subprocess.check_output([str(lean), "--version"], env=env, text=True)
    if LEAN not in version or "4.33.1" not in version:
        parser.error("The compiler differs from the construction key.")
    relative = {"odd": "checks/odd/OddSolution.lean", "fourths": "checks/fourths/FourthSolution.lean",
                "partial": "checks/partial/PALSolution.lean",
                "final": "PALSolution.lean"}[args.kind]
    source = project / relative
    if not source.is_file():
        parser.error("The final PALSolution.lean must contain the independently derived bare theorem.")
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="pal-export-") as scratch:
        work = Path(scratch)
        exporter = work / "exporter"
        exporter.mkdir()
        for name, digest in EXPORT_FILES.items():
            (exporter / name).write_bytes(pinned_bytes(
                "leanprover/lean4export", EXPORT_PIN, name, digest))
        subprocess.run([str(lean), "-o", "Export.olean", "Export.lean"],
                       cwd=exporter, env=dict(env, LEAN_PATH=""), check=True)

        def compile_and_export(src, name, selected_libs, destination):
            stage = work / src.stem
            stage.mkdir()
            shutil.copyfile(src, stage / src.name)
            module = src.stem
            stage_env = dict(env, LEAN_PATH=os.pathsep.join([str(stage), *selected_libs]))
            subprocess.run([str(lean), "-o", module + ".olean", src.name],
                           cwd=stage, env=stage_env, check=True)
            export_env = dict(stage_env, LEAN_PATH=str(exporter) + os.pathsep + stage_env["LEAN_PATH"])
            # Same-volume atomic publication; a failed export never becomes a replay input.
            with tempfile.NamedTemporaryFile(dir=output, delete=False) as stream:
                temp = Path(stream.name)
                try:
                    subprocess.run([str(lean), "--run", "Main.lean", module, "--", name, *PRIMITIVES],
                                   cwd=exporter, env=export_env, stdout=stream, check=True)
                except BaseException:
                    stream.close()
                    temp.unlink(missing_ok=True)
                    raise
            temp.replace(output / destination)
            print(destination, (output / destination).stat().st_size, "bytes", flush=True)

        references = {"odd": ("OddChallenge.lean", "oddReopening"),
                      "fourths": ("FourthChallenge.lean", "fourthPowerAreaReduction")}
        if args.kind in references:
            reference, theorem = references[args.kind]
            compile_and_export(project / "checks" / args.kind / reference, theorem,
                               dep_libs, args.kind + "-challenge.ndjson")
            compile_and_export(source, theorem, libs, args.kind + "-solution.ndjson")
        else:
            compile_and_export(source, "riemannHypothesis", libs, args.kind + ".ndjson")


if __name__ == "__main__":
    main()
