"""Measure axiom dependencies of each public corpus theorem's statement and full proof.
Use the object directories produced by compare_corpus_lean.py on each requested pin.
The TSV row numbers refer to the source inventory in the same archive.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import csv
import json
import os
from pathlib import Path
import subprocess
import tempfile

INVENTORY = Path(__file__).with_name("2026-11-24-corpus-theorem-axioms.jsonl")
PROBE = """
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for text in (NAMES : Array String) do
    let name := text.toName
    let some ci := env.find? name | throwError "Unknown declaration {text}"
    let mut statement : Array String := #[]
    for c in ci.type.getUsedConstants do
      for a in ← collectAxioms c do
        unless statement.contains a.toString do
          statement := statement.push a.toString
    let full ← collectAxioms name
    let row := Json.mkObj [("name", toJson text), ("statement", toJson statement),
      ("full", toJson (full.map Name.toString))]
    IO.println ("RESULT " ++ row.compress)
"""


def libraries(packages):
    for entry in sorted(packages.resolve().iterdir()):
        if entry.is_dir():
            lake = entry / ".lake/build/lib/lean"
            yield lake if lake.is_dir() else entry


def measure(rows, slot, binaries, packages, pal_objects, cpx_objects, workspace):
    lean = (binaries / ("lean.exe" if os.name == "nt" else "lean")).resolve()
    version = subprocess.check_output([str(lean), "--version"], encoding="utf-8")
    expected = {"432": "4.32.1", "433": "4.33.1"}[slot]
    if "version " + expected + "," not in version:
        raise ValueError(f"Expected Lean {expected}, found {version.strip()}")
    groups = {}
    field = "axioms_" + slot
    for idx, row in enumerate(rows, 1):
        if row.get(field) is not None:
            groups.setdefault(row["project"], []).append((idx, row))
    measured = {}
    for group, records in groups.items():
        objects = (cpx_objects if group == "CPX" else pal_objects) / group
        if not objects.is_dir():
            raise ValueError(f"Missing {objects}")
        imports = sorted({row["module"] for _, row in records})
        names = [row["name"] for _, row in records]
        source = workspace / f"Probe_{slot}_{group}.lean"
        name_array = "#" + json.dumps(names, ensure_ascii=False)
        source.write_text("import Lean\n" + "".join(f"import {m}\n" for m in imports)
                          + PROBE.replace("NAMES", name_array), encoding="utf-8")
        env = os.environ.copy()
        roots = [objects.resolve()]
        if group == "supplement":
            roots.append((pal_objects / "APCI").resolve())
        env["LEAN_PATH"] = os.pathsep.join(str(p) for p in [*roots, *libraries(packages)])
        env["LEAN_SYSROOT"] = str(binaries.resolve().parent)
        env["PATH"] = str(binaries.resolve()) + os.pathsep + env.get("PATH", "")
        run = subprocess.run([str(lean), "-j", "2", str(source)], env=env,
                             cwd=workspace, capture_output=True, encoding="utf-8", errors="replace")
        values = [json.loads(line[7:]) for line in run.stdout.splitlines() if line.startswith("RESULT ")]
        if run.returncode or [v["name"] for v in values] != names:
            diagnostics = [s for s in run.stdout.splitlines() if not s.startswith("RESULT ")]
            raise RuntimeError(f"{slot} {group}: {diagnostics[-8:]} {run.stderr[-1200:]}")
        for (idx, row), value in zip(records, values):
            full = set(value["full"])
            statement = set(value["statement"])
            if full != set(row[field]) or not statement <= full:
                raise ValueError(f"Changed dependencies at source row {idx}: {value}")
            measured[idx] = ",".join(sorted(statement)) or "none"
        print(slot, group, len(values), flush=True)
    return measured


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, default=INVENTORY)
    parser.add_argument("--out", required=True, type=Path)
    for pin in ("432", "433"):
        for opt in ("bin", "packages", "pal-objects", "cpx-objects"):
            parser.add_argument(f"--{opt}-{pin}", required=True, type=Path)
    args = vars(parser.parse_args())
    rows = [json.loads(line) for line in args["inventory"].read_text(encoding="utf-8").splitlines()]
    with tempfile.TemporaryDirectory(prefix="pal-statement-axioms-") as tmp:
        with ThreadPoolExecutor(max_workers=2) as pool:
            jobs = {pin: pool.submit(measure, rows, pin, args["bin_" + pin], args["packages_" + pin],
                                     args["pal_objects_" + pin], args["cpx_objects_" + pin], Path(tmp))
                    for pin in ("432", "433")}
            result = {pin: job.result() for pin, job in jobs.items()}
    with args["out"].open("w", newline="", encoding="utf-8") as out:
        tsv = csv.writer(out, delimiter="\t", lineterminator="\n")
        tsv.writerow(("source_inventory_line", "statement_axioms_432", "statement_axioms_433"))
        for idx in range(1, len(rows) + 1):
            tsv.writerow((idx, result["432"][idx], result["433"].get(idx, "unavailable")))


if __name__ == "__main__":
    main()
