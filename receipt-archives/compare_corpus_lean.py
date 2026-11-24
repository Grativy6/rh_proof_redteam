"""Compile and inspect the personal Lean sources from a pinned PAL-Lean-Audit checkout.

Supply a matching library search path in LEAN_PATH, the Lean bin directory,
and a fresh work directory. The source tree is read-only. The optional second
checker replays each module against its compiled imports. The JSON records
the exact files checked, theorem types, axioms and any failed stages.
"""

import argparse
import concurrent.futures
import json
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
from zipfile import ZipFile

from measure_lean_sources import header_imports


PIN = "5d5f88d283cd3fdab27aa2c7d91ceb0745653cd0"
SUPPLEMENT = "supplements/APCI-manuscript-20261008/Audits/2026-10-08-manuscript"
ROOTS = {"root": "", "APCI": "projects/APCI", "FRONT": "projects/FRONT", "supplement": SUPPLEMENT}


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])


def executable(directory, name):
    return directory / (name + (".exe" if os.name == "nt" else ""))


def source_inventory(root):
    records = {}
    for raw in git(root, "ls-files", "-z", "*.lean").split(b"\0"):
        if not raw:
            continue
        path = raw.decode("utf-8")
        if path.startswith("external-audits/") or Path(path).name == "lakefile.lean":
            continue
        group = next((g for g, prefix in ROOTS.items() if prefix and path.startswith(prefix + "/")), "root")
        prefix = ROOTS[group]
        relative = path[len(prefix)+1:] if prefix else path
        module = relative[:-5].replace("/", ".")
        data = (root / path).read_bytes()
        if data != git(root, "show", PIN + ":" + path):
            raise ValueError("Modified source " + path)
        imports = header_imports(data)
        records[(group, module)] = {
            "group": group, "module": module, "path": path, "sha256": hashlib.sha256(data).hexdigest(),
            "lines": data.count(b"\n") + int(bool(data) and not data.endswith(b"\n")),
            "imports": sorted(set(imports)),
        }
    for (group, _), record in records.items():
        deps = []
        for name in record["imports"]:
            if (group, name) in records:
                deps.append((group, name))
            elif group == "supplement" and ("APCI", name) in records:
                deps.append(("APCI", name))
        record["deps"] = deps
    return records


def cpx_inventory(archive_path, work):
    """Use the seven Lean files in the deposited current CPX formal project."""
    expected = "f3cf930ac8ef6bec06a13e0f948334aa150834d84bda01e9fce120610a88c32e"
    if hashlib.sha256(archive_path.read_bytes()).hexdigest() != expected:
        raise ValueError("Unexpected CPX companion revision")
    root = work / "cpx-source"
    records = {}
    with ZipFile(archive_path) as archive:
        files = [n for n in archive.namelist() if n.startswith("formal/") and n.endswith(".lean")]
        if len(files) != 7:
            raise ValueError("Unexpected CPX source inventory")
        for n in files:
            relative = Path(n).relative_to("formal")
            if ".." in relative.parts:
                raise ValueError(n)
            data = archive.read(n)
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            module = ".".join(relative.with_suffix("").parts)
            imports = sorted(set(header_imports(data)))
            records[("CPX", module)] = {"group": "CPX", "module": module,
                "path": archive_path.name + "!" + n, "sha256": hashlib.sha256(data).hexdigest(),
                "lines": data.count(b"\n") + int(bool(data) and not data.endswith(b"\n")),
                "imports": imports}
    for row in records.values():
        row["deps"] = [("CPX", dep) for dep in row["imports"] if ("CPX", dep) in records]
    return records


def declared_theorems(text):
    """Return public theorem/lemma/axiom commands with one-based source lines."""
    marker = re.compile(r'/-|-/|--|"(?:\\.|[^"\\])*"', re.DOTALL)
    nested = re.compile(r"/-|-/")
    out = []
    pos = depth = 0
    while pos < len(text):
        match = (nested if depth else marker).search(text, pos)
        stop = match.start() if match else len(text)
        fragment = text[pos:stop]
        out.append(re.sub(r"[^\n]", " ", fragment) if depth else fragment)
        if not match:
            break
        token = match[0]
        pos = match.end()
        if token == "/-":
            depth += 1
        elif token == "-/" and depth:
            depth -= 1
        elif token == "--":
            end = text.find("\n", pos)
            pos = len(text) if end < 0 else end
        elif token.startswith('"'):
            out.append(re.sub(r"[^\n]", " ", token))
        out.append(" ")
    clean = "".join(out)
    pattern = (r"(?m)^[ \t]*(?:@\[[^\]]*\]\s*)*"
               r"(?P<mods>(?:(?:private|protected|noncomputable|unsafe|local|nonrec|scoped)\s+)*)"
               r"(?:theorem|lemma|axiom)\s+(?P<name>[^\s\(\[{:]+)")
    for match in re.finditer(pattern, clean):
        if not {"private", "local"}.intersection(match["mods"].split()):
            yield match["name"].removeprefix("_root_."), clean.count("\n", 0, match.start("name")) + 1


def tag_source_commands(options, result):
    """Distinguish source declarations from generated equation/induction lemmas."""
    for record in result["source_files"]:
        group, module = record["group"], record["module"]
        inspection = result["groups"][group]
        if inspection["status"] != 0 or result["build"][group + "|" + module].get("compile") != 0:
            continue
        root = options.work / "cpx-source" if group == "CPX" else options.source / ROOTS[group]
        source = (root / (module.replace(".", "/") + ".lean")).read_text(encoding="utf-8-sig")
        declarations = [row for row in inspection["declarations"] if row["module"] == module]
        for name, line in declared_theorems(source):
            matches = [row for row in declarations if row["name"] == name or row["name"].endswith("." + name)]
            if len(matches) != 1:
                raise ValueError(f"Could not identify {group}:{module}:{line} {name} in checked declarations")
            matches[0]["source_line"] = line


def write_json(path, value):
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    temp.replace(path)


def run(cmd, directory, env, log, timeout):
    try:
        proc = subprocess.run([str(a) for a in cmd], cwd=directory, env=env, stdin=subprocess.DEVNULL,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout,
                              creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        log.write_bytes(proc.stdout)
        return proc.returncode
    except subprocess.TimeoutExpired as exc:
        log.write_bytes((exc.stdout or b"") + b"\nComparison runner timed out.\n")
        return 124


def environment(options, group):
    env = dict(os.environ)
    libraries = [str(options.work / "objects" / group)]
    if group == "supplement":
        libraries.append(str(options.work / "objects/APCI"))
    env["LEAN_PATH"] = os.pathsep.join(libraries + [s for s in os.environ.get("LEAN_PATH", "").split(os.pathsep) if s])
    env["PATH"] = str(options.bin) + os.pathsep + env["PATH"]
    env["LEAN_ABORT_ON_PANIC"] = "1"
    return env


def kernel_environment(options, record):
    """Keep a parent module's native prefix replay within its import closure."""
    group, module = record["group"], record["module"]
    env = environment(options, group)
    if not any(g == group and n.startswith(module + ".") for g, n in options.inventory):
        return env
    sparse = options.work / "replay-paths" / group / module
    todo = [(group, module)]
    seen = set()
    while todo:
        key = todo.pop()
        if key in seen:
            continue
        seen.add(key)
        matched_group, name = key
        rel = Path(*name.split("."))
        output = options.work / "objects" / matched_group / rel.parent
        dst = sparse / rel.parent
        dst.mkdir(parents=True, exist_ok=True)
        for artifact in output.glob(rel.name + ".*"):
            suffix = artifact.name[len(rel.name):]
            if not artifact.is_file() or suffix not in (".olean", ".olean.server", ".olean.private", ".ir", ".ilean"):
                continue
            path = dst / artifact.name
            if not path.exists():
                try:
                    os.link(artifact, path)
                except OSError:
                    shutil.copyfile(artifact, path)
        todo.extend(options.inventory[key]["deps"])
    env["LEAN_PATH"] = os.pathsep.join([str(sparse)] + [s for s in os.environ.get("LEAN_PATH", "").split(os.pathsep) if s])
    return env


def recheck_failed_replays(options, rows, statuses):
    for key, record in rows.items():
        status = statuses["|".join(key)]
        if status.get("compile") != 0:
            continue
        for stage, exe in [("native_kernel", executable(options.bin, "leanchecker")),
                           ("second_kernel", options.second_checker)]:
            if exe is None or status.get(stage) in (None, 0):
                continue
            logfile = options.work / "logs" / (key[0] + "-" + key[1] + ".retry-" + stage + ".log")
            command = [exe, "-v", key[1]]
            status[stage] = run(command, options.work, kernel_environment(options, record), logfile, options.timeout)
    write_json(options.work / "build.json", statuses)


def build_one(options, record):
    group, module = record["group"], record["module"]
    root = options.work / "cpx-source" if group == "CPX" else options.source / ROOTS[group]
    source = root / (module.replace(".", "/") + ".lean")
    target = options.work / "objects" / group / (module.replace(".", "/") + ".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    env = environment(options, group)
    log = options.work / "logs" / (group + "-" + module)
    codes = {}
    codes["compile"] = run([executable(options.bin, "lean"), "-j", "2", "--root=" + str(root),
                            "-o", target, source], root, env, Path(str(log)+".compile.log"), options.timeout)
    if codes["compile"] == 0:
        env = kernel_environment(options, record)
        codes["native_kernel"] = run([executable(options.bin, "leanchecker"), module], root, env,
                                     Path(str(log)+".kernel.log"), options.timeout)
        if options.second_checker is not None:
            codes["second_kernel"] = run([options.second_checker, "-v", module], root, env,
                                         Path(str(log)+".second.log"), options.timeout)
    return codes


def inspect(options, group, records):
    modules = sorted(r["module"] for r in records)
    if not modules:
        return {"status": "no compiled modules", "declarations": []}
    probe = options.work / ("Comparison_" + group + ".lean")
    imports = ["import Lean", "import Mathlib.NumberTheory.LSeries.RiemannZeta"]
    imports.extend("import " + name for name in modules)
    mine = "#[" + ", ".join(json.dumps(name) for name in modules) + "]"
    source = "\n".join(imports) + "\n\n" + INSPECTOR.replace("MINE", mine)
    probe.write_bytes(source.encode("utf-8"))
    logfile = options.work / "logs" / (group + "-inspection.log")
    status = run([executable(options.bin, "lean"), "-j", "2", probe], options.work,
                 environment(options, group), logfile, options.timeout)
    rows = []
    for line in logfile.read_text(encoding="utf-8", errors="replace").splitlines():
        if line.startswith("PALRESULT "):
            rows.append(json.loads(line[len("PALRESULT "):]))
    return {"status": status, "declarations": sorted(rows, key=lambda x: (x["module"], x["name"]))}


INSPECTOR = r'''
set_option maxHeartbeats 0
set_option maxRecDepth 4096
open Lean Elab Command in
run_cmd do
  let mine : Array String := MINE
  let env ← getEnv
  let rh := mkConst §RiemannHypothesis
  for (name, ci) in env.constants.toList do
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .axiomInfo _ => "axiom"
      | _ => ""
    if kind.isEmpty || name.isInternal then continue
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!.toString
    unless mine.contains mod do continue
    let qs ← collectAxioms name
    let (statement, same) ← liftTermElabM do
      let st ← Meta.ppExpr ci.type
      let isRH ← Meta.withTransparency .all <| Meta.isDefEq ci.type rh
      return (st.pretty 110, isRH)
    let row := Json.mkObj [("module", toJson mod), ("name", toJson name.toString),
      ("kind", toJson kind), ("type", toJson statement),
      ("axioms", toJson (qs.map Name.toString)), ("sameTypeAsMathlibRH", toJson same)]
    IO.println ("PALRESULT " ++ row.compress)
'''.replace("§", chr(96))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="Pinned PAL Git checkout; used for the collection run.")
    parser.add_argument("--bin", required=True, type=Path)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--packages", type=Path, help="Use dependency directories from Lake or a restored binary package collection instead of LEAN_PATH.")
    parser.add_argument("--jobs", default=2, type=int)
    parser.add_argument("--timeout", default=300, type=int)
    parser.add_argument("--second-checker", type=Path)
    parser.add_argument("--cpx-only", type=Path, metavar="DEPOSITED_ZIP", help="Check the separate Context Parallax project only.")
    parser.add_argument("--resume", action="store_true", help="Resume interrupted jobs in an existing work directory.")
    parser.add_argument("--retry-replays", action="store_true", help="Retry unsuccessful checker stages on the existing compiled files.")
    parser.add_argument("--inspect-only", action="store_true", help="Reuse this run's compiled modules after fixing an inspection failure.")
    options = parser.parse_args()
    if options.source is None and not options.cpx_only:
        parser.error("--source is required for the PAL collection")
    if options.source is not None:
        options.source = options.source.resolve()
    options.work = options.work.resolve()
    options.bin = options.bin.resolve()
    if not options.cpx_only and git(options.source, "rev-parse", "HEAD").decode().strip() != PIN:
        raise ValueError("Expected pinned PAL revision " + PIN)
    rows = cpx_inventory(options.cpx_only, options.work) if options.cpx_only else source_inventory(options.source)
    options.inventory = rows
    if options.packages:
        libraries = []
        for directory in sorted(options.packages.resolve().iterdir()):
            if directory.is_dir():
                built = directory / ".lake/build/lib/lean"
                libraries.append(str(built if built.is_dir() else directory))
        os.environ["LEAN_PATH"] = os.pathsep.join(libraries)
    options.work.mkdir(parents=True, exist_ok=True)
    (options.work / "logs").mkdir(exist_ok=True)
    result_path = options.work / "result.json"
    build_path = options.work / "build.json"
    if options.inspect_only or options.retry_replays:
        statuses = json.loads(build_path.read_text(encoding="utf-8"))
        if options.retry_replays:
            recheck_failed_replays(options, rows, statuses)
    else:
        if options.resume:
            statuses = json.loads(build_path.read_text(encoding="utf-8"))
            if not set(statuses) <= {"|".join(k) for k in rows}:
                raise ValueError("Existing inventory differs from this source")
            for key, record in rows.items():
                if statuses.get("|".join(key), {}).get("compile") == 0:
                    output = options.work / "objects" / key[0] / (key[1].replace(".", "/") + ".olean")
                    if not output.is_file():
                        raise ValueError("Missing previously compiled module " + str(output))
        else:
            if build_path.exists() or (options.work / "objects").exists():
                raise ValueError("Use a fresh work directory for a new source build")
            statuses = {}
        pending = {key for key in rows if "|".join(key) not in statuses}
        running = {}
        with concurrent.futures.ThreadPoolExecutor(max_workers=options.jobs) as pool:
            while pending or running:
                for key in sorted(pending.copy()):
                    if len(running) >= options.jobs:
                        break
                    deps = ["|".join(d) for d in rows[key]["deps"]]
                    if not all(d in statuses for d in deps):
                        continue
                    pending.remove(key)
                    if any(statuses[d].get("compile") != 0 for d in deps):
                        statuses["|".join(key)] = {"compile": "dependency failed"}
                    else:
                        running[pool.submit(build_one, options, rows[key])] = key
                if running:
                    done, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
                    for job in done:
                        statuses["|".join(running.pop(job))] = job.result()
                    write_json(build_path, statuses)
                elif pending:
                    if all(any("|".join(d) not in statuses for d in rows[k]["deps"]) for k in pending):
                        raise ValueError("Unresolved personal import cycle")
    if options.resume:
        recheck_failed_replays(options, rows, statuses)
    env = environment(options, "root")
    version = subprocess.check_output([str(executable(options.bin, "lean")), "--version"], env=env).decode().strip()
    result = {"pin": ("10.5281/zenodo.23306102" if options.cpx_only else PIN), "lean_version": version, "second_checker": options.second_checker.name if options.second_checker else None,
              "source_files": list(rows.values()), "build": statuses, "groups": {}}
    for group in sorted({key[0] for key in rows}):
        compiled = [r for key, r in rows.items() if key[0] == group and statuses["|".join(key)].get("compile") == 0]
        result["groups"][group] = inspect(options, group, compiled)
    tag_source_commands(options, result)
    write_json(result_path, result)
    print(version)
    print(f"{sum(v.get('compile') == 0 for v in statuses.values())}/{len(rows)} personal source files compiled.")
    print("Group inspection:", [(g, v["status"], len(v["declarations"])) for g, v in result["groups"].items()])
    failed = any(any(x != 0 for x in v.values()) for v in statuses.values())
    failed |= any(v["status"] != 0 for v in result["groups"].values())
    raise SystemExit(int(failed))


if __name__ == "__main__":
    main()
