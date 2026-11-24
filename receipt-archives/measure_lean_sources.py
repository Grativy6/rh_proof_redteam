"""Count tracked Lean source and root import footprints at the two public pins."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tarfile


RH = "40e56bab026552e089d7afcfeff08d2defb9c005"
PAL = "5d5f88d283cd3fdab27aa2c7d91ceb0745653cd0"
SUP = "supplements/APCI-manuscript-20261008/Audits/2026-10-08-manuscript/"
IMP = re.compile(rb"^(?:(?:public|private|meta|all)\s+)*import\s+(.+)$")


def header_imports(raw):
    """Read the pinned sources' import headers, skipping nested Lean comments."""
    names = []
    depth = 0
    pos = 0
    while pos < len(raw):
        end = raw.find(b"\n", pos)
        if end < 0:
            end = len(raw)
        line = raw[pos:end].strip()
        pos = end + 1
        if line.startswith(b"\xef\xbb\xbf"):
            line = line[3:]
        out = bytearray()
        while line:
            if depth:
                open_at, close_at = line.find(b"/-"), line.find(b"-/")
                if open_at >= 0 and (close_at < 0 or open_at < close_at):
                    depth += 1
                    line = line[open_at+2:]
                elif close_at >= 0:
                    depth -= 1
                    line = line[close_at+2:]
                else:
                    break
            else:
                block_at, comment_at = line.find(b"/-"), line.find(b"--")
                if comment_at >= 0 and (block_at < 0 or comment_at < block_at):
                    out.extend(line[:comment_at])
                    break
                if block_at < 0:
                    out.extend(line)
                    break
                out.extend(line[:block_at])
                out.extend(b" ")
                depth = 1
                line = line[block_at+2:]
        command = bytes(out).strip()
        if not command or command in (b"module", b"prelude"):
            continue
        match = IMP.match(command)
        if not match:
            break
        names.extend(n.decode("utf-8") for n in match[1].split() if n not in (b"all", b"meta"))
    return names


def counts(files):
    return {"files": len(files), "physical_lines": sum(f["lines"] for f in files)}


def scope(repo, revision, is_pal):
    modules = {}
    excluded = Counter()
    command = ["git", "-C", str(repo), "archive", revision]
    if not is_pal:
        command.append("src")
    with subprocess.Popen(command, stdout=subprocess.PIPE) as process:
        with tarfile.open(fileobj=process.stdout, mode="r|") as archive:
            for member in archive:
                if not member.isfile() or not member.name.endswith(".lean"):
                    continue
                path = member.name
                if path.startswith("external-audits/"):
                    excluded["vendored external audit files"] += 1
                    continue
                if Path(path).name == "lakefile.lean":
                    excluded["Lake configuration files"] += 1
                    continue
                file = archive.extractfile(member)
                data = file.read()
                group, relative = "root", path
                if is_pal:
                    for name, prefix in [("APCI", "projects/APCI/"), ("FRONT", "projects/FRONT/"), ("supplement", SUP)]:
                        if path.startswith(prefix):
                            group, relative = name, path[len(prefix):]
                            break
                else:
                    relative = path.removeprefix("src/")
                modules[(group, relative[:-5].replace("/", "."))] = {
                    "path": path,
                    "lines": data.count(b"\n") + int(bool(data) and not data.endswith(b"\n")),
                    "sha256": hashlib.sha256(data).hexdigest(),
                    "imports": header_imports(data),
                }
        if process.wait() != 0:
            raise RuntimeError("git archive failed at " + revision)

    targets = ([("root", "PALLeanAudit"), ("root", "Experiments.FiniteAbstractionControls"),
                ("APCI", "APCILeanAudit.Interface"), ("FRONT", "FrontLean"),
                ("supplement", "APCIManuscript")] if is_pal else [("root", "Main")])
    result = {"revision": revision, **counts(list(modules.values())), "excluded": dict(excluded),
              "identical_files_counted_once": counts(list({m["sha256"]:m for m in modules.values()}.values())),
              "groups": {}, "entry_modules": {}}
    for group in sorted({g for g, _ in modules}):
        result["groups"][group] = counts([v for (g, _), v in modules.items() if g == group])
    for group, name in targets:
        todo, seen, external = [(group, name)], set(), set()
        while todo:
            key = todo.pop()
            if key in seen:
                continue
            seen.add(key)
            origin, _ = key
            for other in modules[key]["imports"]:
                dep = (origin, other)
                if dep in modules:
                    todo.append(dep)
                elif origin == "supplement" and ("APCI", other) in modules:
                    todo.append(("APCI", other))
                else:
                    external.add(other)
        entry = modules[(group, name)]
        result["entry_modules"][group + "." + name] = {
            "entry_file": entry["path"], "entry_file_lines": entry["lines"],
            "project_import_closure": counts([modules[k] for k in seen]),
            "external_module_names_directly_imported_by_closure": len(external),
        }
    return result


def cpx_scope(path):
    from zipfile import ZipFile

    packed = path.read_bytes()
    if hashlib.sha256(packed).hexdigest() != "f3cf930ac8ef6bec06a13e0f948334aa150834d84bda01e9fce120610a88c32e":
        raise ValueError("Expected the deposited CPX v1.0 companion")
    with ZipFile(path) as archive:
        members = [item for item in archive.namelist() if item.startswith("formal/") and item.endswith(".lean")]
        rows = []
        for name in members:
            data = archive.read(name)
            rows.append({"path": name, "lines": data.count(b"\n") + int(bool(data) and not data.endswith(b"\n"))})
    return {"edition": "10.5281/zenodo.23306102", **counts(rows), "source_files": rows}


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--pal", type=Path, required=True)
    cli.add_argument("--rh", type=Path, required=True)
    cli.add_argument("--cpx", type=Path, help="Include the current formal project in the deposited CPX v1.0 ZIP.")
    cli.add_argument("--out", type=Path, required=True)
    args = cli.parse_args()
    result = {"line_rule": "LF count plus an unterminated final line; comments and blanks included",
              "pal": scope(args.pal, PAL, True), "rh": scope(args.rh, RH, False)}
    if args.cpx:
        result["cpx"] = cpx_scope(args.cpx)
        result["corpus_total"] = {k: result["pal"][k] + result["cpx"][k] for k in ("files", "physical_lines")}
    args.out.write_bytes((json.dumps(result, indent=2) + "\n").encode())
    for name in ("pal", "rh"):
        print(name, result[name]["files"], result[name]["physical_lines"])
