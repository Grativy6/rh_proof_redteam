"""Replay one ordinary Windows Lean 4.35.0 library and one named proof export."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import tempfile


ARCHIVE_SHA = "893fde3f52b48c647e3edcf33844cbb61f8ef70fcd88e0536bfc83f29844081e"
SOURCE = "theorem palStockCheck : (1 : Nat) = 1 := rfl\n"


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def replay(root, archive):
    prefix = root.resolve()
    if archive is not None and digest(archive) != ARCHIVE_SHA:
        raise ValueError("The archive differs from the published Windows 4.35.0 tar.zst.")
    lib = prefix / "lib" / "lean"
    result = {
        "platform": platform.system(),
        "release": "v4.35.0",
        "archive_sha256_checked": ARCHIVE_SHA if archive is not None else None,
        "sha256": {p: digest(prefix / p) for p in (
            "bin/lean.exe", "bin/leanexport.exe", "bin/lean4lean.exe",
            "bin/leanchecker.exe", "lib/lean/Init/Prelude.olean")},
        "source": SOURCE,
        "runs": [],
    }
    with tempfile.TemporaryDirectory(prefix="pal-lean435-") as directory:
        cwd = Path(directory)
        env = os.environ.copy()
        env.update(LEAN_SYSROOT=str(prefix), LEAN_PATH=str(lib),
                   PATH=str(prefix / "bin") + os.pathsep + env.get("PATH", ""))

        def run(name, *args, export=None):
            child = subprocess.run([str(prefix / "bin" / (name + ".exe")), *args],
                                   cwd=cwd, env=env, stdout=export or subprocess.PIPE,
                                   stderr=subprocess.PIPE, timeout=120)
            def public(raw):
                return (raw or b"").decode("utf-8", "replace").replace(
                    str(prefix), "<toolchain>").replace(str(cwd), "<scratch>").strip()

            row = dict(program=name, args=list(args), exit=child.returncode,
                       stdout=public(child.stdout), stderr=public(child.stderr))
            result["runs"].append(row)
            return row

        version = run("lean", "--version")
        if "version 4.35.0," not in version["stdout"]:
            raise ValueError("This control requires the Windows Lean 4.35.0 release.")
        direct = run("lean4lean", "Init.Prelude")
        native = run("leanchecker", "Init.Prelude")
        env["LEAN_PATH"] = os.pathsep.join((str(cwd), str(lib)))
        (cwd / "PalStockCheck.lean").write_bytes(SOURCE.encode())
        compile_result = run("lean", "-o", "PalStockCheck.olean", "PalStockCheck.lean")
        export_path = cwd / "PalStockCheck.ndjson"
        with export_path.open("wb") as out:
            export_result = run("leanexport", "PalStockCheck", "--", "palStockCheck", export=out)
        entries = [json.loads(line) for line in export_path.read_bytes().splitlines() if line]
        ids = {r["in"] for r in entries if r.get("str") == {"pre": 0, "str": "palStockCheck"}}
        assert any(r.get("thm", {}).get("name") in ids for r in entries), "Named theorem missing"
        result["export"] = {"bytes": export_path.stat().st_size, "sha256": digest(export_path),
                            "records": len(entries), "theorem": "palStockCheck"}
        external_export = run("lean4lean", "--import", export_path.name)
        native_export = run("leanchecker", "--from-export", export_path.name)
        result["observed_header_rejection"] = (
            direct["exit"] == 1 and "incompatible header" in direct["stderr"])
        result["controls_passed"] = all(
            record["exit"] == 0 for record in (native, compile_result, export_result,
                                               external_export, native_export))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("toolchain", type=Path, help="Unpacked lean-4.35.0-windows directory")
    parser.add_argument("--archive", type=Path, help="Official tar.zst to authenticate")
    parser.add_argument("--out", type=Path, help="Optional JSON receipt")
    args = parser.parse_args()
    report = replay(args.toolchain, args.archive)
    payload = json.dumps(report, indent=2) + "\n"
    if args.out:
        args.out.write_bytes(payload.encode())
    print(payload, end="")
    raise SystemExit(0 if report["observed_header_rejection"] and report["controls_passed"] else 1)
