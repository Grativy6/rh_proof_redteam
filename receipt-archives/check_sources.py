"""Verify the public source pins and optionally reconcile the supplied research pack."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import zipfile


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git(repo, *args, data=None):
    return subprocess.run(
        ["git", "-C", str(repo), *args], input=data, stdout=subprocess.PIPE, check=True
    ).stdout


def read_sources(repo, revision, paths):
    ordered = sorted(paths)
    request = "".join(f"{revision}:{path}\n" for path in ordered).encode()
    stream = io.BytesIO(git(repo, "cat-file", "--batch", data=request))
    sources = {}
    for path in ordered:
        header = stream.readline().split()
        require(len(header) == 3 and header[1] == b"blob", f"Missing Git blob: {path}")
        size = int(header[2])
        raw = stream.read(size)
        require(len(raw) == size and stream.read(1) == b"\n", f"Truncated blob: {path}")
        sources[path] = (header[0].decode(), raw)
    return sources


def pack_rows(path, pins):
    require(digest(path.read_bytes()) == pins["sha256"], "Unexpected handoff ZIP digest")
    rows = []
    prefix = pins["member_root"] + "/"
    with zipfile.ZipFile(path) as archive:
        def read(name):
            return archive.read(prefix + name)

        manifest = json.loads(read("MANIFEST_SHA256.json"))
        listed = {prefix + row["path"] for row in manifest}
        listed.add(prefix + "MANIFEST_SHA256.json")
        members = [item.filename for item in archive.infolist() if not item.is_dir()]
        require(len(members) == len(listed) and set(members) == listed, "Manifest inventory differs")
        for row in manifest:
            raw = read(row["path"])
            require(len(raw) == row["bytes"] and digest(raw) == row["sha256"], row["path"])

        for name, field in pins["source_manifests"].items():
            content = json.loads(read("evidence/" + name))
            for row in (content[field] if field else content):
                source_path = row["path"]
                if not source_path.startswith("src/"):
                    source_path = "src/" + source_path
                rows.append((source_path, row))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("release", type=Path, help="Git checkout or bare mirror containing the pinned commit")
    parser.add_argument("--handoff", type=Path, help="Optional original research pack from 23 November")
    args = parser.parse_args()
    record = json.loads(Path(__file__).with_name("source-pins.json").read_text(encoding="utf-8"))
    revision = record["release"]["revision"]
    tree = git(args.release, "rev-parse", revision + "^{tree}").decode().strip()
    require(tree == record["release"]["tree"], "Release tree differs")
    primary = [(row["path"], row) for row in record["release"]["files"]]
    extra = pack_rows(args.handoff, record["handoff"]) if args.handoff else []
    sources = read_sources(args.release, revision, {path for path, _ in primary + extra})
    for path, row in primary + extra:
        oid, data = sources[path]
        if "sha256" in row:
            require(digest(data) == row["sha256"], f"SHA-256 differs: {path}")
        if "bytes" in row:
            require(len(data) == row["bytes"], f"Byte length differs: {path}")
        if "blob_sha" in row:
            require(oid == row["blob_sha"], f"Git blob differs: {path}")
    print(f"Verified {len(primary)} selected files at {revision}.")
    if args.handoff:
        print(f"Verified the handoff archive and {len(extra)} references to {len({p for p, _ in extra})} distinct release files.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, ValueError, zipfile.BadZipFile, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
