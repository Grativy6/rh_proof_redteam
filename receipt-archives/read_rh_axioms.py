"""Read the five compiled RH endpoint receipts with Lean 4.33.1.

This downloads the published cache manifest, one small module, and two
independent build manifests. It does not build the full RH project.
"""

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
from urllib.request import Request, urlopen


MIT = "https://math.mit.edu/~drew/grh/"
CACHE = "https://rh-cache.taucetiproject.org/"
MANIFEST = CACHE + "bootstrap/e50d09817ad81469f737e8f637561e6ccf86c670/modules.jsonl.gz"
HASHES = {
    "modules.jsonl.gz": "292caa386a620d935cfc736b56fcceaab9fe7073086693b62e899c1ee4725f04",
    "audit.log": "0a1473fce6eed840011f4a76b1c51558fc6f03edd1e6bd1ee542e6c738d87a62",
    "project-oleans.sha256": "375cbee2fc3fc0f5088ef2e6dc9a5ac5530924310dc62422ec65aac9dc4c1d25",
    "sandbox-project-oleans.sha256": "51319e37e06fd80dc16cdbe3380e13967603cc36d529389f835ca48076c24859",
}
ROOT_SHA256 = "9146dfb4148e24d2252e04c50742f3e49dd126dfcc5006d10bf5f873ddf796ad"


def download(url, expected):
    with urlopen(Request(url, headers={"User-Agent": "PAL-RH-source-check"}), timeout=60) as reply:
        data = reply.read()
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError("Digest mismatch for " + url)
    return data


def read(bin_dir, workspace, local_manifest=None):
    workspace.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, PATH=str(bin_dir) + os.pathsep + os.environ["PATH"])
    suffix = ".exe" if os.name == "nt" else ""
    lean = bin_dir / ("lean" + suffix)
    version = subprocess.check_output([str(lean), "--version"], env=env).decode().strip()
    if "version 4.33.1," not in version:
        raise ValueError(version)
    packed = local_manifest.read_bytes() if local_manifest else download(MANIFEST, HASHES["modules.jsonl.gz"])
    if hashlib.sha256(packed).hexdigest() != HASHES["modules.jsonl.gz"]:
        raise ValueError("Unexpected local cache manifest")
    lines = iter(gzip.decompress(packed).splitlines())
    header = json.loads(next(lines))
    if header["modules"] != 175187 or header["toolchain"] != "leanprover/lean4:v4.33.1":
        raise ValueError(header)
    root_records = [json.loads(line) for line in lines if line.startswith(b'["Main",')]
    if len(root_records) != 1:
        raise ValueError("Expected one Main module")
    _, dep_hash, filename, digest = root_records[0]
    archive = workspace / filename
    archive.write_bytes(download(CACHE + "artifacts/leanprover-community/riemann-hypothesis/"
                                 + filename.removesuffix(".ltar") + ".art", digest))
    lib, ir = workspace / "lib", workspace / "ir"
    lib.mkdir(exist_ok=True)
    ir.mkdir(exist_ok=True)
    jobs = [{"file": str(archive), "hash": dep_hash, "base": [str(lib), str(ir)]}]
    subprocess.run([str(bin_dir / ("leantar" + suffix)), "--jobs", "1", "-f", "-x", "-j", "-"],
                   input=json.dumps(jobs).encode(), cwd=workspace, env=env, check=True)
    main = lib / "Main.olean"
    if hashlib.sha256(main.read_bytes()).hexdigest() != ROOT_SHA256:
        raise ValueError("Unexpected compiled Main module")
    for name in ("project-oleans.sha256", "sandbox-project-oleans.sha256"):
        manifest = download(MIT + name, HASHES[name])
        if (ROOT_SHA256 + "  ./Main.olean").encode() not in manifest.splitlines():
            raise ValueError("Root module did not match " + name)
    reader = Path(__file__).resolve().with_name("ReadAxiomReceipt.lean")
    raw = subprocess.check_output([str(lean), "--run", str(reader), str(main)], env=env, cwd=workspace)
    rows = [json.loads(line) for line in raw.splitlines() if line.strip()]
    audit = download(MIT + "audit.log", HASHES["audit.log"]).decode()
    expected_names = {"riemannHypothesis", "riemannZeta_eq_zero_re",
                      "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re",
                      "LFunction_eq_zero_re_of_isPrimitive"}
    if {row["name"] for row in rows} != expected_names or len(rows) != 5:
        raise ValueError("Missing or extra endpoint in compiled receipt")
    for row in rows:
        line = "'" + row["name"] + "' depends on axioms: [" + ", ".join(row["axioms"]) + "]"
        if line not in audit.splitlines():
            raise ValueError(line)
    rh = next(row for row in rows if row["name"] == "riemannHypothesis")
    if rh["typeExpr"] != "RiemannHypothesis" or rh["bodyConstants"] != ["rhOfAll"]:
        raise ValueError("Unexpected headline statement or proof body")
    result = {"lean": version, "olean_sha256": ROOT_SHA256, "lookup_file": filename,
              "download_sha256": digest, "verified_build_manifests": 2,
              "source_revision": "40e56bab026552e089d7afcfeff08d2defb9c005", "endpoints": rows}
    (workspace / "rh-endpoints.json").write_bytes((json.dumps(result, indent=2) + "\n").encode())
    print("5 compiled endpoint records agreed with the upstream axiom transcript and both module manifests.")


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--bin", type=Path, required=True, help="Lean 4.33.1 bin directory")
    cli.add_argument("--work", type=Path, required=True)
    cli.add_argument("--manifest", type=Path, help="Optional already downloaded pinned modules.jsonl.gz")
    args = cli.parse_args()
    read(args.bin.resolve(), args.work.resolve(), args.manifest)
