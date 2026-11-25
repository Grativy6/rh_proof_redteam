"""Judge a PAL solution export against the independently published, fixed RH target.

Run on Linux with a Comparator-capable Lake and its published kernel executables
on PATH. The reference export is an input downloaded independently of the solution.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

EXPECTED = "bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9"
CONFIG = Path(__file__).resolve().parents[1] / "pal-rh" / "checks" / "rh-only.json"


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("challenge", type=Path)
    parser.add_argument("solution", type=Path)
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    if digest(args.challenge) != EXPECTED:
        parser.error("Supply the decompressed reference export with the pinned SHA-256.")
    c = json.loads(CONFIG.read_text(encoding="utf8"))
    if (c["theorem_names"] != ["riemannHypothesis"]
            or set(c["permitted_axioms"]) != {"propext", "Quot.sound", "Classical.choice"}
            or c["challenge_module"] != "Challenge" or c["solution_module"] != "PALSolution"
            or c["external_kernels"] != {"Lean paranoid": ["leanchecker-paranoid", "--silent", "--from-export"],
                                        "nanoda": ["nanoda_bin"]}):
        parser.error("The target, axiom list or replay configuration changed.")
    print("Challenge SHA-256", EXPECTED, flush=True)
    print("Solution SHA-256", digest(args.solution), flush=True)
    result = subprocess.run([args.lake, "comparator", "--config", str(CONFIG),
                             "--challenge-from-export", str(args.challenge.resolve()),
                             "--solution-from-export", str(args.solution.resolve())])
    return result.returncode


if __name__ == "__main__":
    sys.exit(main())
