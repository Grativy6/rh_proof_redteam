"""Check the 64-bit prime boundary, the dense runtime outputs and the optional pinned source scan."""

import argparse
from contextlib import redirect_stdout
from io import StringIO
import json
from math import gcd, prod
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

from check_release_prime_large import (
    MODULUS,
    PRIMES_FILE,
    T,
    check_certificates,
    elementary_prime,
)

PIN = "40e56bab026552e089d7afcfeff08d2defb9c005"
EXPONENT = 136279841
MAX_WORD_PRIME = 2**64 - 59
# Each tuple supplies a primitive-root witness and the full factorization of n-1.
CERT = {
    3: (2, [(2, 1)]),
    5: (2, [(2, 2)]),
    7: (3, [(2, 1), (3, 1)]),
    11: (2, [(2, 1), (5, 1)]),
    13: (2, [(2, 2), (3, 1)]),
    17: (3, [(2, 4)]),
    23: (5, [(2, 1), (11, 1)]),
    31: (3, [(2, 1), (3, 1), (5, 1)]),
    71: (7, [(2, 1), (5, 1), (7, 1)]),
    73: (5, [(2, 3), (3, 2)]),
    137: (3, [(2, 3), (17, 1)]),
    547: (2, [(2, 1), (3, 1), (7, 1), (13, 1)]),
    1427: (2, [(2, 1), (23, 1), (31, 1)]),
    2131: (2, [(2, 1), (3, 1), (5, 1), (71, 1)]),
    15331: (2, [(2, 1), (3, 1), (5, 1), (7, 1), (73, 1)]),
    5594472617641: (13, [(2, 3), (3, 1), (5, 1), (1427, 1), (2131, 1), (15331, 1)]),
    MAX_WORD_PRIME: (2, [(2, 2), (11, 1), (137, 1), (547, 1), (5594472617641, 1)]),
}
# Proper divisors of every odd candidate above the stated prime through 2^64-1.
ODD_DIVISORS = (
    41,
    3,
    29,
    5,
    3,
    31,
    11071,
    3,
    5,
    139646831,
    3,
    17,
    827,
    3,
    13,
    11,
    3,
    7,
    5,
    3,
    19,
    53,
    3,
    5,
    7,
    3,
    11,
    13,
    3,
)
PATTERN = r"(^|[^[:alnum:]_])(U?Int(8|16|32|64)|USize|ISize|BitVec|Float(32)?|toU?Int(8|16|32|64)|toUSize|toISize)([^[:alnum:]_]|$)"


def released_example():
    with redirect_stdout(StringIO()):
        check_certificates()
    low32 = T % 2**32
    low64 = T % 2**64
    assert T.bit_length() == 385 and elementary_prime(low32)
    assert low64 == 3 * 195559350344448683 and pow(5, T - 1, T) == 1
    low_test = pow(5, low64 - 1, low64)
    assert low_test == 497633511686448868
    return {
        "bits": 385,
        "decimal_digits": len(str(T)),
        "certificate": "replayed full-width Lucas chain",
        "low_32_bits": low32,
        "low_32_is_prime": True,
        "low_64_bits": low64,
        "low_64_divisor": 3,
        "cofactor": low64 // 3,
        "full_base_5_residue": 1,
        "low_64_base_5_residue": low_test,
    }


def certified_primes():
    other = json.loads(
        Path(__file__).with_name("word_prime_order_witnesses.json").read_bytes()
    )
    tree = {**CERT, **{int(n): w for n, w in other.items()}}
    established = {2}
    for n, (a, factors) in sorted(tree.items()):
        assert all(q in established for q, _ in factors)
        assert prod(q**v for q, v in factors) == n - 1
        assert pow(a, n - 1, n) == 1
        assert all(gcd(pow(a, (n - 1) // q, n) - 1, n) == 1 for q, _ in factors)
        established.add(n)
    return established


def norm_family(primes):
    full = []
    low = []
    for k in range(1, 973):
        n = 1 + 599 * (k * MODULUS) ** 2
        word = n % 2**64
        assert word > 1 and word % 2 == 1
        if pow(2, n - 1, n) == 1:
            assert k in (363, 663, 972)  # full Lucas tests run by released_example
            full.append(k)
        if pow(2, word - 1, word) == 1:
            assert word in primes
            low.append(k)
    assert full == [363, 663, 972] and len(low) == 45 and not set(low) & set(full)
    true_values = [1 + 599 * (k * MODULUS) ** 2 for k in full]
    possible_widths = []
    for width in range(1, T.bit_length() + 1):
        residues = [value % (2**width) for value in true_values]
        if all(x > 1 and pow(2, x - 1, x) == 1 for x in residues):
            possible_widths.append(width)
    assert possible_widths == [14, 385]
    by_fourteen = [
        k
        for k in range(1, 973)
        if elementary_prime((1 + 599 * (k * MODULUS) ** 2) % (2**14))
    ]
    assert len(by_fourteen) == 365 and 2 in by_fourteen and 2 not in full
    witness14 = 1 + 599 * (2 * MODULUS) ** 2
    assert witness14 % 3 == 0 and witness14 % (2**14) == 15361
    first = 1 + 599 * (26 * MODULUS) ** 2
    assert 26 in low and first % 3 == 0 and first % 2**64 == 2813010139532958721
    return {
        "scanned_parameter_interval": [1, 972],
        "full_prime_parameters": full,
        "low_64_prime_parameters": low,
        "true_positives": 0,
        "first_width_with_all_972_verdicts_correct": 385,
        "widths_passing_Fermat_for_all_three_actual_primes": possible_widths,
        "width_14_actual_prime_readings": len(by_fourteen),
        "width_14_false_positive": {"k": 2, "low_word": 15361, "full_divisor": 3},
        "false_positives": 45,
        "false_negatives": 3,
        "true_negatives": 924,
        "reverse_witness_parameter": 26,
        "reverse_witness_full_divisor": 3,
        "reverse_witness_prime_low_word": first % 2**64,
        "attribution": "The release supplies the actual k=972 example. The parameter sweep is the earlier PAL reconstruction.",
    }


def bounds():
    established = certified_primes()
    candidates = range(MAX_WORD_PRIME + 2, 2**64, 2)
    assert len(candidates) == len(ODD_DIVISORS)
    for n, d in zip(candidates, ODD_DIVISORS):
        assert 1 < d < n and n % d == 0
    x = 2**64 + 17
    assert x % 2**64 == 17 and x == 3 * 6148914691236517211
    for width in (1, 5, 17, 32, 64, 127, 1024):
        m = 2**width
        for k in (1, 2, 17):
            twin = 17 + (m ** (2 * k))
            assert twin % m == 17 % m and twin > 17 and twin % 3 == 0
    runs = []
    for e in (EXPONENT, 17 * EXPONENT):
        runs.append(
            {
                "bits": e,
                "packed_bytes": (e + 7) // 8,
                "mod131071": (pow(2, e, 131071) - 1) % 131071,
                "mod17": (pow(2, e, 17) - 1) % 17,
                "last_nine_decimal_digits": (pow(2, e, 10**9) - 1) % 10**9,
            }
        )
    return {
        "largest_unsigned_64_bit_prime": MAX_WORD_PRIME,
        "release_prime": released_example(),
        "norm_family": norm_family(established),
        "higher_composites": 58,
        "explicit_composite_twin": x,
        "runtime_crosschecks": runs,
    }


def release(repo):
    def git(*args, valid=(0,)):
        result = subprocess.run(
            ["git", "-c", "core.quotepath=false", "-C", str(repo), *args],
            capture_output=True,
        )
        if result.returncode not in valid:
            raise RuntimeError(result.stderr.decode(errors="replace"))
        return result.stdout

    paths = set(
        git("ls-tree", "-rz", "--name-only", PIN, "src")
        .decode()
        .strip("\0")
        .split("\0")
    )
    expected = {p for p in paths if p.endswith(".lean")}
    selected = ["--", "src/**/*.lean", "src/*.lean"]
    control = git("grep", "--threads=4", "-l", "-z", "-I", "-e", "^", PIN, *selected)
    covered = {p.split(":", 1)[1] for p in control.decode().strip("\0").split("\0")}
    assert covered == expected
    matches = git(
        "grep", "--threads=4", "-n", "-I", "-E", PATTERN, PIN, *selected, valid=(0, 1)
    )
    lines = matches.decode().splitlines()
    paths_with_hits = sorted({s.split(":", 2)[1] for s in lines})

    def source(path):
        return git("show", PIN + ":" + path).decode()

    assert f"theorem prime_large : Nat.Prime {T}" in source(PRIMES_FILE)
    main = source("src/Main.lean")
    transfer = source("src/Formalism/GammaFactorNonvanishing/CritLine.lean")
    assert re.search(
        r"theorem riemannHypothesis\s*:\s*RiemannHypothesis\s*:=\s*rhOfAll\b", main
    )
    assert (
        "theorem Formalism.VW.rh_of_every" in transfer
        and "LFunction_modOne_eq" in transfer
    )
    return {
        "pin": PIN,
        "covered_lean_files": len(covered),
        "matched_lines": len(lines),
        "matching_files": paths_with_hits,
        "exact_numeric_type_pattern": PATTERN,
        "scope": "Explicit named machine representations in the release's src Lean files. This test does not expand aliases, inspect transitive Mathlib or prove runtime correctness.",
    }


def actual(lake, project):
    source = Path(__file__).with_name("IntegerWidth.lean").resolve()
    result = []
    for row in bounds()["runtime_crosschecks"]:
        exponent = row["bits"]
        output = subprocess.check_output(
            [lake, "env", "lean", "--run", str(source), str(exponent)],
            cwd=project,
            text=True,
        )
        expected = (
            f"bits={exponent} bytes={row['packed_bytes']} mod131071={row['mod131071']} "
            f"mod17={row['mod17']} last9={row['last_nine_decimal_digits']}"
        )
        assert (
            expected in output
            and "UInt64=0 Nat=18446744073709551616 twin64=17" in output
        )
        result.append(expected)
    with TemporaryDirectory(prefix="pal-width-") as tmp:
        negative = Path(tmp) / "NarrowingControl.lean"
        negative.write_text(
            "import Mathlib.Data.Nat.Prime.Defs\n"
            "example : Nat.Prime (2^64+17) := by\n"
            "  exact (show Nat.Prime 17 by decide)\n",
            encoding="utf8",
        )
        reject = subprocess.run(
            [lake, "env", "lean", str(negative)],
            cwd=project,
            capture_output=True,
            text=True,
        )
        msg = reject.stdout + reject.stderr
        assert reject.returncode != 0 and "type mismatch" in msg.lower()
        assert "Nat.Prime 17" in msg and "Nat.Prime (2 ^ 64 + 17)" in msg
    return {
        "dense_runs": result,
        "invalid_prime_transfer": "rejected with a type mismatch",
    }


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--release",
        type=Path,
        help="Local checkout or mirror of the pinned published RH source",
    )
    ap.add_argument(
        "--project",
        type=Path,
        help="Built pinned Lake project, to replay the Lean tests",
    )
    ap.add_argument(
        "--lake",
        default="lake",
        help="Pinned Lake executable on PATH or an absolute path",
    )
    args = ap.parse_args()
    out = bounds()
    if args.project:
        out["lean"] = actual(args.lake, args.project)
    if args.release:
        out["release_source"] = release(args.release)
    print(json.dumps(out, indent=2))
