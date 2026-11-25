"""Check the released Lucas chain and the finite family of quadratic norms."""

import argparse
from math import isqrt, prod
from pathlib import Path
import re
import subprocess


REV = "40e56bab026552e089d7afcfeff08d2defb9c005"
PRIMES_FILE = "src/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean"
A, B = 413718278401, 603339156001
MODULUS = 16 * 571 * 599 * (A * B)**2
T = 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937


def elementary_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def lucas(n, base, factors, proved):
    assert set(factors) <= proved
    assert n - 1 == prod(p**e for p, e in factors.items())
    assert pow(base, n - 1, n) == 1
    assert all(pow(base, (n - 1) // p, n) != 1 for p in factors)
    proved.add(n)


def check_certificates():
    small = {2, 3, 5, 7, 11, 13, 17, 571, 599}
    assert all(elementary_prime(p) for p in small)
    proved = small.copy()
    lucas(A, 34, {2: 8, 3: 3, 5: 2, 7: 1, 571: 1, 599: 1}, proved)
    lucas(B, 17, {2: 5, 3: 2, 5: 3, 7: 2, 571: 1, 599: 1}, proved)
    common = {571: 2, 599: 3, A: 4, B: 4}
    cases = {
        363: common | {2: 8, 3: 2, 11: 4},
        663: common | {2: 8, 3: 2, 13: 2, 17: 2},
        972: common | {2: 12, 3: 10},
    }
    passed = []
    for k in range(1, 973):
        n = 1 + 599 * (k * MODULUS)**2
        if pow(2, n - 1, n) == 1:
            assert k in cases
            lucas(n, 5, cases[k], proved)
            passed.append(k)
    assert passed == [363, 663, 972]
    assert 1 + 599 * (972 * MODULUS)**2 == T
    assert T.bit_length() == 385 and len(str(T)) == 116
    assert (599 + 1) % 571 == 29
    print(f"Lucas-certified norm parameters {passed}. Base 2 rejects all other 969.")
    print(f"Release prime: {T}")


def inspect_source(repo):
    def git(*args):
        return subprocess.check_output(["git", "-C", str(repo), *args])

    metadata = git("cat-file", "-p", REV).split(b"\n\n", 1)[0].splitlines()
    assert not any(row.startswith(b"parent ") for row in metadata)
    files = git("ls-tree", "-rz", "--name-only", REV, "--", "src").split(b"\0")
    assert sum(f.endswith(b".lean") for f in files) == 175187
    # These are specifically same-line decimal Nat.Prime statements in the Lean source.
    rows = git("grep", "-n", "-I", "-E", r"Nat\.Prime[[:space:]]+[0-9]", REV, "--", "*.lean").splitlines()
    scan = re.compile(rb"\bNat\.Prime[ \t]+([0-9]+(?:_[0-9]+)*)\b")
    largest = max(int(number) for row in rows for number in scan.findall(row))
    assert largest == T
    target = git("show", REV + ":" + PRIMES_FILE).decode("utf8").splitlines()
    assert target[517].startswith(f"theorem prime_large : Nat.Prime {T} :=")
    search = subprocess.run(["git", "-C", str(repo), "grep", "-n", "-I", "-E",
                             r"(^|[^[:alnum:]_])(577|2663)([^[:alnum:]_]|$)",
                             REV, "--", "*.lean"], capture_output=True)
    assert search.returncode == 1 and not search.stdout and not search.stderr
    print("Original parent count 0. Inspected 175,187 Lean files. No separate decimal 577 or 2663.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="Git repository containing the published revision")
    args = parser.parse_args()
    check_certificates()
    if args.source:
        inspect_source(args.source)
