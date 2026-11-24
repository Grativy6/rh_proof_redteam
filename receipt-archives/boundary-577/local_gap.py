"""Check the final local power gap and its two tame inertia readings.

The default uses the published end digits. Pass --binary or --alternate to
recover those digits from all coefficients of a fresh local computation.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import numpy as np

P = 577
MP = P**2
MOD = P**3
TAME_INDEX = 297


def polynomial_product(a, b):
    s = np.convolve(a, b)
    v = np.zeros(P, dtype=np.int64)
    v += s[:P]
    v[: len(s) - P] += s[P:]
    return (v[:-1] - v[-1]) % MP


def lower_uniformizer_power():
    g = pow(5, P, MP)
    v = np.zeros(P, dtype=np.int64)
    for i in range(P - 1):
        a = pow(g, i, MP)
        v[a % P] = pow(a * (P - 1), -1, MP)
    v[0] = -int(np.sum(v)) % MP
    a = (v[:-1] - v[-1]) % MP
    out = np.zeros(P - 1, dtype=np.int64)
    out[0] = 1
    for bit in bin(TAME_INDEX)[2:]:
        out = polynomial_product(out, out)
        if bit == "1":
            out = polynomial_product(out, a)
    return out


def read_binary(file):
    a = np.fromfile(file, dtype="<u4").astype(np.int64)
    assert len(a) == 4 * MP
    k = np.arange(MP, dtype=np.int64)
    t = pow(20, MP, MOD)
    ts = np.array([pow(t, j, MOD) for j in range(64)], dtype=np.int64)
    v = np.empty((4, MP), dtype=np.int64)
    for u in range(4):
        idx = k + MP * ((u - k) % 4)
        # Align the unramified fourth root with the original prime-level embedding.
        v[u] = a[idx] * ts[((idx - u) // 4 + 48 * u) % 64] % MOD
    v = v.reshape(4, P, P)
    v = (v[:, :-1, :] - v[:, -1:, :]) % MOD
    v[0, 0, 0] = (v[0, 0, 0] - 1) % MOD
    return v


def verify_array(v):
    assert v.shape == (4, P - 1, P) and not np.any(v % P)
    v = v.astype(np.int64) // P
    base = lower_uniformizer_power()
    low = int(v[1, 0, 0]) * pow(int(base[0]), -1, P) % P
    v[1, :, 0] = (v[1, :, 0] - low * base) % MP
    assert not np.any(v % P)
    h = (v // P).sum(axis=1) % P
    amp = int(h[1, 1])
    expected = np.array([0] + [pow(j, -297, P) for j in range(1, P)], dtype=np.int64)
    assert np.array_equal(h[1], amp * expected % P) and not np.any(h[[0, 2, 3]])
    j = np.arange(P, dtype=np.int64)
    binomial = np.ones(P, dtype=np.int64)
    for k in range(298):
        v = h @ binomial % P
        if k < 297:
            assert not np.any(v)
        else:
            high = int(v[1])
        binomial = binomial * (j - k) * pow(k + 1, -1, P) % P
    assert high == -amp * pow(math.factorial(297), -1, P) % P
    return low, amp, high, (low - 553 * high) % P


def report(data):
    assert pow(20, 144, P) == 553 and data["teich_y4"] == pow(20, MP, MOD)
    e = 64 * P
    levels = [min(P * j, e + j) for j in range(1, 66)]
    twice = [min(P * j, e + j) for j in levels]
    assert twice[-2:] == [73856, 73921] and 2 * e + 33 == 73889
    records = data["records"]
    z = np.array(
        [[x["unramified_dual"], x["divided_log_dual"]] for x in records], dtype=np.int64
    )
    assert (int(z[0, 0]) * int(z[1, 1]) - int(z[1, 0]) * int(z[0, 1])) % P == 291
    for rec in records:
        for v in rec["weights"]:
            amp = v["residue_row_amplitude"]
            high = -amp * pow(math.factorial(297), -1, P) % P
            assert v["high"] == high and v["low"] == rec["divided_log_dual"]
            assert (v["low"] - 553 * high) % P == v["local_reading"]
            s = v["twist"] + 1
            assert (
                v["local_reading"]
                == (
                    406 * s * rec["unramified_dual"]
                    + (1 + 177 * s) * rec["divided_log_dual"]
                )
                % P
            )
        assert (
            rec["weights"][-1]["local_reading"] * pow(rec["unramified_dual"], -1, P) % P
            == 177
        )
    inv = pow(291, -1, P) * np.array([[367, -101], [-514, 507]], dtype=np.int64) % P
    for j, expect in [(171368, [2, 461]), (296, [230, 8]), (265256, [110, 459])]:
        pairing = np.array(
            [(261 + 37 * (j + 1)) % P, 202 * (j + 1) % P], dtype=np.int64
        )
        tame = (inv @ pairing) % P
        assert tame.tolist() == expect and np.array_equal(z.T @ tame % P, pairing)
        # z has primes as rows. The inverse above inverts the matrix with
        # functionals as rows and primes as columns.
        print("twist", j, "dual pairings", pairing.tolist(), "tame inertia", expect)
    print("Both primes give the obstruction 177 at the exceptional twist.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--binary", type=Path)
    group.add_argument("--alternate", type=Path)
    parser.add_argument("--prime", type=int)
    parser.add_argument("--twist", type=int)
    args = parser.parse_args()
    data = json.loads(
        Path(__file__)
        .with_name("second_level_readings.json")
        .read_text(encoding="ascii")
    )
    if args.binary or args.alternate:
        primes = {r["prime"] for r in data["records"]}
        twists = {w["twist"] for r in data["records"] for w in r["weights"]}
        if args.prime not in primes or args.twist not in twists:
            parser.error(
                "supply a recorded --prime and --twist with the coefficient file"
            )
    elif args.prime is not None or args.twist is not None:
        parser.error("--prime and --twist need a coefficient file")
    report(data)
    if args.binary or args.alternate:
        rec = next(r for r in data["records"] if r["prime"] == args.prime)
        want = next(r for r in rec["weights"] if r["twist"] == args.twist)
        if args.binary:
            assert (
                hashlib.sha256(args.binary.read_bytes()).hexdigest()
                == want["binary_sha256"]
            )
            v = read_binary(args.binary)
        else:
            v = np.load(args.alternate, allow_pickle=False)
        got = verify_array(v)
        assert got == (
            want["low"],
            want["residue_row_amplitude"],
            want["high"],
            want["local_reading"],
        )
        print("Verified all", v.size, "coefficients and recovered", got)


if __name__ == "__main__":
    main()
