"""Recover the descended wild circular-unit class at three split primes."""

import argparse
import hashlib
from pathlib import Path
import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "fixed-character-577"))
from bounds import char2
from fourier_witness import primitive, roots
from dual_primes import readings
from real_norm_units import base_residue

P = 577
D = 256
HISTOGRAM_SHA256 = "24e2bd97aee0b8a24e2111904760f7420f19d66bdd5389015591307042fdd1eb"


def product(rows, r):
    while rows.shape[-1] > 1:
        if rows.shape[-1] % 2:
            rows = np.concatenate(
                (rows, np.ones(rows.shape[:-1] + (1,), dtype=np.int64)), axis=-1
            )
        rows = rows[..., ::2] * rows[..., 1::2] % r
    return rows[..., 0]


def split_prime(r):
    m = P**2
    g = primitive(r)
    assert (r - 1) % (D * m) == 0 and (r - 1) ** 2 < 2**63
    v = np.arange(1, D, 2)
    tame = roots(pow(g, (r - 1) // D * pow(m, -1, D), r), D, r)[v]
    wild = roots(pow(g, (r - 1) // m * pow(D, -1, m), r), m, r)
    t = np.array([pow(i, P, m) for i in range(1, P)], dtype=np.int64)
    chi = np.array(char2(), dtype=np.int64)
    weights = (
        chi[v, None] * np.array([pow(i, 296, P) for i in range(1, P)])[None, :] % P
    ).ravel()
    order = np.argsort(weights)
    assert np.all(weights[order].reshape(P - 1, 128) == np.arange(1, P)[:, None])
    logs = {x: i for i, x in enumerate(roots(pow(g, (r - 1) // P, r), P, r))}
    exponents = []
    for j in range(P):
        factors = ((1 - tame[:, None] * wild[t * (1 + P * j) % m][None, :]) % r).ravel()
        base = product(factors[order].reshape(P - 1, 128), r)
        exp = np.arange(1, P, dtype=np.int64)
        values = np.ones(P - 1, dtype=np.int64)
        while np.any(exp):
            values = np.where(exp % 2, values * base % r, values)
            exp //= 2
            base = base * base % r
        exponents.append(logs[pow(int(product(values, r)), (r - 1) // P, r)])
    assert sum(exponents) % P == 0
    # (tau-1)^(p-2) has coefficients -(j+1) on tau^j modulo p.
    return -sum((j + 1) * n for j, n in enumerate(exponents)) % P


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--histogram",
        type=Path,
        help="independently rebuild dual readings at the third prime",
    )
    args = parser.parse_args()
    controls = {
        340919297: (26, 68, 507, 514),
        1022757889: (488, 210, 101, 367),
        1278447361: (44, 82, 183, 468),
    }
    for r, (e, rho, u, v) in controls.items():
        assert base_residue(r)[2] == e and split_prime(r) == rho
        assert (523 * e + 376 * rho) % P == u and (251 * e + 251 * rho) % P == v
        print(r, "unit and derivative", e, rho, "dual characters", u, v)
    if args.histogram:
        with args.histogram.open("rb") as f:
            assert hashlib.file_digest(f, "sha256").hexdigest() == HISTOGRAM_SHA256
        u, v = readings(1278447361, args.histogram)
        assert (u, v.tolist()) == (183, [0, 468, 0, 0])
    local, ideal = 488, 567
    for r, (_, rho, u, v) in controls.items():
        h = (406 * u + 178 * v) % P
        assert (8 * 223 * h * local + u * ideal - 576 * 298 * rho) % P == 0
    assert 231 * ideal % P == 575 and (local + 95 * 171) % P == 0
    assert 8 * 47 * 171 % P == 249 and 249 * pow(413, -1, P) % P == 2
    assert (8 * 47 * local + 231 * ideal) % P == 0
    assert (8 * local % P, 575 * pow(268, -1, P) % P) == (442, 366)
    assert -2 * pow(296, -1, P) % P == 269
    print("Named base unit cyclic-norm defect 249; preimage ideal reading 2.")
    print(
        "Descended derivative local coefficient 488 and divided ideal reading -2; simultaneous norm defect 0."
    )


if __name__ == "__main__":
    main()
