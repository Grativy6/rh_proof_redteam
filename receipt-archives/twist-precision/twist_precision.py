"""Test all twist residues that can change the 5, 25 or 125 conditions."""

import argparse
import json
from pathlib import Path
import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "selmer-order-25"))
import jacobi_obstruction as jacobi
from verify_order25 import quadratic_class_number


def multipliers(q, m, twists):
    chi = np.full(q, -1, dtype=np.int64)
    u = np.arange(1, (q + 1) // 2, dtype=np.int64)
    chi[u * u % q] = 1
    chi[0] = 0
    f = m * q
    histogram = np.zeros(m, dtype=np.int64)
    for start in range(f // 2 + 1, f, 500000):
        a = np.arange(start, min(start + 500000, f), dtype=np.int64)
        np.add.at(histogram, a % m, chi[a % q])
    return [
        int(
            histogram
            @ np.array(
                [pow(a, -e - 1, m) if a % 5 else 0 for a in range(m)], dtype=np.int64
            )
        )
        % m
        for e in twists
    ]


def rebuild_norm():
    # An int32 log table uses 640 MB. Histogram updates are split into blocks.
    q, m, M, r = 106619, 125, 625, 159928501
    f = q * m
    assert jacobi.trial_prime(r) and r == 12 * f + 1 and jacobi.generator(r) == 7
    logs = np.empty(r, dtype=np.int32)
    step = 65536
    short = np.array([pow(7, i, r) for i in range(step)], dtype=np.int64)
    inc = pow(7, step, r)
    scale = 1
    for j in range(0, r - 1, step):
        n = min(step, r - 1 - j)
        logs[short[:n] * scale % r] = np.arange(j, j + n) % f
        scale = scale * inc % r
    hist = np.zeros(f, dtype=np.int32)
    for start in range(2, r, step):
        end = min(r, start + step)
        exps = -(logs[start:end] + logs[r + 2 - end : r + 2 - start][::-1]) % f
        np.add.at(hist, exps, 1)
    assert int(hist.sum()) == r - 2
    del logs
    v = jacobi.norm_q_squares((hist % M).astype(np.int64), q, m, M)
    i = np.arange(m, dtype=np.int64)
    non = next(t for t in range(2, q) if pow(t, (q - 1) // 2, q) == q - 1)
    return [v[i + m * ((b - i) * pow(m, -1, q) % q)].tolist() for b in (0, 1, non)]


def digit(record):
    m, q, M = 125, 106619, 625
    z, a, b = [np.array(v, dtype=np.int64) for v in record]
    root = next(k for k in range(M) if (k * k + q) % M == 0)
    p = (root - 1) * pow(2, -1, M) % M
    c = jacobi.Cyclo(m, M)
    plus = c.reduce(z + a * p + b * (-1 - p))
    minus = c.reduce(z + b * p + a * (-1 - p))
    sc = pow(12 * m * q + 1, (q - 1) // 2, M)
    assert np.array_equal(c.mul(plus, c.action(minus, -1)), sc * c.one % M)
    beta = c.one
    for k in range(1, m):
        if k % 5 == 0:
            continue
        weight = pow(k, -82, m)
        if weight > 62:
            weight -= m
        side = plus if weight > 0 else minus
        v = c.mul(c.action(side, k), c.action(side, -k)) * pow(sc, -1, M) % M
        beta = c.mul(beta, c.power(v, abs(weight)))
    assert np.array_equal(beta, c.action(beta, -1))
    checks = [jacobi.local_test(c, beta, n) for n in (1, 2, 3)]
    assert [x[0] for x in checks] == [True, True, False]
    assert checks[-1][1:] == (
        115,
        161,
        [
            (3, 4),
            (4, 1),
            (5, 4),
            (6, 1),
            (7, 4),
            (8, 3),
            (9, 1),
            (10, 3),
            (11, 1),
            (12, 2),
        ],
    )
    return checks[-1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rebuild-norm",
        action="store_true",
        help="recompute all 53309 square conjugates at q=106619",
    )
    args = parser.parse_args()
    for q, klass, k25, k125 in [
        (2179, 7, [0, 15, 5, 20, 10], [0, 75, 25, 100, 50]),
        (106619, 119, [0, 10, 20, 5, 15], [50, 100, 25, 75, 0]),
    ]:
        assert quadratic_class_number(-q) == klass
        assert multipliers(q, 25, range(1, 20, 4)) == k25
        assert multipliers(q, 125, range(1, 100, 20)) == k125
        print(q, "class number", klass, "mod-25 and mod-125 obstructions", k25, k125)
    record = json.loads(
        Path(__file__).with_name("orbit_coefficients.json").read_text(encoding="ascii")
    )
    if args.rebuild_norm:
        assert rebuild_norm() == record
        print("All 375 orbit coefficients reconstructed.")
    print("Twist 81 local obstruction", digit(record))


if __name__ == "__main__":
    main()
