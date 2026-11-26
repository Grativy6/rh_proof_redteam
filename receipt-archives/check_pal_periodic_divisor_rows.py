"""Exact integer-period verification of upper masks, with rational log enclosures."""

import json
from fractions import Fraction as Q
from math import lcm
from pathlib import Path

from check_pal_dense_square_payment import display
from check_pal_dyson_window import SCALE, log_int


def node(k, j):
    m = k // j
    return m * k - j * m * (m + 1) // 2


def check(period, coeff):
    den = lcm(*(c.denominator for c in coeff.values()))
    weights = {j: int(den * c) for j, c in coeff.items()}
    assert all(period % j == 0 for j in weights)
    assert (
        sum(weights.values()) == 0
        and sum(j * v for j, v in weights.items()) == -2 * den
    )
    excess = []
    for k in range(1, period + 1):
        v = 2 * den + sum(c * (k % j) * (j - k % j) for j, c in weights.items())
        raw = sum(j * c * node(k, j) for j, c in weights.items()) - den * (k - 1)
        assert v == 2 * raw and raw >= 0
        excess.append(raw)
    a = b = -Q(1, 2)
    for j, c in coeff.items():
        lo, hi = (Q(t, SCALE) for t in log_int(j))
        x, y = -c * lo / 2, -c * hi / 2
        a += min(x, y)
        b += max(x, y)
    result = {
        "period": period,
        "labels": len(coeff),
        "denominator": str(den),
        "all_nonnegative_addresses": len(excess),
        "positive_addresses": sum(v > 0 for v in excess),
        "area_excess": display((a, b), 12),
    }
    return excess, den, (a, b), result


def audit():
    primary = {}
    for L, raw in ((4, {1: 1, 2: -1, 4: -2}), (6, {1: 1, 2: -1, 3: -1, 6: -1})):
        e, d, delta, res = check(L, {j: Q(a, j) for j, a in raw.items()})
        assert e == [0] * (L - 1) + [d]
        assert delta[0] > Q(1, 210)
        primary[str(L)] = res
    candidates = []
    for row in json.loads(
        Path(__file__).with_name("periodic_divisor_rows.json").read_bytes()
    ):
        L = row["period"]
        c = {int(k): Q(v) for k, v in row["weights_a_over_label"].items()}
        values, den, delta, record = check(L, c)
        assert delta[1] < Q(1, 210)
        allowed = (2, 3, 5) if L == 2160 else (2, 3, 5, 7)
        for j in c:
            for p in allowed:
                while j % p == 0:
                    j //= p
            assert j == 1

        # Pin the loss transport at 6, with the exact second differences.
        def e(k):
            return Q(values[(k - 1) % L], den)

        def a(j):
            return j * c.get(j, 0)

        assert e(6) == a(1) + a(47) - a(49) + 2 * e(7) - e(8) + e(50) - 2 * e(
            49
        ) + 2 * e(47) - e(46)
        record["excess_at_6"] = str(e(6))
        record["excess_at_7"] = str(e(7))
        record["allowed_prime_factors"] = allowed
        candidates.append(record)
    return {
        "sharp_witnesses": primary,
        "below_one_over_210": candidates,
        "node_price": "sum_(k>=2) E(k)/(k*(k^2-1))",
        "certificate_scope": "All integers via one exact period, with zero drift and balanced reciprocal weights.",
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
