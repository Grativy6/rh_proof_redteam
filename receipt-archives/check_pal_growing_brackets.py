"""Reprice upper divisor rows and the single-boundary repair using exact integers."""

import json
from fractions import Fraction as F
from pathlib import Path

from check_pal_divisor_brackets import UP, twice_area
from check_pal_dyson_window import SCALE, log_int


def enclosure(low, high, digits=12):
    den = 10**digits
    a = low.numerator * den // low.denominator
    b = -(-high.numerator * den // high.denominator)

    def show(value):
        sign = "-" if value < 0 else ""
        q, r = divmod(abs(value), den)
        return f"{sign}{q}.{r:0{digits}d}"

    return [show(a), show(b)]


def arithmetic_price(coeffs):
    # coeffs[j-1] is the actual normalized coefficient of U_j(t).
    low = high = F(0)
    for j, a in enumerate(coeffs, 1):
        lo_log, hi_log = log_int(j)
        weight = -a / F(2 * j)
        if weight < 0:
            lo_log, hi_log = hi_log, lo_log
        low += weight * F(lo_log, SCALE)
        high += weight * F(hi_log, SCALE)
    excess_low, excess_high = low - F(1, 2), high - F(1, 2)
    cost = sum(abs(a) for a in coeffs)
    assert 0 < excess_low <= excess_high
    return excess_low, excess_high, cost


def check_upper(row):
    c = row["coefficients"]
    M, L, D = row["support"], row["direct_through"], row["denominator"]
    assert len(c) == M and D > 0 and sum(c) == 0
    first = sum(j * v for j, v in enumerate(c, 1))
    abs2 = sum(j * j * abs(v) for j, v in enumerate(c, 1))
    slope = -first - 2 * D
    tail = 4 * ((L + 1) * slope + 2 * D) - abs2
    assert slope >= 0 and tail >= 0
    for k in range(1, L + 1):
        # The doubled signed reading is evaluated directly at the actual quotient.
        assert sum(v * twice_area(j, k) for j, v in enumerate(c, 1)) >= 2 * D * (k - 1)
    return arithmetic_price([F(j * v, D) for j, v in enumerate(c, 1)])


def frozen():
    def gap(k):
        numerator = sum(c * twice_area(j, k) for j, c in enumerate(UP, 1)) - 204 * (k - 1)
        return F(numerator, 204 * k)

    total = sum((gap(k) + gap(k + 1)) * (F(1, k) - F(1, k + 1)) / 2 for k in range(1, 17))
    assert total == F(1568059, 885224340)
    return total


def mobius(M):
    mu = [1] * (M + 1)
    primes = bytearray(b"\x01") * (M + 1)
    for p in range(2, M + 1):
        if primes[p]:
            for k in range(p, M + 1, p):
                primes[k] = 0
                mu[k] = -mu[k]
            for k in range(p * p, M + 1, p * p):
                mu[k] = 0
    return mu


def ramp(j, k):
    q = k // j
    return q * k - j * q * (q + 1) // 2


def single_repair(M):
    L = 64 * M
    mu = mobius(M - 1)
    terminal = -M * sum(F(mu[j], j) for j in range(1, M))
    source = [0] * (L + 1)
    for j in range(1, M):
        if mu[j]:
            for i in range(j, L + 1, j):
                source[i] += mu[j]
    area = prefix = 0
    required = F(0)
    at = 0
    for k in range(1, L + 1):
        area += prefix
        prefix += source[k]
        raw = area + terminal * ramp(M, k) - (k - 1)
        if k <= M:
            assert raw == 0
            continue
        pair = ramp(M, k) - 2 * ramp(2 * M, k)
        assert pair > 0
        if -raw > required * pair:
            required, at = -raw / pair, k
    l1 = sum(abs(mu[j]) * j for j in range(1, M)) + abs(terminal) * M
    last = (2 + sum(mu[1:M]) + terminal + l1 / (4 * (L + 1))) / (1 - F(5 * M, 4 * (L + 1)))
    required = max(required, last, 0)
    guard = F(-(-required.numerator * 1024 // required.denominator), 1024)
    coeffs = [F(x) for x in mu[1:M]] + [terminal + guard] + [F(0)] * (M - 1) + [-2 * guard]
    assert sum(a / j for j, a in enumerate(coeffs, 1)) == 0
    low, hi, cost = arithmetic_price(coeffs)
    return {
        "initial_exact_through": M,
        "support_through": 2 * M,
        "tail_from": L + 1,
        "repair_weight": str(guard),
        "worst_direct_address": at,
        "excess": enclosure(low, hi),
        "cost": enclosure(cost, cost),
        "cost_times_excess": enclosure(cost * low, cost * hi),
    }


def audit():
    source = Path(__file__).with_name("growing_divisor_rows.json")
    rows = json.loads(source.read_bytes())["rows"]
    refit = next(row for row in rows if row["support"] == 64)
    changed = {
        j: [
            str(F(j * UP[j - 1], 102)),
            str(F(j * refit["coefficients"][j - 1], refit["denominator"])),
        ]
        for j in (5, 8, 13)
    }
    assert changed == {
        5: ["-50/51", "-1048575/1048576"],
        8: ["4/51", "0"],
        13: ["0", "-262145/262144"],
    }
    old = frozen()
    results = []
    for row in rows:
        low, hi, cost = check_upper(row)
        results.append(
            {
                "available_labels": row["support"],
                "direct_through": row["direct_through"],
                "excess": enclosure(low, hi),
                "cost": enclosure(cost, cost),
                "cost_times_excess": enclosure(cost * low, cost * hi),
                "below_old_frozen_part": hi < old,
            }
        )
    assert [x["available_labels"] for x in results if x["below_old_frozen_part"]] == [64, 128, 256]
    return {
        "optimized": results,
        "individual_revisions_at_64_labels": changed,
        "fixed_first_16_exact_surplus": str(old),
        "fixed_first_16_surplus": enclosure(old, old),
        "initially_exact_then_repaired": [single_repair(M) for M in (16, 32, 64, 128, 256, 512)],
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
