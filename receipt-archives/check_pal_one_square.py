"""Replay the proper-divisor return on both sides of one square, including 17."""

import json
from fractions import Fraction as F
from math import comb, gcd, isqrt

from check_pal_adjacent_squares import common
from check_pal_dense_square_payment import display, sub
from check_pal_doubled_ruler import extra, three_halves
from check_pal_dyson_window import SCALE, log_int, prime_data
from check_pal_rise_direction import add, box, mul, sqrt_box
from check_pal_square_holes import log_box, sixth_prefix
from check_pal_two_square_range import window


def center(k):
    first = (k * k + 20) // 21
    j = next(j for j in range(first, first + 3) if gcd(j, 85) == 1)
    return 21 * j


def inward(k, b, cut):
    n = k**4
    return {
        b * b - t * t
        for t in range(1, b - 1)
        if 2 * n < cut * (b * b - t * t) and b * b - t * t <= n
    }


def outward(k, b, primes):
    n = k**4
    return {
        d
        for t in range(1, k * k + 1)
        if n < (d := b * b + t * t) <= 2 * n
        and any(1 < p < d and d % p == 0 for p in primes)
    }


def phase_integral(coef, left, right):
    def at(sq):
        return mul(
            sqrt_box(sq), box(sum(v * sq**i / (2 * i + 1) for i, v in enumerate(coef)))
        )

    return sub(at(right), at(left))


def constants():
    price = box(0)
    for m in (2, 3, 4):
        row = [F(0) for _ in range(7)]
        row[1] = -1
        for j in range(1, m + 1):
            a = F(j, 2)
            for i in range(6):
                power = 2 * comb(5, i) * (1 - a) ** (5 - i) * a**i
                row[i] += power * (7 * a - 1)
                row[i + 1] -= power * 7 * a
        price = add(price, phase_integral(row, 1 - F(2, m), 1 - F(2, m + 1)))
    closed = add(
        add(
            mul(box(F(-26496629, 15640625)), sqrt_box(15)),
            mul(box(F(640, 9009)), sqrt_box(3)),
        ),
        mul(box(F(4608, 1001)), sqrt_box(2)),
    )
    assert max(closed[0], price[0]) < min(closed[1], price[1])
    exterior = sum(
        F(comb(5, i) * (-1) ** i, 32) * (F(5, 2 * i + 1) + F(7, 2 * i + 3))
        for i in range(6)
    )
    assert exterior == F(64, 1001)
    missed = F(1, 2) * F(2, 3) * F(3, 5) * F(6, 7)
    assert missed == F(6, 35) and 1 - missed * F(15, 17) == F(101, 119)
    four = add(price, box((1 - missed) * exterior))
    five = add(price, box(F(101, 119) * exterior))
    diff = F(12, 595) * exterior
    assert five[0] - four[0] == diff
    # This is the specific sufficient budget, not a lower bound on the true RH price.
    allowance = F(4621, 100000) + F(1, 24) + F(2, 3) * (three_halves(96) - 1)
    assert four[1] < allowance < five[0]
    return {
        "inner": display(price, 10),
        "all_outward": str(exterior),
        "four_prices": display(four, 10),
        "five_prices": display(five, 10),
        "gain_from_seventeen": str(diff),
        "sufficient_RH_price_upper": display(box(allowance), 10),
    }


def directed_test(k, b, cut, primes, logs):
    n = k**4
    N = 2 * n
    inner = inward(k, b, cut)
    outer = outward(k, b, primes)
    holes = inner | outer
    assert not inner & outer
    assert all(1 < d <= N and d not in logs for d in holes)
    credit = sum(extra(n, d) for d in holes)
    bill = max(0, sixth_prefix(N) - 16 * n**7 - credit)
    lo = hi = 0
    for p, (a, c) in logs.items():
        if p > N:
            break
        if p**8 > n**7:
            w = extra(n, p)
            lo += a * w
            hi += c * w
    tick = sub(log_box(n + 1), log_box(n))
    cost = mul(box(n * bill), tick)
    margin = mul(box(F(1, N**5 * k**6)), sub((F(lo, SCALE), F(hi, SCALE)), cost))
    assert margin[0] > 0 or margin[1] < 0
    return {
        "k": k,
        "center": b,
        "cut_denominator": cut,
        "proper_divisors": list(primes),
        "inner_positions": len(inner),
        "outer_positions": len(outer),
        "normalized_margin": display(margin, 10),
        "paid": margin[0] > 0,
    }


def arithmetic():
    gap = 2 * 1933**2 + 1
    assert gap == 3**8 * 17 * 67 and (9 * 2 * 2) // 2 - 1 == 17
    for k in range(2, 1934):
        factors = [
            r
            for r in range(3, isqrt(2 * k * k + 1) + 1, 2)
            if (2 * k * k + 1) % r == 0 and r * r < 2 * k * k + 1
        ]
        assert (len(factors) == 17) == (k == 1933)
    b = 1933**2
    hits = list(common(b))
    for r, v, t, u, d in hits:
        assert 4 * d == (r * r - 1) * (v * v - 1)
        e = b * b + u * u
        assert e == (b + 1) ** 2 + t * t and 4 * e == (r * r + 1) * (v * v + 1)
    first_17 = {"k": 1933, "gap": gap, "smaller_factors": [r for r, _, _, _, _ in hits]}
    assert list(common(25)) == [(3, 17, 7, 10, 576)] and not list(common(144))
    assert [i for i in range(17) if (2 * i * i + 1) % 17 == 0] == [5, 12]
    board8 = sorted(outward(8, 64, (17,)))
    assert board8 == [4097, 4352, 4420, 5185, 5321, 6596, 6800] and not outward(
        2, 4, (17,)
    )
    assert extra(16, 17) == 66065625
    for m in range(85):
        j = next(j for j in range(m, m + 3) if gcd(j, 85) == 1)
        assert m <= j <= m + 2
    flags, _ = prime_data(2 * 27**4)
    logs = {p: log_int(p) for p in range(2, len(flags)) if flags[p]}
    eight = [directed_test(8, 64, 3, S, logs) for S in ((), (17,))]
    assert [x["paid"] for x in eight] == [False, True]
    shifted = [
        directed_test(k, center(k), 5, (2, 3, 5, 7, 17), logs)
        for k in (2, 3, 4, 5, 8, 12, 17, 21, 27)
    ]
    for row in shifted:
        k, b = row["k"], row["center"]
        assert k * k <= b <= k * k + 62 and b % 21 == 0 and gcd(b, 85) == 1
    early = [directed_test(k, k * k, 5, (2, 3, 5, 7, 17), logs) for k in range(2, 28)]
    assert all(row["paid"] for row in early)
    k0 = 2**17
    costs = window(k0, 2**120)
    loss = F(5 * (3572 + 12 * k0), 32 * k0**2) + F(124, k0**2) + F(3844, k0**4)
    available = F(constants()["five_prices"][0]) - loss
    upper = F(costs["combined_cost_upper"])
    assert upper < available
    return {
        "all_unshifted_small_indices": [2, 27],
        "least_unshifted_small_margin": min(
            early, key=lambda r: F(r["normalized_margin"][0])
        ),
        "uniform_index_interval": [k0, 2**30],
        "finite_refund_lower": display(box(available), 10)[0],
        "finite_price_upper": costs["combined_cost_upper"],
        "first_seventeen_overlaps": first_17,
        "board_eight_new_slots": board8,
        "board_eight_seventeen_flip": eight,
        "moved_center_examples": shifted,
        "constants": constants(),
    }


if __name__ == "__main__":
    print(json.dumps(arithmetic(), indent=2))
