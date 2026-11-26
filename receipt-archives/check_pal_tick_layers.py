"""Count genuine tick triples and recover both kinds of shared Pascal data."""

from bisect import bisect_right
from functools import lru_cache
from itertools import product
from math import comb, factorial, gcd, isqrt, prod
import json

from check_pal_dyson_window import log_int, minus, prime_data
from check_pal_pascal_board import subset_rank, subset_unrank
from pal_tick_codec import TickCube, pack_trip, unpack_trip, ceil_div


@lru_cache(maxsize=200000)
def log_number(n):
    return log_int(n)


def exact_ticks(p, numerator, denominator):
    def sufficient(t):
        return numerator**t >= p * denominator**t

    lo, hi = 0, 1
    while not sufficient(hi):
        hi *= 2
    if p <= 1:
        return 0
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if sufficient(mid):
            hi = mid
        else:
            lo = mid
    return hi


def tick_count(p, numerator, denominator, step):
    height = log_number(p)
    lo = ceil_div(height[0], step[1])
    hi = ceil_div(height[1], step[0])
    if lo == hi:
        return lo
    return exact_ticks(p, numerator, denominator)


def heads():
    roots = [1, 2, 3, 4, 6, 8, 10, 12, 16, 20, 24, 32, 40, 48, 64]
    maxn = roots[-1] ** 4
    flags, _ = prime_data(maxn)
    primes = [i for i in range(2, maxn + 1) if flags[i]]
    data = []
    for k in roots:
        n = k**4
        x = k * k
        selectors = primes[bisect_right(primes, x) : bisect_right(primes, n)]
        if n <= 4096:
            marker = factorial(x)
            assert selectors == [p for p in range(2, n + 1) if gcd(p, marker) == 1]
        result = {"k": k, "n": n, "square_root": x}
        for name, top, bot in (
            ("ordinary", x + 1, x),
            ("shifted_five_sixths", 6 * x + 11, 6 * x + 5),
        ):
            step = minus(log_number(top), log_number(bot))
            total = 0
            samples = []
            for p in selectors:
                height = tick_count(p, top, bot, step)
                total += (n - p) * height
                if n <= 81:
                    assert height == exact_ticks(p, top, bot)
                    samples.append([p, n - p, height])
            required = ceil_div(2 * total, n * n)
            result[name] = {
                "oriented_triples": 2 * total,
                "layers_required": required,
                "whole_layers_spared": x - required,
            }
            if samples:
                result[name]["individual_prime_costs"] = samples
        data.append(result)
    return data


def owner_control(reserved=0):
    k = 8
    n = k**4
    x = k * k
    b = n.bit_length()
    h = x - reserved
    blocks = b if reserved == 0 else b + 1
    assert reserved == 0 or 2 * b + 2 <= x
    flags, _ = prime_data(n)
    primes = [p for p in range(2, n + 1) if flags[p]]
    interior = [p for p in primes if p > x and 4 * blocks * p <= n]
    occupied = {}
    records = 0
    for p in interior:
        height = exact_ticks(p, x + 1, x)
        for block in range(ceil_div(height, h)):
            for side, starts in enumerate((min((n + 1) // 2, n - p), max(0, n - p - (n + 1) // 2))):
                lanes = min(h, height - block * h)
                if starts <= 0 or lanes <= 0:
                    continue
                distance = (2 * block + side + 1) * p
                assert distance not in occupied and distance <= n // 2 and starts - 1 + distance < n
                occupied[distance] = [p, starts, lanes]
                records += starts * lanes
                for i in (side * ((n + 1) // 2), side * ((n + 1) // 2) + starts - 1):
                    for t in (block * h, block * h + lanes - 1):
                        stored = pack_trip(n, h, p, i, t)
                        assert unpack_trip(n, h, stored, primes) == (p, i, t)
    assert records == sum((n - p) * exact_ticks(p, x + 1, x) for p in interior)
    example = pack_trip(n, h, 67, 4028, 270)
    assert unpack_trip(n, h, example, primes) == (67, 4028, 270)
    return {
        "k": k,
        "storage_layers": h,
        "all_middle_primes": interior,
        "first_half_distances_owned": len(occupied),
        "distinct_oriented_records_recovered": 2 * records,
        "example": {
            "input": [67, 4028, 270],
            "stored": example,
            "recovered": unpack_trip(n, h, example, primes),
        },
    }


def row_count(n):
    return prod(comb(n, a) for a in range(n + 1))


def row_at(n, rank):
    parts = []
    for a in reversed(range(n + 1)):
        rank, j = divmod(rank, comb(n, a))
        parts.append(subset_unrank(n, a, j))
    assert rank == 0
    return tuple(reversed(parts))


def read_row(n, row):
    rank = 0
    for a, part in enumerate(row):
        rank = rank * comb(n, a) + subset_rank(part)
    return rank


def base_digits(rank, radix, length):
    result = []
    for _ in range(length):
        rank, j = divmod(rank, radix)
        result.append(j)
    assert rank == 0
    return result


def from_digits(digits, radix):
    result = 0
    for d in reversed(digits):
        result = radix * result + d
    return result


def weld_five(common, payload):
    halves = [divmod(read_row(4, row), 32) for row in common]
    bits = base_digits(halves[0][1], 2, 5) + base_digits(halves[1][1], 2, 5)
    two = [row_at(2, d) for d in bits[:4]]
    three = row_at(3, halves[0][0] + 3 * halves[1][0])
    five = []
    for j in range(3):
        base = from_digits(bits[4 + 2 * j : 6 + 2 * j], 2)
        digits = from_digits(payload[4 * j : 4 * j + 4], 5)
        five.append(row_at(5, base + 4 * digits))
    return two, three, five


def split_five(records):
    two, three, five = records
    bits = [read_row(2, row) for row in two]
    ternary = base_digits(read_row(3, three), 3, 2)
    payload = []
    for row in five:
        digits, base = divmod(read_row(5, row), 4)
        bits += base_digits(base, 2, 2)
        payload += base_digits(digits, 5, 4)
    common = tuple(
        row_at(4, 32 * ternary[j] + from_digits(bits[5 * j : 5 * j + 5], 2)) for j in range(2)
    )
    return common, tuple(payload)


def five_control():
    left = row_count(2) ** 4 * row_count(3) * row_count(5) ** 3
    right = row_count(4) ** 2 * 5**12
    assert left == right
    payloads = [(0,) * 12, (4,) * 12, tuple(j % 5 for j in range(12))]
    tested = 0
    for a, b in product(range(96), repeat=2):
        common = row_at(4, a), row_at(4, b)
        for payload in payloads:
            assert split_five(weld_five(common, payload)) == (common, payload)
            tested += 1
    return {
        "identical_state_counts": str(left),
        "common_four_row_pairs": 96**2,
        "remaining_independent_five_settings": 5**12,
        "decoded_controls": tested,
    }


def crossing(n, flags):
    total = sum(n - p for p in range(isqrt(n) + 1, n + 1) if flags[p])
    h = total
    first = None
    for j in range(2, n + 1):
        room = (j - 1) * (n + 1 - j)
        if h <= room:
            if first is None:
                first = j
        else:
            assert first is None
        if flags[j] and j > isqrt(n):
            h -= n - j
    return {
        "n": n,
        "first_primitive_height_that_fits": first,
        "forward_records_before_weighting": total,
    }


def complete_cube_control():
    controls = []
    for k, layers, exhaustive in ((2, 3, True), (3, 7, True), (8, 62, False)):
        n = k**4
        x = k * k
        flags, _ = prime_data(n)
        primes = [p for p in range(x + 1, n + 1) if flags[p]]
        step = minus(log_number(x + 1), log_number(x))
        prices = {p: tick_count(p, x + 1, x, step) for p in primes}
        cube = TickCube(n, layers, prices)
        visited = set()
        for p in primes:
            if p == n:
                continue
            starts = range(n - p) if exhaustive else sorted({0, (n - p) // 2, n - p - 1})
            ticks = range(prices[p]) if exhaustive else sorted({0, prices[p] // 2, prices[p] - 1})
            for i, t, direction in product(starts, ticks, (0, 1)):
                record = p, i, t, direction
                cell = cube.encode(*record)
                assert cell not in visited and cube.decode(*cell) == record
                visited.add(cell)
        if exhaustive:
            assert len(visited) == cube.count
        controls.append(
            {
                "k": k,
                "n": n,
                "layers": layers,
                "all_oriented_records": cube.count,
                "capacity": n * n * layers,
                "middle_reserved": cube.middle_records,
                "exterior_placed_afterwards": cube.outer_records,
                "unused_cells": n * n * layers - cube.count,
                "tested_roundtrips": len(visited),
                "exhaustive_roundtrips": exhaustive,
            }
        )
    try:
        TickCube(16, 2, {5: 8, 7: 9, 11: 11, 13: 12})
    except ValueError as error:
        assert "exceed the remaining" in str(error)
    else:
        raise AssertionError("two layers should be too few at sixteen")
    return controls


def finite_signed_rows(n):
    from fractions import Fraction as Q
    from math import lcm

    mu = [0] * (n + 1)
    mu[1] = 1
    for d in range(1, n + 1):
        for multiple in range(2 * d, n + 1, d):
            mu[multiple] -= mu[d]
    # Recover the exact ramp of prime-power weights at every original integer label d>=2.
    h = [0] + [sum(mu[r] * (n - r * k) for r in range(1, n // k + 1)) for k in range(1, n + 1)]
    tail = [Q(0)] * (n + 2)
    suffix = 0
    for k in range(n, 1, -1):
        tail[k] = Q(k * h[k] + suffix, k * (k - 1))
        suffix += h[k]
    change = [tail[k] - tail[k + 1] for k in range(n + 1)]
    for d in range(2, n + 1):
        exact = sum(change[m] * (m // d) * (d - 1 - m % d) for m in range(d, n + 1))
        assert exact == n - d
    period = lcm(*range(1, n + 1))
    assert all((period * entry).denominator == 1 for entry in change[2:])
    flags, _ = prime_data(n)
    for p in range(2, n + 1):
        if not flags[p]:
            continue
        positive = negative = expected = 0
        power = p
        while power <= n:
            expected += period * (n - power)
            for m in range(power, n + 1):
                weighted = int(period * change[m]) * (m // power) * (power - 1 - m % power)
                positive += max(0, weighted)
                negative += max(0, -weighted)
            power *= p
        assert positive - negative == expected
    return {k: str(change[k]) for k in range(2, n + 1) if change[k] < 0}


def finite_inverse_control():
    first = None
    for n in range(2, 62):
        negative = finite_signed_rows(n)
        if negative and first is None:
            first = (n, negative)
    assert first == (61, {11: "-1/330"})
    negative81 = finite_signed_rows(81)
    assert negative81 == {14: "-29/1365", 15: "-29/1680"}
    return {
        "first_negative_row_on_full_integer_profile": first,
        "first_quartic_with_negative_row": {"n": 81, "signed_rows": negative81},
        "scope": "Exact recovery of f(d)=n-d on all integer labels d>=2; a stricter requirement than reading only prime-power labels.",
    }


def sharp_chart_control(space, jobs, holes):
    """Place the exact unavoidable disagreements in one hole; verify every interval image."""
    if len(holes) != 3 or any(finish < start for start, finish in holes):
        raise ValueError("three intervals required")
    if any(holes[i][1] > holes[i + 1][0] for i in range(2)):
        raise ValueError("the omitted intervals must be disjoint in job order")
    excess = max(0, jobs - space)
    if any(finish - start < excess for start, finish in holes):
        raise ValueError("some chart is too small")
    left = holes[0][0]

    def common(j):
        if j < left:
            return j
        if j >= left + excess:
            return j - excess
        raise ValueError("record needs a local slot")

    def slot(chart, j):
        lo, hi = holes[chart]
        if lo <= j < hi:
            return None
        if left <= j < left + excess:
            return common(lo + j - left)
        return common(j)

    cuts = sorted(set([0, jobs, left + excess] + [x for bounds in holes for x in bounds]))
    ranges = [pair for pair in zip(cuts, cuts[1:]) if pair[0] < pair[1]]
    disagreement = 0
    for a, b in ranges:
        readings = {slot(c, a) for c in range(3)} - {None}
        if len(readings) > 1:
            disagreement += b - a
    assert disagreement == excess
    for chart in range(3):
        image = []
        for a, b in ranges:
            inside = slot(chart, a)
            if inside is None:
                continue
            end = slot(chart, b - 1) + 1
            assert end - inside == b - a and 0 <= inside < end <= space
            image.append((inside, end))
        image.sort()
        assert all(a[1] <= b[0] for a, b in zip(image, image[1:]))
        assert sum(b - a for a, b in image) == jobs - (holes[chart][1] - holes[chart][0])
    return {
        "jobs": jobs,
        "available_slots": space,
        "least_disagreements": disagreement,
        "records_removed_in_each_chart": [b - a for a, b in holes],
        "exact_pieces_in_order": len(ranges),
    }


def three_views():
    from itertools import permutations

    toy = sharp_chart_control(3, 4, [(0, 1), (1, 2), (2, 3)])
    minima = []
    rules = [tuple(j for j in range(4) if j != i) for i in range(3)]
    for trial in product(list(permutations(range(3))), repeat=3):
        views = [dict(zip(keys, assignments)) for keys, assignments in zip(rules, trial)]
        minima.append(sum(len({v[j] for v in views if j in v}) > 1 for j in range(4)))
    assert min(minima) == toy["least_disagreements"] == 1
    actual = []
    for k in (8, 10):
        n = k**4
        x = k * k
        h = x - 2
        b = n.bit_length()
        flags, _ = prime_data(n)
        primes = [p for p in range(x + 1, n + 1) if flags[p]]
        top, bot = 6 * x + 11, 6 * x + 5
        step = minus(log_number(top), log_number(bot))
        prices = {p: tick_count(p, top, bot, step) for p in primes}
        middle = [p for p in primes if 4 * (b + 1) * p <= n]
        base = TickCube(n, h, {p: prices[p] for p in middle})
        outer = [p for p in primes if p not in base.owners]
        offsets = [0]
        for p in outer:
            offsets.append(offsets[-1] + 2 * (n - p) * prices[p])
        width = ceil_div(12 * n, b**3)
        locations = [(a * n // 4, a * n // 4 + width) for a in (1, 2, 3)]
        holes = [
            (offsets[bisect_right(outer, lo)], offsets[bisect_right(outer, hi)])
            for lo, hi in locations
        ]
        result = sharp_chart_control(base.free_offsets[-1], offsets[-1], holes)
        result.update(
            {
                "k": k,
                "n": n,
                "fixed_middle_jobs": base.middle_records,
                "full_job_count": offsets[-1] + base.middle_records,
                "full_capacity": n * n * h,
                "omitted_prime_intervals_open_closed": locations,
            }
        )
        actual.append(result)
    assert [r["least_disagreements"] for r in actual] == [0, 859664]
    return {"small_toy": toy, "all_toy_assignments_compared": len(minima), "shifted_actual": actual}


def audit():
    flags, _ = prime_data(100000)
    for n in range(2, 513):
        crossing(n, flags)
    return {
        "tick_layers": heads(),
        "owned_routes": owner_control(),
        "full_cube_placements": complete_cube_control(),
        "owned_routes_with_two_layers_set_aside": owner_control(2),
        "twelve_fives": five_control(),
        "agreement_of_three_views": three_views(),
        "finite_signed_reconstruction": finite_inverse_control(),
        "contiguous_gap": [crossing(n, flags) for n in (16, 61, 81, 256, 577, 2663, 10000, 100000)],
        "all_crossings_checked_through": 512,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
