"""Rank two Pascal subset families, then price the prime dials their integer factors can carry."""

from itertools import combinations, permutations, product
from math import comb, factorial, gcd, isqrt, prod
import json

from check_pal_prime_board import permutation_rank, permutation_unrank
from check_pal_dyson_window import SCALE, ZERO, interval_text, plus, natural, log_int, prime_data


def subset_rank(subset):
    return sum(comb(v, i + 1) for i, v in enumerate(subset))


def subset_unrank(n, a, rank):
    if not 0 <= rank < comb(n, a):
        raise ValueError("subset rank outside its row")
    upper = n
    values = []
    for i in reversed(range(1, a + 1)):
        j = upper - 1
        while comb(j, i) > rank:
            j -= 1
        values.append(j)
        rank -= comb(j, i)
        upper = j
    return tuple(reversed(values))


def encode(n, orders, families):
    if len(orders) != n or len(families) != 2:
        raise ValueError("expected n row orders and two subset families")
    rank = 0
    for row in orders:
        if sorted(row) != list(range(n)):
            raise ValueError("expected a permutation")
        rank = rank * factorial(n) + permutation_rank(row)
    for family in families:
        if len(family) != n + 1:
            raise ValueError("one subset of each size is required")
        for a, subset in enumerate(family):
            if (
                list(subset) != sorted(set(subset))
                or len(subset) != a
                or any(not 0 <= x < n for x in subset)
            ):
                raise ValueError("invalid subset")
            rank = rank * comb(n, a) + subset_rank(subset)
    cells = []
    for _ in range(n * n):
        rank, digit = divmod(rank, n)
        cells.append(digit)
    if rank:
        raise ValueError("board overflow")
    return tuple(reversed(cells))


def decode(n, cells):
    if len(cells) != n * n or any(not 0 <= c < n for c in cells):
        raise ValueError("invalid board")
    rank = 0
    for digit in cells:
        rank = rank * n + digit
    families = []
    for _ in range(2):
        family = []
        for a in reversed(range(n + 1)):
            rank, digit = divmod(rank, comb(n, a))
            family.append(subset_unrank(n, a, digit))
        families.append(tuple(reversed(family)))
    orders = []
    for _ in range(n):
        rank, r = divmod(rank, factorial(n))
        orders.append(permutation_unrank(n, r))
    if rank:
        raise ValueError("unused board")
    return tuple(reversed(orders)), tuple(reversed(families))


def small_boards():
    rows = []
    for n in (1, 2, 3):
        states = set()
        families = list(product(*(list(combinations(range(n), a)) for a in range(n + 1))))
        for orders in product(permutations(range(n)), repeat=n):
            for packs in product(families, repeat=2):
                cells = encode(n, orders, packs)
                assert cells not in states and decode(n, cells) == (orders, packs)
                states.add(cells)
        paid = factorial(n) ** n * prod(comb(n, a) for a in range(n + 1)) ** 2
        assert len(states) == paid <= n ** (n * n)
        rows.append({"n": n, "distinct_inputs_recovered": paid, "all_board_states": n ** (n * n)})
    return rows


def direct(n):
    primes, _ = prime_data(n)
    every_subset = prod(comb(n, a) for a in range(n + 1))
    needed = prod(p ** (n - p) for p in range(isqrt(n) + 1, n + 1) if primes[p])
    common = gcd(every_subset, needed)
    missing = needed // common
    free = every_subset // common
    assert gcd(missing, free) == 1

    def valuation(p):
        v = every_subset
        count = 0
        while v % p == 0:
            count += 1
            v //= p
        return count

    rows = []
    for p in range(isqrt(n) + 1, n + 1):
        if not primes[p]:
            continue
        groups, r = divmod(n, p)
        carrying = [a for a in range(n + 1) if a % p > r]
        actual = [a for a in range(n + 1) if comb(n, a) % p == 0]
        assert actual == carrying and valuation(p) == len(carrying) == groups * (p - 1 - r)
        rows.append([p, n - p, len(carrying)])
    return {
        "n": n,
        "one_direction_unpaid": str(missing),
        "unused_subset_capacity": str(free),
        "unused_and_unpaid_are_coprime": True,
        "prime_digit_rows": rows if n == 16 else [],
        "extra_whole_bits_after_two_full_pascal_families": (
            n ** (n * n) // (factorial(n) ** n * every_subset**2)
        ).bit_length()
        - 1,
    }


def fraction_price(cut=10000):
    # The omitted tail is bounded by half the integral of t^(-4) from cut to infinity.
    floor_sum = 0
    for q in range(1, cut + 1):
        floor_sum += SCALE // (2 * q * q * (q * q + q + 1))
    lo = floor_sum
    hi = floor_sum + cut - (-SCALE // (6 * cut**3))
    return {
        "unpaid_log_cost_per_n_squared": interval_text((lo, hi), 10),
        "fraction_of_large_prime_payload_paid_before_exchange": interval_text(
            (SCALE - 2 * hi, SCALE - 2 * lo), 10
        ),
    }


def prime_prices(n):
    flags, _ = prime_data(n)
    roots = isqrt(n)
    needed = matched = unused = unpaid = ZERO
    by_q = {q: ZERO for q in (1, 2, 3, 4, 5, 10, 20)}
    for p in range(roots + 1, n + 1):
        if not flags[p]:
            continue
        q, r = divmod(n, p)
        present = q * (p - 1 - r)
        ordinary = n - p
        lp = log_int(p)
        needed = plus(needed, natural(ordinary, lp))
        matched = plus(matched, natural(min(ordinary, present), lp))
        unused = plus(unused, natural(max(0, present - ordinary), lp))
        unpaid = plus(unpaid, natural(max(0, ordinary - present), lp))
        if q in by_q:
            delta = present - ordinary
            entry = natural(delta, lp) if delta >= 0 else (delta * lp[1], delta * lp[0])
            by_q[q] = plus(by_q[q], entry)

    def normalized(v):
        return interval_text((v[0] // (n * n), -(-v[1] // (n * n))), 8)

    return {
        "n": n,
        "one_way_needed_per_n_squared": normalized(needed),
        "matched_per_n_squared": normalized(matched),
        "unpaid_per_n_squared": normalized(unpaid),
        "unused_large_factors_per_n_squared": normalized(unused),
        "net_surplus_per_n_squared_by_quotient": {q: normalized(x) for q, x in by_q.items()},
    }


def row_mixture_control():
    from fractions import Fraction as Q

    mobius = {1: 1}
    for k in range(2, 7):
        mobius[k] = -sum(value for d, value in mobius.items() if k % d == 0)

    def recovered_tail(d):
        return sum(value * (Q(d * d, k) - k) / 2 for k, value in mobius.items() if k <= d)

    assert sum(Q(mobius[k], k) for k in range(1, 6)) == -Q(1, 30)
    low, high = recovered_tail(6), recovered_tail(5)
    assert (low, high) == (Q(39, 10), Q(49, 12))
    a, b = Q(1, 6), Q(1, 5)
    middle = (a + b) / 2
    weighted_tent = (b - a) / (2 * a * b * middle)
    target_observation = -weighted_tent / 30
    dual_bound = (60 / a + 2 / a**2) * sum(Q(abs(v), k) for k, v in mobius.items())
    assert target_observation == -Q(1, 11) and dual_bound < 1000
    assert 2 * abs(target_observation) / dual_bound > Q(1, 5500)

    # Check the inversion against known positive inventories, including boundary atoms.
    scales = [(Q(1, 6), Q(2)), (Q(1, 5), Q(3, 2)), (Q(3, 5), Q(7, 4)), (Q(1), Q(5))]

    def reading(t):
        return sum(
            w * (t * j * (j + 1) - length * j) for length, w in scales for j in [length // t]
        )

    for y in [a, middle, b, Q(1, 4), Q(1, 2), Q(1)]:
        recovered = sum(mobius[k] * reading(k * y) for k in range(1, int(1 / y) + 1))
        direct = sum(w * (2 * y - length) for length, w in scales if length >= y)
        integral = sum(w * (y * length - y * y) for length, w in scales if length >= y)
        assert recovered == direct
        assert recovered / y + integral / y**2 == sum(w for length, w in scales if length >= y)
    return {
        "mobius_on_first_six": list(mobius.values()),
        "target_inventory_at_one_sixth": str(low),
        "target_inventory_at_one_fifth": str(high),
        "change_required_when_cut_rises": str(high - low),
        "target_tent_observation": str(target_observation),
        "upper_bound_on_dual_weight": str(dual_bound),
        "normalized_excess_cost_lower_bound": "1/5500",
    }


def audit():
    controls = [direct(n) for n in (3, 4, 16, 49, 81)]
    assert next(a for a in controls if a["n"] == 16)["one_direction_unpaid"] == "175"
    return {
        "decoder": small_boards(),
        "nonnegative_row_inventory": row_mixture_control(),
        "factor_controls": controls,
        "limiting_price": fraction_price(),
        "prime_readings": [prime_prices(n) for n in (256, 2663, 100000, 1000000, 10000000)],
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
