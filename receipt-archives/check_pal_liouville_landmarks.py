"""Independent quotient-recursion checks on the Pólya crossing and square-switch prices."""

import json
from fractions import Fraction
from functools import lru_cache
from itertools import accumulate
from math import isqrt, prod

from check_pal_dyson_window import prime_data
from check_pal_growing_brackets import enclosure, mobius


def prefix_oracle(base=200000):
    mu = mobius(base)
    original = [0] * (base + 1)
    for a in range(1, isqrt(base) + 1):
        square = a * a
        for d in range(1, base // square + 1):
            if mu[d]:
                assert original[square * d] == 0
                original[square * d] = mu[d]
    assert all(abs(v) == 1 for v in original[1:])
    early = list(accumulate(original))

    @lru_cache(maxsize=None)
    def value(n):
        if n <= base:
            return early[n]
        # Summing (1 * lambda)(m) = [m is a square] over 1..n.
        result = isqrt(n)
        left = 2
        while left <= n:
            q = n // left
            last = n // q
            result -= (last - left + 1) * value(q)
            left = last + 1
        return result

    return value


def single_change(n, p, value):
    delta = 0
    q = n // (p * p)
    coefficient = -2
    while q:
        delta += coefficient * value(q)
        coefficient = -coefficient
        q //= p * p
    return delta


def smooth_products(primes, limit):
    """(product, 2^omega(product)) with all prime factors in the given tuple."""
    if not primes:
        yield 1, 1
        return
    p, *rest = primes
    for a, w in smooth_products(rest, limit):
        yield a, w
        a *= p
        while a <= limit:
            yield a, 2 * w
            a *= p


def audit():
    original = prefix_oracle()
    first, peak = 906150257, 906316571
    flags, _ = prime_data(isqrt(2_000_000_000))
    primes = [p for p in range(2, len(flags)) if flags[p]]
    chosen = [p for p in primes if p * p > 500_000_000][:415]
    assert len(chosen) == 415 and chosen[-1] ** 2 < first
    landmarks = {}
    for n in [48432, 48433, first - 1, first, 906180359, peak, 10**9, 2 * 10**9]:
        v = original(n)
        corrected = v - 2 * sum(original(n // (p * p)) for p in chosen)
        landmarks[str(n)] = [v, v + single_change(n, 17, original), corrected]
    assert landmarks[str(first - 1)][0] == 0 and landmarks[str(first)][0] == 1
    assert landmarks[str(peak)] == [829, 3491, -1]
    assert landmarks[str(10**9)] == [-25216, -21002, -26046]
    assert landmarks[str(2 * 10**9)] == [-23088, -20930, -22408]
    choices = [(original(peak) + single_change(peak, p, original), p) for p in primes]
    price = min(v for v, _ in choices)
    best = [p for v, p in choices if v == price]
    assert 174**4 > peak
    upper = isqrt(peak)
    lower = isqrt(peak // 2)
    cap4 = sum(w for a, w in smooth_products([2, 3, 5, 7], upper) if a > lower)
    cap_other_four = 2 * sum(w for _, w in smooth_products([3, 5, 11], upper))
    assert (cap4, cap_other_four) == (404, 718)
    infinite_ratio = prod(Fraction(p - 1, p + 1) for p in chosen)
    return {
        "critical_reciprocal_product": enclosure(infinite_ratio, infinite_ratio),
        "four_smallest_capacity": cap4,
        "all_other_four_capacity_upper": cap_other_four,
        "prime_switches": len(chosen),
        "first_prime": chosen[0],
        "last_prime": chosen[-1],
        "first_square": chosen[0] ** 2,
        "last_square": chosen[-1] ** 2,
        "landmark_columns": [
            "ordinary",
            "only_17_negative",
            "415_fixed_large_switches",
        ],
        "landmarks": landmarks,
        "single_flip_minimum_at_ordinary_peak": price,
        "single_flip_minimizers_count": len(best),
        "least_minimizing_prime": min(best),
        "oracle": "sum_(m<=x) L(floor(x/m))=floor(sqrt(x)), with an independent squarefree initialization",
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
