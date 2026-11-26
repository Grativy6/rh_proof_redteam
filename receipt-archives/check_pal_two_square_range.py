"""Pay the two-square reference at every positive quartic head with k^4 <= 2^142."""

import json
from bisect import bisect_right
from fractions import Fraction as F
from math import isqrt

from check_pal_adjacent_squares import fast
from check_pal_crossing_refund import (
    HEIGHT,
    HIGH_FACTOR,
    ORDINATE_MASS,
    SHORT_PASSES,
    SHORT_WIDTH,
)
from check_pal_doubled_ruler import extra, margin_text, three_halves
from check_pal_dyson_window import SCALE, log_int, prime_data
from check_pal_square_holes import contact_price


def small_payments():
    cap = 2 * 24**4
    flags, _ = prime_data(cap)
    primes = [p for p in range(2, cap + 1) if flags[p]]
    logs = [log_int(p)[0] for p in primes]
    margins = []
    for k in range(2, 25):
        n = k**4
        N = 2 * n
        _, _, bill, _ = fast(k * k)
        income = sum(
            extra(n, p) * logs[i]
            for i, p in enumerate(primes[: bisect_right(primes, N)])
            if p**8 > n**7
        )
        cost = n * bill * (log_int(n + 1)[1] - log_int(n)[0])
        margin = F(income - cost, SCALE * N**5 * k**6)
        assert margin > 0
        margins.append((margin, k))
    bound, k = min(margins)
    return {
        "index_interval": [2, 24],
        "least_normalized_margin_index": k,
        "margin_lower": margin_text(bound, False),
    }


def raw_prefix(last):
    cap = last**4
    flags, powers = prime_data(cap)
    marks = iter(sorted(powers))
    p = flags.find(1, 2)
    q = next(marks, cap + 1)
    sum_logs = weighted = 0
    upper = {}
    for k in range(2, last + 1):
        n = k**4
        while min(p, q) <= n:
            if p < q:
                d = p
                log = log_int(p)[1]
                p = flags.find(1, p + 1)
                if p < 0:
                    p = cap + 1
            else:
                d = q
                log = log_int(powers[q][0])[1]
                q = next(marks, cap + 1)
            sum_logs += log
            weighted += d * log
        upper[k] = F(2 * (n * sum_logs - weighted) - SCALE * n * n, 2 * SCALE * k**6)
    return upper


def individual():
    last = 1023
    cap = max(2**19, isqrt(2 * last**4))
    flags, _ = prime_data(cap)
    primes = [i for i in range(2, cap + 1) if flags[i]]
    logs = [log_int(p)[1] for p in primes]
    moment = [0]
    for p, log in zip(primes, logs):
        moment.append(moment[-1] + p**3 * log)
    exact_upper = raw_prefix(63)
    bands = {}
    for k in range(25, last + 1):
        n = k**4
        N = 2 * n
        D = isqrt(isqrt(isqrt(n**7)))
        assert D**8 <= n**7 < (D + 1) ** 8
        if D <= cap:
            small = F(2 * moment[bisect_right(primes, D)], 3 * SCALE * N**2 * k**6)
        else:
            assert 599 < D < 10**26
            ell = F(log_int(D)[1], SCALE)
            small = (
                F(1, 4)
                + F(13, 7) * ell**2 / (24 * isqrt(D))
                + 2 * ell / D
                + 3 * F(599, D) ** 4
            ) / 6
        repeat = 0
        for i in range(bisect_right(primes, isqrt(N))):
            p = primes[i]
            d = p * p
            while d <= N:
                repeat += extra(n, d) * logs[i]
                d *= p
        _, _, bill, _ = fast(k * k)
        allowance = (F(n * n, 14) - F(bill, N**5)) / k**6
        raw = exact_upper.get(k, F(4622, 100000))
        margin = allowance - raw - F(4, k * k) - F(repeat, SCALE * N**5 * k**6) - small
        assert margin > 0, k
        band = k.bit_length() - 1
        if band not in bands or margin < bands[band][0]:
            bands[band] = margin, k
    return {
        "index_interval": [25, last],
        "last_direct_prime_area": 63,
        "band_minimum_lower_margins": [
            {
                "from": max(25, 2**b),
                "through": min(last, 2 ** (b + 1) - 1),
                "minimum_index": k,
                "lower": margin_text(v, False),
            }
            for b, (v, k) in bands.items()
        ],
    }


def ceil_root(x, j):
    high = 1 << ((x.bit_length() + j - 1) // j)
    low = 0
    while high - low > 1:
        mid = (low + high) // 2
        if mid**j >= x:
            high = mid
        else:
            low = mid
    return high


def window(k0, nmax):
    n = k0**4
    N = 2 * n
    b = k0 * k0
    assert k0 >= 1024 and N == 1 << (N.bit_length() - 1)
    v = SHORT_PASSES * SHORT_WIDTH**2 / 3
    root = ceil_root(nmax, 2)
    raw = (
        F(root, 2) * v / (1 - v)
        + ORDINATE_MASS
        + F(10 * root, HEIGHT) * HIGH_FACTOR**SHORT_PASSES
    )
    ell = F(log_int(N)[1], 2 * SCALE)
    square = F(2, 3) * (three_halves(96) - 1) + F(5, 16) * max(
        F(599, b), F(6, 5) * ell**2 / (24 * k0) + ell / b
    )
    higher = (
        F(7, 5)
        * F(5, 32 * b)
        * (sum(ceil_root(N, i) for i in range(3, 9)) + N.bit_length() * ceil_root(N, 9))
    )
    small = (F(1, 4) + F(7, 4) * F(2, 1000) + F(3, 2**20)) / 6
    quadrature = F(4, b)
    c = contact_price()[0][0]
    refund = 2 * c - F(5, 32 * b) * (2 + 3 * k0)
    spend = raw + square + higher + small + quadrature
    assert spend < refund
    return {
        "first_index": k0,
        "last_board": str(nmax),
        "refund_lower": margin_text(refund, False),
        "raw_upper": margin_text(raw, True),
        "square_upper": margin_text(square, True),
        "higher_upper": margin_text(higher, True),
        "first_primes_upper": margin_text(small, True),
        "quadrature_upper": margin_text(quadrature, True),
        "combined_cost_upper": margin_text(spend, True),
        "surplus_lower": margin_text(refund - spend, False),
    }


def audit():
    last = isqrt(2**71)
    assert last**4 <= 2**142 < (last + 1) ** 4 and 2**72 < 10**26
    return {
        "all_positive_indices_through": last,
        "upper_board": str(2**142),
        "at_one": "bill zero",
        "direct": small_payments(),
        "individual": individual(),
        "uniform": [window(2**10, 2**56), window(2**14, 2**142)],
        "sources": "Same finite height, unrestricted high-zero tail and explicit prime estimates as the doubled-ruler reference. The nonasymptotic refund counts the actual two square traces.",
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
