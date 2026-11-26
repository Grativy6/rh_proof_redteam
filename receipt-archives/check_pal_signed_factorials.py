"""Compute the forced signed factorial weights and price both orientations on genuine labels."""

import argparse
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, isqrt
import json

from check_pal_growth_windows import sieve
from check_pal_dyson_window import (
    SCALE,
    ZERO,
    plus,
    minus,
    natural,
    times,
    log_int,
    prime_data,
    inverse_root,
    interval_text,
    integer_box,
    ceil_div,
)
from check_pal_dense_square_payment import arctan_inverse, ln, c_limit, mul, sub, box, display
from check_pal_rise_direction import sqrt_box


def rational(q):
    return integer_box((Q(q), Q(q)))


@lru_cache(maxsize=30000)
def log_base(n):
    return log_int(n)


def signed(k, x):
    return natural(k, x) if k >= 0 else (k * x[1], k * x[0])


def direct_weight(x, d):
    if d <= 0 or 2 * d <= x or d >= 2 * x:
        return ZERO
    logw = minus(plus(log_base(2), log_base(min(x, d))), log_base(max(x, d)))
    return times(inverse_root(d), logw)


def factorial_prices(j):
    x = j * j
    N = 2 * x
    mu, _, primes = sieve(N)
    # Tail queries need only the division quotients, while the sieve is exact through 2*x.
    cuts = sorted(
        {v // n for v in (x // 2, x, 2 * x) for n in range(1, isqrt(2 * x) + 1)}
        | set(range(isqrt(2 * x) + 2))
    )
    a = b = ZERO
    data = {}
    start = 1
    for end in cuts:
        if end > N:
            continue
        for n in range(start, end + 1):
            if mu[n]:
                r = signed(mu[n], inverse_root(n))
                a = plus(a, r)
                b = plus(b, times(r, log_base(n)))
        data[end] = (a, b)
        start = end + 1
    L = log_base(2)
    lx = log_base(x)

    def tail(m):
        if m > N:
            return ZERO
        u = minus(lx, log_base(m))
        lo, mid, hi = x // (2 * m), x // m, 2 * x // m
        al, bl = data[lo]
        am, bm = data[mid]
        ah, bh = data[hi]
        left = minus(minus(bm, bl), times(minus(u, L), minus(am, al)))
        right = minus(times(plus(u, L), minus(ah, am)), minus(bh, bm))
        return times(inverse_root(m), plus(left, right))

    def exact_price():
        total = ZERO
        prim = ZERO
        for p in primes:
            if p > N:
                break
            n = p
            while n <= N:
                term = times(log_base(p), direct_weight(x, n))
                total = plus(total, term)
                if n == p:
                    prim = plus(prim, term)
                n *= p
        return total, prim

    direct, prime_only = exact_price()
    tol_cut = 1
    while (tol_cut - 1) ** 4 < j:
        tol_cut += 1
    pi = sub(mul(box(16), arctan_inverse(5)), mul(box(4), arctan_inverse(239)))
    hi = 10**11
    lp = (
        ln(2 * Q(pi[0] * hi // 1, hi))[0],
        ln(2 * Q(ceil_div(pi[1].numerator * hi, pi[1].denominator), hi))[1],
    )
    half_log_pi = integer_box((lp[0] / 2, lp[1] / 2))
    smoothed = total = logfac = first = positive = negative = ZERO
    selected = []
    tail_sum = 0
    here = tail(1)
    for m in range(1, N + 1):
        nxt = tail(m + 1)
        coefficient = minus(here, nxt)
        lm = log_base(m)
        logfac = plus(logfac, lm)
        total = plus(total, times(coefficient, logfac))
        first = plus(first, natural(m, coefficient))
        positive = plus(positive, natural(m, (max(0, coefficient[0]), max(0, coefficient[1]))))
        negative = plus(negative, natural(m, (max(0, -coefficient[1]), max(0, -coefficient[0]))))
        if m < tol_cut:
            approx = logfac
        else:
            approx = plus(
                plus(minus(times(rational(Q(2 * m + 1, 2)), lm), rational(m)), half_log_pi),
                rational(Q(1, 12 * m)),
            )
            price = max(abs(coefficient[0]), abs(coefficient[1]))
            tail_sum += ceil_div(price, 360 * m**3)
        smoothed = plus(smoothed, times(coefficient, approx))
        if j <= 7 or m in (1, 2, 3, 4, tol_cut - 1, tol_cut, x // 2, x, 3 * x // 2):
            selected.append([m, interval_text(here, 10), interval_text(coefficient, 10)])
        here = nxt
    assert first[0] <= 0 <= first[1]
    assert max(positive[0], negative[0]) <= min(positive[1], negative[1])
    assert max(direct[0], total[0]) <= min(direct[1], total[1])
    universal = Q(j, 90 * (tol_cut - 1) ** 4)
    assert max(direct[0], smoothed[0] - tail_sum) <= min(direct[1], smoothed[1] + tail_sum)
    point = {}
    for d in sorted({1, 2, 3, 4, 5, x, 2 * x, max(1, x // 3), max(1, x // 2 + 1)}):
        if d > N:
            continue
        read = ZERO
        for r in range(1, N // d + 1):
            read = plus(read, tail(d * r))
        expected = direct_weight(x, d)
        assert max(read[0], expected[0]) <= min(read[1], expected[1])
        point[str(d)] = interval_text(read, 8)
    return {
        "root": j,
        "head": x,
        "direct_prime_powers": interval_text(direct, 8),
        "prime_only": interval_text(prime_only, 8),
        "using_only_signed_log_factorials": interval_text(total, 8),
        "first_moment": interval_text(first, 8),
        "positive_first_moment": interval_text(positive, 8),
        "negative_first_moment_magnitude": interval_text(negative, 8),
        "continued_fractional_source_without_large_factorials": interval_text(smoothed, 8),
        "exact_factorials_below": tol_cut,
        "universal_stirling_allowance": str(universal),
        "local_stirling_allowance": interval_text((0, tail_sum), 9)[1],
        "reconstructed_labels": point,
        "selected_tail_and_change": selected,
    }


def measure_quarter_rows(heads=(50, 5000, 500000, 2000000)):
    """Separate the signed prime, square and higher-power contributions at whole heads."""
    flags, powers = prime_data(4 * max(heads))
    pi = sub(mul(box(16), arctan_inverse(5)), mul(box(4), arctan_inverse(239)))
    log_pi = integer_box((ln(pi[0])[0], ln(pi[1])[1]))
    rows = []
    for head in heads:

        def direction(label):
            return (4 * head) // label - 4 * ((2 * head) // label) + 4 * (head // label)

        groups = [ZERO, ZERO, ZERO]
        for prime in range(2, 4 * head + 1):
            if flags[prime]:
                orientation = direction(prime)
                if orientation:
                    groups[0] = plus(groups[0], signed(orientation, log_int(prime)))
        for label, (prime, exponent) in powers.items():
            if label <= 4 * head:
                group = 1 if exponent == 2 else 2
                groups[group] = plus(groups[group], signed(direction(label), log_int(prime)))
        full = plus(plus(groups[0], groups[1]), groups[2])
        # Combine the first-order Stirling expressions for (4m)!, (m!)^4 and (2m)!^4.
        twice_lead = minus(plus(log_pi, log_int(head)), log_int(2))
        approximated = plus(times(rational(Q(1, 2)), twice_lead), rational(Q(3, 16 * head)))
        remainder = Q(1, 70 * head**3)
        reference = plus(approximated, integer_box((-remainder, remainder)))
        assert max(full[0], reference[0]) <= min(full[1], reference[1])
        rows.append(
            {
                "head": head,
                "primes": interval_text(groups[0], 7),
                "squares": interval_text(groups[1], 7),
                "higher": interval_text(groups[2], 7),
                "all": interval_text(full, 7),
                "log_factorial_ratio": interval_text(reference, 7),
                "prime_contribution_per_root": interval_text(
                    times(groups[0], inverse_root(head)), 7
                ),
            }
        )
    return rows


def four_phases():
    R = Q(1)
    rows = []
    for m in range(32):
        rnext = R * Q((4 * m + 1) * (4 * m + 3) * (m + 1), 2 * (2 * m + 1) ** 3)
        values = [R, (4 * m + 1) * R, 4 * rnext / ((m + 1) * (4 * m + 3)), 4 * rnext / (m + 1)]
        for h, expected in enumerate(values):
            k = 4 * m + h
            actual = Q(factorial(k) * factorial(k // 4) ** 4, factorial(k // 2) ** 4)
            assert actual == expected
        if m in (0, 1, 2, 24, 25, 26):
            rows.append([m, *[str(q) for q in values]])
        R = rnext
    square = mul(sub(sqrt_box(2), box(2)), sub(sqrt_box(2), box(2)))
    k = mul(mul(box(2), c_limit()), square)
    return {
        "quarter_ratios": rows,
        "direct_signed_prime_powers": measure_quarter_rows(),
        "signed_primes_per_root_limit": display(k, 10),
        "odd_center_triangle_at_three": "(5*7)/(6*6)=35/36",
    }


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--roots", type=int, nargs="+", default=[2, 7, 49, 256])
    a = cli.parse_args()
    if any(n < 2 for n in a.roots):
        cli.error("positive roots from two are required")
    print(
        json.dumps(
            {"signed": list(map(factorial_prices, a.roots)), "stencil": four_phases()}, indent=2
        )
    )
