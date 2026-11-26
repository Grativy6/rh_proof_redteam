"""Reproduce the two unbounded integer address inequalities and their ordinary-log prices."""

import json
from fractions import Fraction as F
from math import prod

from check_pal_dyson_window import SCALE, log_int
from check_pal_moving_endpoint import upper_text

UP = (102, -51, -34, 0, -20, 17, -15, 1, 0, 8, -8, 0, 0, 4, -1, -3)
LOW = (-198, 99, 66, 0, 40, -29, 21, 3, 0, -9, 0, 7, 11, -8, -6, 3)


def coefficients(row):
    low = high = 0
    for j, c in enumerate(row, 1):
        a, b = log_int(j)
        if c < 0:
            a, b = b, a
        low += c * a
        high += c * b
    return F(low, SCALE), F(high, SCALE)


def twice_area(j, k):
    q, r = divmod(k, j)
    by_ramps = j * (2 * k * q - j * q * (q + 1))
    by_marks = k * k - j * k + r * (j - r)
    assert by_ramps == by_marks
    return by_marks


def check_row(row, sign, D):
    assert sum(row) == 0
    first = sum(j * c for j, c in enumerate(row, 1))
    absolute = sum(j * j * abs(c) for j, c in enumerate(row, 1))
    slope = -first - 2 * sign * D
    lower_tail_times_four = 4 * (201 * slope + 2 * sign * D) - absolute
    assert slope > 0 and lower_tail_times_four >= 0

    def residual(k):
        twice = sum(c * twice_area(j, k) for j, c in enumerate(row, 1)) - 2 * sign * D * (k - 1)
        assert twice % 2 == 0
        return twice // 2

    assert all(residual(k) >= 0 for k in range(1, 201))
    assert residual(18) - 2 * residual(17) + residual(16) == row[0]
    # Reprice using arithmetic on products only. The logarithm enclosure is an
    # independent check on the combined dyadic power inequality used in Lean.
    plus = prod(j ** max(0, c) for j, c in enumerate(row, 1))
    minus = prod(j ** max(0, -c) for j, c in enumerate(row, 1))
    logs = coefficients(row)
    if sign == 1:
        low, hi = -logs[1] / (2 * D), -logs[0] / (2 * D)
        assert minus**64 <= 2**9490 * plus**64 and hi < F(63, 125)
    else:
        low, hi = logs[0] / (2 * D), logs[1] / (2 * D)
        assert plus**64 >= 2**18142 * minus**64 and low > F(62, 125)
    separate = sum(j * abs(c) for j, c in enumerate(row, 1))
    rounded_low = low.numerator * 10**12 // low.denominator
    lower_text = f"{rounded_low // 10**12}.{rounded_low % 10**12:012d}"
    return {
        "coefficients": list(row),
        "normalizer": D,
        "sum": sum(row),
        "first_moment": first,
        "absolute_second_moment": absolute,
        "end_of_direct_test": 200,
        "tail_slope": slope,
        "four_times_tail_margin_at_201": lower_tail_times_four,
        "sampled_address_excess_at_16_17_18": [residual(k) for k in (16, 17, 18)],
        "slope_kink_at_missing_17": row[0],
        "absolute_sampling_price": 3 * separate,
        "leading_area_interval": [lower_text, upper_text(hi)],
    }


def audit():
    up = check_row(UP, 1, 102)
    lo = check_row(LOW, -1, 198)
    # At k>=512: k^5<=k^6, and k^8>=512^2*k^6.
    assert (1 - 13 * (F(4, 7) - F(62, 125))) * 512**2 > 13 * (96 + 256) + 3
    # At k>=200000^2: all omitted single primes are <=n/200000.
    # The known stock Chebyshev bounds pay all remaining repeated powers.
    gain = 15 * (F(4, 7) - F(63, 125) - F(84, 200000)) - 1
    assert gain * 200000**2 > 15 * (498 + 256 + 448)
    return {
        "upper": up,
        "lower": lo,
        "proved_integer_comparisons": {
            "thirteen_fails_from": 512,
            "fifteen_pays_from": 200000**2,
            "fourteen_eventual_implies": "stock Mathlib RiemannHypothesis",
        },
        "unconditional_area_leading_range": ["62/125", "63/125"],
        "ordinary_sampling_error_per_side": "32 n log(n+1)",
        "unseen_prime": 17,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
