"""Exact largest corrected mismatch on the returned-horizon boards, with rational log bounds."""

import argparse
from fractions import Fraction
from math import ceil, floor
import json

from check_pal_dyson_window import log_int, prime_data
from check_pal_single_parent import SCALE


def area(n, m):
    return n * m - m * (m + 1) // 2


def log_ratio_interval(value, unit, terms):
    """Enclose log(value/unit) by rational odd powers, with value >= unit > 0."""
    z = Fraction(value - unit, value + unit)
    lower = 2 * sum(z ** (2 * k + 1) / (2 * k + 1) for k in range(terms))
    upper = lower + 2 * z ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))
    return lower, upper


class CoveringClock:
    """Reciprocate the small log step before quantizing the tick count."""

    def __init__(self, root):
        self.root = root
        self.scale = 10**40
        self.refinements = 0
        low, high = log_ratio_interval(root + 1, root, 12)
        self.inverse_low = floor(self.scale / high)
        self.inverse_high = ceil(self.scale / low)

    def ticks(self, p):
        low, high = log_int(p)
        unit = SCALE * self.scale
        first = -(-(low * self.inverse_low) // unit)
        last = -(-(high * self.inverse_high) // unit)
        if first == last:
            return first
        self.refinements += 1
        exponent = p.bit_length() - 1
        terms = 40
        while True:
            two_low, two_high = log_ratio_interval(2, 1, terms)
            rem_low, rem_high = log_ratio_interval(p, 2**exponent, terms)
            step_low, step_high = log_ratio_interval(self.root + 1, self.root, terms)
            first = ceil((exponent * two_low + rem_low) / step_high)
            last = ceil((exponent * two_high + rem_high) / step_low)
            if first == last:
                return first
            # For root > 1 a positive power of the reduced fraction (root+1)/root
            # cannot equal an integer prime. Shrinking these intervals separates it.
            terms *= 2


def head(j):
    u = j + 1
    x = 4**u * u**2
    n = x**2
    end = 16**j
    high = low = 0
    high_at = low_at = high_jobs = 0
    jobs = 0
    first = last = None

    def observe(m):
        nonlocal high, low, high_at, low_at, high_jobs
        diff = jobs + x * area(n, min(m, x)) - x * area(n, m)
        if diff > high:
            high, high_at, high_jobs = diff, m, jobs
        if -diff > low:
            low, low_at = -diff, m

    clock = CoveringClock(x)
    observe(min(x, end))
    if x < end:
        primes, _ = prime_data(end)
        for p in range(x + 1, end + 1):
            if not primes[p]:
                continue
            observe(p - 1)
            t = clock.ticks(p)
            if first is None:
                first = (p, t)
            last = (p, t)
            jobs += (n - p) * t
            observe(p)
    observe(end)
    if j == 4:
        for p, t in (first, last):
            # Decides the covering tick directly with ordinary integers.
            assert (x + 1) ** (t - 1) < p * x ** (t - 1)
            assert (x + 1) ** t >= p * x**t
    worst = max(high, low)
    allowed = n**2 // 13
    unreturned = x * area(n, min(x, end))
    assert worst <= allowed
    if j <= 3:
        assert x >= end and worst == 0
    if j >= 3:
        assert x <= end and 13 * unreturned > n**2
    tight = None
    if high:
        p = high_at
        t = clock.ticks(p)
        before = high + x * (area(n, p - 1) - area(n, x))
        through = high + x * (area(n, p) - area(n, x))
        assert x < p <= end and t > 0 and high_jobs == through
        assert through - before == x * (n - p)
        start, lane = divmod(high_jobs - 1 - before, x)
        assert (start, lane) == (n - p - 1, x - 1)
        tight = {
            "minimum_initial_buffer": high,
            "distance": p,
            "last_forward_job": [p, n - p - 1, t - 1],
            "arrival_ordinal": high_jobs - 1,
            "actual_destination_sites_and_layer": [start, start + p, lane],
            "jobs_through_cut": high_jobs,
            "released_before_cut": before,
            "released_through_cut": through,
        }
    natural_minimum = lowest_prime_weight(end) if j >= 4 else None
    return {
        "j": j,
        "ordinary_prime_error_minimum": natural_minimum,
        "last_arrival_at_tight_upper_cut": tight,
        "root": x,
        "board_size": n,
        "last_cut": end,
        "forward_jobs_at_last_cut": jobs,
        "first_and_last_prime_ticks": [first, last],
        "log_intervals_refined": clock.refinements,
        "largest_surplus": [high, high_at],
        "largest_deficit": [low, low_at],
        "maximum_absolute_mismatch": worst,
        "one_thirteenth_integer_allowance": allowed,
        "whole_units_left": allowed - worst,
        "uncorrected_gap_at_last_empty_cut": unreturned,
    }


def lowest_prime_weight(end):
    """Certify the unique minimum of theta(m)-m through end using rational log enclosures."""
    flags, _ = prime_data(end)
    low_sum = high_sum = 0
    previous = None
    best = None
    widest_gap = None
    two_lowest = []

    def observe(cut, next_prime):
        nonlocal best, two_lowest
        lo, hi = low_sum - SCALE * cut, high_sum - SCALE * cut
        if best is None or hi < best[0]:
            best = (hi, cut, lo, previous, next_prime)
        two_lowest = sorted([*two_lowest, (lo, cut)])[:2]

    for p in range(2, end + 1):
        if flags[p]:
            observe(p - 1, p)
            if previous is not None and (
                widest_gap is None or p - previous > widest_gap[1] - widest_gap[0]
            ):
                widest_gap = (previous, p)
            lo, hi = log_int(p)
            low_sum += lo
            high_sum += hi
            previous = p
    observe(end, None)
    hi, cut, lo, previous, following = best
    rival = next((bound for bound, m in two_lowest if m != cut), None)
    if rival is not None:
        assert hi < rival
    return {
        "cut": cut,
        "previous_prime": previous,
        "first_widest_complete_prime_gap": widest_gap,
        "next_prime": following,
        "error_numerators": [lo, hi],
        "denominator": SCALE,
        "second_terminal_cut_error_at_least": rival,
    }


def rational_constants():
    # Elementary log bounds use the symmetric geometric series with an explicit remainder.
    # Machin's formula and the alternating arctangent series give strict rational pi bounds.
    def atan_interval(d):
        z = Fraction(1, d)
        lower = sum((-1) ** k * z ** (2 * k + 1) / (2 * k + 1) for k in range(12))
        return lower, lower + z**25 / 25

    log2_lo, log2_hi = log_ratio_interval(2, 1, 45)
    log5_lo, log5_hi = log_ratio_interval(5, 1, 45)
    a_lo, a_hi = atan_interval(5)
    b_lo, b_hi = atan_interval(239)
    pi_lo, pi_hi = 16 * a_lo - 4 * b_hi, 16 * a_hi - 4 * b_lo
    assert Fraction(69, 100) < log2_lo < log2_hi < Fraction(6932, 10000)
    assert Fraction(160, 100) < log5_lo < log5_hi < Fraction(161, 100)
    assert Fraction(314, 100) < pi_lo < pi_hi < Fraction(22, 7)
    c_lo, c_hi = log2_lo**2 / (2 * pi_hi), log2_hi**2 / (2 * pi_lo)
    remainder = (10 * log2_hi + 2 * log5_hi) ** 2 / (8 * pi_lo * 32) + Fraction(3, 16 * 5**3)
    assert remainder < Fraction(13, 100) < Fraction(9, 5) * c_lo and c_hi < Fraction(1, 13)
    assert c_lo > Fraction(2, 27)
    return {
        "c_above": "2/27",
        "c_below": "1/13",
        "root_error_times_five_plus_rounding_below": "13/100",
    }


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--last-index", type=int, default=6)
    args = cli.parse_args()
    if args.last_index < 0:
        cli.error("use a nonnegative last index")
    print(
        json.dumps(
            {
                "rational_bounds": rational_constants(),
                "boards": [head(j) for j in range(args.last_index + 1)],
            },
            indent=2,
        )
    )
