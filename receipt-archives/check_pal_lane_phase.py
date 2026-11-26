"""Integer enclosures for the first full lane harmonic and a shift invisible to every fast harmonic."""

import argparse
import json
from fractions import Fraction
from functools import lru_cache
from math import isqrt

from check_pal_dense_square_payment import arctan_inverse, display
from check_pal_dyson_window import prime_data
from check_pal_returned_horizon import CoveringClock
from check_pal_single_parent import Box, Interval, ONE, SCALE, ZERO, exponential


def quadrant_table(x):
    if x % 4:
        raise ValueError("these boards use complete quarters")
    a, b = arctan_inverse(5)
    c, d = arctan_inverse(239)
    angle = Interval.enclose(2 * (16 * a - 4 * d) / x, 2 * (16 * b - 4 * c) / x)
    step = exponential(Box(ZERO, angle))
    table = []
    value = ONE
    for _ in range(x // 4):
        table.append((value.real.lower, value.real.upper, value.imag.lower, value.imag.upper))
        value = value * step
    assert (
        value.real.lower <= 0 <= value.real.upper and value.imag.lower <= SCALE <= value.imag.upper
    )
    return table


def phasor(table, r):
    q, i = divmod(r, len(table))
    a, b, c, d = table[i]
    if q == 0:
        return a, b, c, d
    if q == 1:
        return -d, -c, a, b
    if q == 2:
        return -b, -a, -d, -c
    return c, d, -b, -a


def norm_squares(a, b):
    return (0 if a <= 0 <= b else min(a * a, b * b)), max(a * a, b * b)


def norm_interval(low, high):
    return Fraction(isqrt(low), SCALE), Fraction(isqrt(high) + 1, SCALE)


def sharp_control(M, x, clock):
    h = (clock.ticks(M) - 1) // x
    left, right = 1, M + 1
    while right - left > 1:
        c = (left + right) // 2
        if clock.ticks(c) <= h * x:
            left = c
        else:
            right = c
    length = isqrt(M) // 20
    first = left - length + 1
    separated = sum(h * x - clock.ticks(d) for d in range(first, left + 1))
    assert first > x and 0 <= separated and 12 * separated < x
    return {
        "integer_labels": [first, left],
        "count": length,
        "near_integer_winding": h,
        "total_distance_from_whole_turns_in_tick_units": separated,
        "tick_units_per_turn": x,
        "real_part_exceeds": str(Fraction(length, 2)),
    }


def evaluate_offset(histogram, table, count):
    ar = br = ai = bi = 0
    for index, multiplicity in enumerate(histogram):
        if multiplicity:
            a, b, c, d = phasor(table, index)
            ar += a * multiplicity
            br += b * multiplicity
            ai += c * multiplicity
            bi += d * multiplicity
    l0, h0 = norm_squares(ar, br)
    l1, h1 = norm_squares(ai, bi)
    lo, hi = norm_interval(l0 + l1, h0 + h1)
    # The rational angles have been rounded to the nearest grid point.
    # A half-grid step moves a unit phasor by at most pi/grid, with pi < 22/7.
    radius = Fraction(22 * count, 7 * len(histogram))
    return max(Fraction(0), lo - radius), hi + radius


OFFSETS = {4: (7537, 8192), 5: (36715, 262144), 6: (765853, 2097152)}
GRID = 2**20


@lru_cache(maxsize=1)
def offset_table():
    return quadrant_table(GRID)


def run(j):
    M = 16**j
    x = 4 ** (j + 1) * (j + 1) ** 2
    n = x * x
    clock = CoveringClock(x)
    table = quadrant_table(x)
    flags, _ = prime_data(M)
    selected = OFFSETS.get(j)
    histogram = [0] * GRID if selected else None
    count = total = fake = 0
    ar = br = ai = bi = 0
    best_low = best_high = 0
    best_at = 0
    first_breach = None
    largest_slow = 0
    allowance = x * (x // 13)
    for p in range(x + 1, M + 1):
        if not flags[p]:
            continue
        assert total % x == fake % x
        if selected:
            top, bottom = selected
            exact = (total % x) * bottom + (count * top % bottom) * x
            cell = ((2 * GRID * exact + x * bottom) // (2 * x * bottom)) % GRID
            histogram[cell] += 1
        a, b, c, d = phasor(table, total % x)
        ar, br, ai, bi = ar + a, br + b, ai + c, bi + d
        l0, h0 = norm_squares(ar, br)
        l1, h1 = norm_squares(ai, bi)
        if l0 + l1 > best_low:
            best_low, best_at = l0 + l1, p
        best_high = max(best_high, h0 + h1)
        before = total - x * (p - 1 - x)
        largest_slow = max(largest_slow, abs(before))
        tick = clock.ticks(p)
        total += tick
        fake += tick + x
        count += 1
        natural = total - x * (p - x)
        altered = fake - x * (p - x)
        largest_slow = max(largest_slow, abs(natural))
        assert altered - natural == x * count
        if first_breach is None and altered > allowance:
            assert allowance < altered % n < n - allowance
            first_breach = {
                "prime": p,
                "arrival": count,
                "actual_unwrapped": natural,
                "altered_unwrapped": altered,
                "actual_fast_lane": total % x,
                "altered_fast_lane": fake % x,
                "slow_arc_half_width": allowance,
            }
    largest_slow = max(largest_slow, abs(total - x * (M - x)))
    assert largest_slow <= allowance and first_breach is not None
    nl, nh = norm_squares(ar, br)
    il, ih = norm_squares(ai, bi)
    full = norm_interval(nl + il, nh + ih)
    maximum = norm_interval(best_low, best_high)
    assert maximum[1] < 1 + 100 * isqrt(M) + Fraction(20 * M, x)
    offset_data = None
    if selected:
        en = evaluate_offset(histogram, offset_table(), count)
        assert en[0] * en[0] > count
        offset_data = {
            "rational_turn": selected,
            "terminal_norm": display(en, 7),
            "selection": "FFT grid used to choose the frequency. A separate rational enclosure evaluates it.",
            "phase_rounding_grid": GRID,
        }
    return {
        "j": j,
        "selected_offset": offset_data,
        "M": M,
        "x": x,
        "prime_arrivals": count,
        "first_harmonic_terminal_norm": display(full, 7),
        "maximum_prefix_norm": display(maximum, 7),
        "largest_certified_lower_endpoint_at_prime": best_at,
        "prefix_norm_in_sqrt_M_units": display(tuple(a / isqrt(M) for a in maximum), 8),
        "true_slow_maximum_in_tick_units": largest_slow,
        "altered_first_forbidden_cut": first_breach,
        "integer_label_sharpness_control": sharp_control(M, x, clock),
    }


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--heads", type=int, nargs="+", default=[4, 5, 6])
    args = cli.parse_args()
    if any(j < 4 for j in args.heads):
        cli.error("the comparison of active streams starts at board four")
    print(json.dumps({"boards": [run(j) for j in sorted(set(args.heads))]}, indent=2))
