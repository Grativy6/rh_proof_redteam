"""Fit one integer height to every measured prefix on each of the geometric boards."""

import argparse
import json
from math import factorial, gcd

from check_pal_dyson_window import minus, prime_data
from check_pal_tick_layers import exact_ticks, log_number, tick_count


def area(n, m):
    return n * m - m * (m + 1) // 2


def price_curve(j):
    """Between prime jumps the job count stays fixed and the comparison area increases."""
    m_last = 16**j
    x = 4 ** (j + 1)
    n = x * x
    flags, _ = prime_data(m_last)
    step = minus(log_number(x + 1), log_number(x))
    rows = [(0, 0, 0)]
    total = 0
    if x <= m_last:
        rows.append((x, area(n, x), 0))
    for p in range(x + 1, m_last + 1):
        if not flags[p]:
            continue
        rows.append((p - 1, area(n, p - 1), total))
        total += (n - p) * tick_count(p, x + 1, x, step)
        rows.append((p, area(n, p), total))
    rows.append((m_last, area(n, m_last), total))
    return n, x, rows


def deviations(rows, h):
    high = low = cut_high = cut_low = 0
    for m, a, jobs in rows:
        diff = jobs - h * a
        if diff > high:
            high, cut_high = diff, m
        if -diff > low:
            low, cut_low = -diff, m
    return high, low, cut_high, cut_low


def integer_window(rows, error):
    """Compute the intersection of all allowed heights and the cuts fixing its ends."""
    lower, upper = (0, 0), None
    for m, a, jobs in rows:
        if not a:
            assert jobs == 0
            continue
        lo = -((error - jobs) // a)
        hi = (jobs + error) // a
        if lo > lower[0]:
            lower = (lo, m)
        if upper is None or hi < upper[0]:
            upper = (hi, m)
    return lower, upper


def solve(j):
    n, x, rows = price_curve(j)
    below, above = -1, 1
    while True:
        high, low, _, _ = deviations(rows, above)
        if low >= high:
            break
        above *= 2
    while above - below > 1:
        mid = (above + below) // 2
        high, low, _, _ = deviations(rows, mid)
        if low >= high:
            above = mid
        else:
            below = mid
    error, h = min((max(deviations(rows, y)[:2]), y) for y in {above, max(0, below)})
    high, low, cut_high, cut_low = deviations(rows, h)
    lo, hi = integer_window(rows, error)
    centered = ((m, a, jobs + x * area(n, min(x, m))) for m, a, jobs in rows)
    c_high, c_low, c_up, c_down = deviations(centered, x)
    assert lo[0] <= h <= hi[0]
    impossible = None
    if error:
        left, right = integer_window(rows, error - 1)
        assert left[0] > right[0]
        impossible = {"minimum_height": left, "maximum_height": right}
    single_lower, single_upper = integer_window(rows, n**2)
    cuts = {single_lower[1], single_upper[1]}
    single_cuts = {m: {"area": a, "jobs": jobs} for m, a, jobs in rows if m in cuts}
    if j <= 2:
        total = 0
        all_rows = [(0, 0, 0)]
        marker = factorial(x)
        for m in range(1, 16**j + 1):
            if m >= 2 and gcd(m, marker) == 1:
                total += (n - m) * exact_ticks(m, x + 1, x)
            all_rows.append((m, sum(n - d for d in range(1, m + 1)), total))
        assert error == min(
            max(abs(jobs - y * a) for _, a, jobs in all_rows) for y in range(2 * x + 1)
        )
        assert deviations(all_rows, h)[:2] == (high, low)
    return {
        "j": j,
        "n": n,
        "last_prefix": 16**j,
        "square_root": x,
        "one_best_height": h,
        "with_small_prefix_return_at_root_height": {
            "largest_surplus": [c_high, c_up],
            "largest_deficit": [c_low, c_down],
        },
        "all_best_heights": [lo[0], hi[0]],
        "minimum_maximum_error": error,
        "board_area": n**2,
        "largest_surplus": {"at": cut_high, "count": high},
        "largest_deficit": {"at": cut_low, "count": low},
        "impossible_one_fewer": impossible,
        "one_board_area": {
            "height_at_least": single_lower,
            "height_at_most": single_upper,
            "cuts": single_cuts,
        },
    }


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--last-index", type=int, default=6)
    args = cli.parse_args()
    if args.last_index < 0:
        cli.error("the final board index must be nonnegative")
    print(json.dumps([solve(j) for j in range(args.last_index + 1)], indent=2))
