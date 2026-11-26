"""Compare the single product clock to the actual tick and whole-column clocks."""

import argparse
import json
from math import prod

from check_pal_dyson_window import prime_data
from check_pal_returned_horizon import CoveringClock
from pal_product_clock import ProductClock, ProductRows


def run(n, x, m, direct=False):
    flags, _ = prime_data(m)
    primes = [p for p in range(x + 1, m + 1) if flags[p]]
    clock = ProductClock(x)
    separate = CoveringClock(x)
    raw = pooled = flag_cells = flags_hit = 0
    separate_sum = old = 0
    comparison_budget = max(0, x // 13 - (-(-m // x)))
    largest = 0
    positive_at = 0
    lowest = low_at = 0
    joint = [[0, 0], [0, 0]]
    joint_rows = [[0, 0], [0, 0]]
    events = []
    times = []
    pooled_ends = []
    first_flag = None
    for i, p in enumerate(primes):
        prior_short = max(0, p - 1 - x) - ((old - 1) // x if old else 0)
        if prior_short > lowest:
            lowest, low_at = prior_short, p - 1
        ticks, shared, total = clock.push(p)
        if direct or i % max(1, len(primes) // 64) == 0:
            assert ticks == separate.ticks(p)
        if direct:
            q = prod(primes[: i + 1])
            assert (x + 1) ** (total - 1) < q * x ** (total - 1) and (
                x + 1
            ) ** total >= q * x**total
            whole = -(-total // x)
            assert (x + 1) ** ((whole - 1) * x) < q * x ** ((whole - 1) * x) and (x + 1) ** (
                whole * x
            ) >= q * x ** (whole * x)
            events.append([p, ticks, shared, total])
        times.append(ticks)
        pooled_ends.append(total)
        if first_flag is None and ticks != shared:
            first_flag = i
        older_columns = -(-separate_sum // x)
        separate_sum += ticks
        columns = -(-separate_sum // x) - older_columns
        tick_flag = ticks - shared
        column_flag = -(-ticks // x) - columns
        assert tick_flag in (0, 1) and column_flag in (0, 1)
        joint[tick_flag][column_flag] += 1
        joint_rows[tick_flag][column_flag] += n - p
        raw += (n - p) * ticks
        pooled += (n - p) * shared
        flag_cells += (ticks - shared) * (n - p)
        flags_hit += ticks - shared
        assert total <= separate_sum <= total + i + 1 and flags_hit == separate_sum - total
        rise = -(-total // x) - max(0, p - x)
        if rise > largest:
            largest, positive_at = rise, p
        old = total
    last_cut_deficit = max(0, m - x) - ((old - 1) // x if old else 0)
    if last_cut_deficit > lowest:
        lowest, low_at = last_cut_deficit, m
    assert raw == pooled + flag_cells
    if not direct:
        assert largest <= comparison_budget and lowest <= x // 13
    bank = max(largest, comparison_budget) if direct else comparison_budget
    if not direct and primes:
        assert bank * x + m <= x * (x // 13)
    codec = ProductRows(n, x, m, bank, primes, times, pooled_ends)
    selected = (
        list(range(len(primes)))
        if direct
        else sorted(
            set(range(0, len(primes), max(1, len(primes) // 24)))
            | ({len(primes) - 1} if primes else set())
            | ({first_flag} if first_flag is not None else set())
        )
    )
    checked = 0
    samples = {}
    for i in selected:
        p = primes[i]
        rows = range(n - p) if direct else sorted({0, n - p - 1})
        for row in rows:
            for tick in range(times[i]) if direct else sorted({0, times[i] // 2, times[i] - 1}):
                slot = codec.encode(p, row, tick)
                assert codec.decode(slot) == (p, row, tick)
                if slot[0] == "ordinary":
                    assert slot[2] - row <= p and slot[2] < n
                label = "flag" if slot[0] == "pocket" and slot[2] < m else slot[0]
                samples.setdefault(label, {"source": [p, row, tick], "stored": slot})
                checked += 1
    if direct:
        assert checked == raw
    return {
        "n": n,
        "x": x,
        "last_cut": m,
        "prime_count": len(primes),
        "joint_flags_tick_then_column": joint,
        "forward_start_counts_by_joint_flags": joint_rows,
        "sum_separate_ticks": separate_sum,
        "single_product_ticks": old,
        "rounded_tick_flags": flags_hit,
        "ordinary_forward_jobs": raw,
        "product_clock_forward_jobs": pooled,
        "separate_positions_for_flags": flag_cells,
        "refined_log_grids": clock.refinements,
        "max_product_columns_above_released_distance": [largest, positive_at],
        "fixed_product_column_budget": comparison_budget,
        "max_lower_product_shortage": [lowest, low_at],
        "lower_budget": x // 13,
        "direct_product_powers": events,
        "fixed_row_codec": {
            "checked": checked,
            "exhaustive": direct,
            "examples": samples,
            "ordinary_bank_columns": bank,
        },
    }


def choice_control():
    j = 4
    x = 4 ** (j + 1) * (j + 1) ** 2
    m = 16**j
    quota = x // 13
    guard = -(-m // x)
    first = x + quota + 1
    flags, _ = prime_data(m)
    p = next(i for i in range(first + 1, m + 1) if flags[i])
    height = (p - x) + (quota - guard)
    copies = height // 9 + 1
    assert first == 27570 and p == 27581 and copies == 439 and p > 3**9
    assert x * ((first - x) - quota) == x and copies * 9 > height
    # With just ones up through first, the lower comparison fails there.
    # At p the replacement sends p**copies. Since (1+1/x)**x < 3, the upper
    # comparison fails without needing to expand the enormous clock powers.
    assert p**copies > 3**height
    return {
        "j": j,
        "lower_fails_at": first,
        "later_genuine_prime_used_as_repeated_label": p,
        "synthetic_multiplicity": copies,
        "number_of_x_step_blocks_in_upper_test": height,
    }


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--heads", type=int, nargs="+", default=[4, 5, 6])
    args = cli.parse_args()
    if any(j < 0 for j in args.heads):
        cli.error("nonnegative board index required")
    boards = []
    for j in sorted(set(args.heads)):
        x = 4 ** (j + 1) * (j + 1) ** 2
        boards.append({"j": j, **run(x * x, x, 16**j)})
    print(
        json.dumps(
            {
                "small_product": run(16, 4, 16, True),
                "choice_control": choice_control(),
                "boards": boards,
            },
            indent=2,
        )
    )
