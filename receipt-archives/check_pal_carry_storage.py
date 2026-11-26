"""Measure what crosses every physical cut on the prime boards, including both orientations."""

from itertools import product
import argparse
import json

from check_pal_dyson_window import prime_data
from check_pal_returned_horizon import CoveringClock, area
from pal_carry_storage import cut_depth, finite_depths, least_capacity, minimum_draw, read_path
from pal_tick_columns import TickColumns, column_receipt


def all_plans(jumps, capacities):
    states = {0: 0}
    for jump, cap in zip(jumps, capacities):
        due, release = max(jump, 0), max(-jump, 0)
        new = {}
        for stock, spent in states.items():
            free = stock + release
            for retained in range(min(free, cap) + 1):
                out = spent + max(0, due + retained - free)
                new[retained] = min(new.get(retained, out), out)
        states = new
    return min(states.values())


def exhaustive():
    total = 0
    for jumps in product(range(-2, 3), repeat=4):
        values = [0]
        for jump in jumps:
            values.append(values[-1] + jump)
        peak = max(values)
        depths = finite_depths(values)
        profile = [min(max(values[: i + 1]), max(values[i:])) - z for i, z in enumerate(values)]
        assert cut_depth(values)[0] == max(profile) == (max(depths) if depths else 0)
        assert all_plans(jumps, profile[1:]) == peak
        for i, depth in enumerate(profile[1:], 1):
            if depth:
                caps = [12] * len(jumps)
                caps[i - 1] = depth - 1
                assert all_plans(jumps, caps) > peak
        for cap in range(7):
            draw = minimum_draw(values, cap)
            assert draw == peak + sum(max(d - cap, 0) for d in depths)
            assert draw == all_plans(jumps, [cap] * 4)
            price = least_capacity(peak, depths, draw)
            assert price <= cap and (not price or minimum_draw(values, price - 1) > draw)
            total += 1
    return total


def sixteen():
    n, x = 16, 4
    primes = [5, 7, 11, 13]
    ticks = [CoveringClock(x).ticks(p) for p in primes]
    counts = column_receipt(n, x, n, primes, ticks, True)
    scheme = TickColumns(n, x, primes, ticks)
    sample = scheme.encode(11, 1, 0)
    dead = [(row, scheme.row_remainder(row, n)) for row in range(n) if scheme.row_remainder(row, n)]
    assert (
        sample == (7, 1, 2, 1)
        and counts["actual_records"] == 260
        and counts["unoccupied_shared_lanes"] == 12
    )
    return {
        "primes": primes,
        "ticks": ticks,
        "counts": counts,
        "source": [11, 1, 0],
        "physical_owner_row_column_lane": sample,
        "inverse": scheme.decode(*sample),
        "retired_rows_and_lanes": dead,
    }


def board(j):
    x = 4 ** (j + 1) * (j + 1) ** 2
    n = x * x
    end = 16**j
    flags, _ = prime_data(end)
    clock = CoveringClock(x)
    primes = [p for p in range(x + 1, end + 1) if flags[p]]
    if not primes:
        return {"j": j, "n": n, "x": x, "last": end, "all_jobs": 0}
    ticks = [clock.ticks(p) for p in primes]
    locations = [x]
    values = [0]
    indices = [0]
    jobs = 0
    base = x * area(n, x)
    for p, t in zip(primes, ticks):
        if p - 1 > locations[-1]:
            locations.append(p - 1)
            values.append(jobs + base - x * area(n, p - 1))
        jobs += (n - p) * t
        locations.append(p)
        values.append(jobs + base - x * area(n, p))
        indices.append(len(values) - 1)
    if locations[-1] != end:
        locations.append(end)
        values.append(jobs + base - x * area(n, end))
        indices.append(len(values) - 1)
    pocket = n * n // 13
    physical = read_path(values, locations, pocket)
    reflected = read_path([-z for z in values], locations, pocket)
    arrivals = read_path([values[i] for i in indices], [locations[i] for i in indices], pocket)
    return {
        "j": j,
        "n": n,
        "x": x,
        "last": end,
        "original": physical,
        "opposite": reflected,
        "capacity_enforced_only_after_prime_arrivals": arrivals,
        "column_allocations": column_receipt(n, x, end, primes, ticks),
    }


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--heads", type=int, nargs="+", default=[4, 5, 6])
    args = cli.parse_args()
    if any(j < 0 for j in args.heads):
        cli.error("nonnegative indices required")
    print(
        json.dumps(
            {
                "exhaustive_state_and_capacity_cases": exhaustive(),
                "worked_sixteen": sixteen(),
                "boards": [board(j) for j in sorted(set(args.heads))],
            },
            indent=2,
        )
    )
