"""Measure the least outer-trip distance change, with and without fixed owner addresses."""

from bisect import bisect_left, bisect_right
from itertools import permutations, product
import argparse
import json

from check_pal_dyson_window import prime_data, minus
from check_pal_tick_layers import tick_count, exact_ticks, log_number
from pal_tick_codec import TickCube, ceil_div
from pal_distance_transport import bounded_intervals, install_high_to_low, install_minimum_radius


def independent_interval(cube, witness):
    a, b = witness["first_prime"], witness["last_prime"]
    first, last = witness["first_destination"], witness["last_destination"]
    demand = sum(2 * (cube.n - p) * cube.prices[p] for p in cube.outer if a <= p <= b)
    full = cube.layers * (
        (cube.n - first) * (cube.n - first + 1) - (cube.n - last - 1) * (cube.n - last)
    )
    if first == 0:
        full -= cube.n * cube.layers  # the diagonal has one orientation
    used = sum(
        2 * starts * lanes for d, (_, starts, lanes) in cube.reserved.items() if first <= d <= last
    )
    assert (demand, full - used, demand - full + used) == (
        witness["source_records"],
        witness["available_cells"],
        witness["shortage"],
    )
    assert demand > full - used


def small_toys():
    cases = 0
    # Independent exhaustive assignments to labelled slots, including holes and excess room.
    for n in (3, 4):
        for source in product(range(3), repeat=n):
            if not 1 <= sum(source) <= 5:
                continue
            for capacity in product(range(3), repeat=n):
                if not sum(source) <= sum(capacity) <= 6:
                    continue
                jobs = [d for d, m in enumerate(source) for _ in range(m)]
                slots = [d for d, c in enumerate(capacity) for _ in range(c)]
                source_d = [d for d in range(n) if source[d]]
                source_offsets = [0]
                free = [0]
                for d in source_d:
                    source_offsets.append(source_offsets[-1] + source[d])
                for count in capacity:
                    free.append(free[-1] + count)
                exact = min(
                    max(abs(a - b) for a, b in zip(jobs, dest))
                    for dest in permutations(slots, len(jobs))
                )
                assert bounded_intervals(n, source_d, source_offsets, free, exact)[0]
                if exact:
                    assert not bounded_intervals(n, source_d, source_offsets, free, exact - 1)[0]
                cases += 1
    return cases


def exact_controls(cube, radius):
    all_inputs = cube.n <= 81
    visited = set()
    selected = (
        cube.outer
        if all_inputs
        else sorted(set(cube.outer[:: max(1, len(cube.outer) // 31)] + cube.outer[-1:]))
    )
    for p in list(selected) + (sorted(cube.owners) if all_inputs else sorted(cube.owners)[:3]):
        starts = range(cube.n - p) if all_inputs else sorted({0, (cube.n - p) // 2, cube.n - p - 1})
        ticks = (
            range(cube.prices[p])
            if all_inputs
            else sorted({0, cube.prices[p] // 2, cube.prices[p] - 1})
        )
        for i, t, side in product(starts, ticks, (0, 1)):
            record = p, i, t, side
            u, v, s = cube.encode(*record)
            assert cube.decode(u, v, s) == record and (u, v, s) not in visited
            visited.add((u, v, s))
            if p not in cube.owners:
                assert abs(abs(v - u) - p) <= radius
    if all_inputs:
        assert len(visited) == cube.count
    return {"exhaustive": all_inputs, "checked_roundtrips": len(visited)}


def owned_profile(cube, cut):
    estimates = []
    reserved_total = cube.middle_records
    if not reserved_total or not cube.outer:
        return estimates
    for numerator in (1, 2, 4, 6, 8, 10, 14):
        i = bisect_left(cube.outer, numerator * cube.n // 20)
        if i == len(cube.outer):
            continue
        p = cube.outer[i]
        q = cube.outer_starts[i]
        d = bisect_right(cube.free_offsets, q) - 1
        unpaid = sum(2 * a * s for m, (_, a, s) in cube.reserved.items() if m > p)
        estimates.append(
            {
                "prime": p,
                "first_destination": d,
                "inward_change": p - d,
                "cut": cut,
                "reserved_records_beyond_prime": unpaid,
                "all_reserved_records": reserved_total,
            }
        )
    return estimates


def run_head(k, shifted=False):
    x = k * k
    n = x * x
    flags, _ = prime_data(n)
    primes = [p for p in range(x + 1, n) if flags[p]]
    a, b = (6 * x + 11, 6 * x + 5) if shifted else (x + 1, x)
    step = minus(log_number(a), log_number(b))
    prices = {p: tick_count(p, a, b, step) for p in primes}
    if n <= 10000:
        assert all(h == exact_ticks(p, a, b) for p, h in prices.items())
    total = 2 * sum((n - p) * h for p, h in prices.items())
    height = ceil_div(total, n**2)
    cube_results = []
    for fixed in (False, True):
        cube = TickCube(n, height, prices, keep_prime_addresses=fixed)
        if n <= 4096:
            # Compare every sparse prefix to a fresh enumeration of all distance blocks.
            free = 0
            for d in range(n):
                assert cube.free_offsets[d] == free
                _, starts, lanes = cube.reserved.get(d, (0, 0, 0))
                free += (1 if d == 0 else 2) * ((n - d) * height - starts * lanes)
            assert cube.free_offsets[n] == free
        high = install_high_to_low(cube)
        cut = n // (4 * ceil_div(x * n.bit_length(), height))
        tail = owned_profile(cube, cut) if fixed else []
        radius, witness = install_minimum_radius(cube)
        assert radius <= high
        if witness:
            independent_interval(cube, witness)
        controls = exact_controls(cube, radius)
        cube_results.append(
            {
                "fixed_multiple_owners": fixed,
                "owner_cutoff": cut if fixed else 0,
                "reserved_distance_labels": len(cube.reserved),
                "reserved_records": cube.middle_records,
                "outer_records": cube.outer_records,
                "minimum_outer_radius": radius,
                "reverse_rank_radius": high,
                "failed_at_radius": radius - 1 if radius else None,
                "impossible_interval": witness,
                "reverse_owner_profile": tail,
                "decoder_control": controls,
            }
        )
    return {
        "k": k,
        "n": n,
        "clock": "shifted" if shifted else "ordinary",
        "actual_minimum_height": height,
        "all_records": total,
        "unused_in_minimum_box": height * n * n - total,
        "placements": cube_results,
    }


def audit(roots):
    return {
        "radius": "absolute difference between the original prime and the destination distance",
        "reference_volume": "minimum integer height at the actual head",
        "exhaustive_toy_layouts": small_toys(),
        "ordinary": [run_head(k) for k in roots],
        "shifted_controls": [run_head(k, True) for k in (8, 10)],
    }


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--roots", type=int, nargs="+", default=[2, 3, 4, 8, 12, 16, 24, 32, 48])
    args = cli.parse_args()
    if any(k < 2 for k in args.roots):
        cli.error("use positive roots from two")
    print(json.dumps(audit(sorted(set(args.roots))), indent=2))
