"""Optimize expiring prime-gap credit, including partitions chosen after all primes are known."""

import argparse
from functools import lru_cache
from itertools import product
import json

from check_pal_dyson_window import prime_data
from check_pal_returned_horizon import CoveringClock, area


def minimum_spent(prefix, last, span, causal=False, reconstruct=False):
    """The previous boundary can be any of the last span prime arrivals."""
    if span < 1:
        raise ValueError("a block must admit at least one prime")
    count = len(prefix) - 1
    cost = [0] * (count + 1)
    previous = [0] * (count + 1) if reconstruct else None
    for end in range(1, count + 1):
        high = prefix[end]
        value = last if end == count else prefix[end]
        best = None
        for start in range(end - 1, max(-1, end - span - 1), -1):
            if causal:
                high = max(high, prefix[start + 1])
                value = high
            candidate = cost[start] + max(0, value - prefix[start])
            if best is None or candidate < best:
                best, best_start = candidate, start
        cost[end] = best
        if reconstruct:
            previous[end] = best_start
    if not reconstruct:
        return cost[-1]
    boundaries = []
    end = count
    price = 0
    while end:
        start = previous[end]
        assert 0 < end - start <= span
        if causal:
            value = max(prefix[start + 1 : end + 1])
        else:
            value = last if end == count else prefix[end]
        price += max(0, value - prefix[start])
        boundaries.append((start, end))
        end = start
    assert price == cost[-1]
    return price, list(reversed(boundaries))


def toy_controls():
    checked = 0
    for jumps in product((-3, 0, 4), repeat=4):
        prefix = [0]
        for jump in jumps:
            prefix.append(prefix[-1] + jump)
        for trailing in (0, 2):
            last = prefix[-1] - trailing
            for span in (1, 2, 3, 4):
                for causal in (False, True):
                    brute = None
                    for mask in range(1 << 3):
                        stops = [0] + [i + 1 for i in range(3) if mask & (1 << i)] + [4]
                        if any(b - a > span for a, b in zip(stops, stops[1:])):
                            continue
                        price = 0
                        for a, b in zip(stops, stops[1:]):
                            endpoint = last if b == 4 else prefix[b]
                            demand = max(prefix[a + 1 : b + 1]) if causal else endpoint
                            price += max(0, demand - prefix[a])
                        brute = price if brute is None else min(brute, price)
                    assert minimum_spent(prefix, last, span, causal) == brute
                    checked += 1
    return checked


def ten_arrivals():
    results = []
    for widths in ([3] * 3 + [2] * 7, [2] * 7 + [3] * 3):
        z = [0]
        for width in widths:
            z.append(z[-1] + 23 - 10 * width)
        assert z[-1] == 0
        shared = max(z)
        spent = minimum_spent(z, z[-1], 1, True)
        assert spent == 21 and minimum_spent(z, z[-1], 10, True) == shared
        results.append(
            {
                "gap_widths": widths,
                "demand": 230,
                "cells_released": 230,
                "shared_initial_buffer": shared,
                "single_gap_resets": spent,
            }
        )
    return results


def replay_allocation(arrivals, trailing, blocks, causal):
    """Spend released cells directly for one named partition, with no prefix differences."""
    required = 0
    for start, end in blocks:
        free = 0
        if causal:
            for released, jobs in arrivals[start:end]:
                free += released
                used = min(free, jobs)
                free -= used
                required += jobs - used
        else:
            free = sum(released for released, _ in arrivals[start:end])
            if end == len(arrivals):
                free += trailing
            jobs = sum(jobs for _, jobs in arrivals[start:end])
            required += max(0, jobs - free)
    return required


def prime_prefix(j):
    x = 4 ** (j + 1) * (j + 1) ** 2
    n = x * x
    m = 16**j
    primes, _ = prime_data(m)
    clock = CoveringClock(x)
    prefix = [0]
    jobs = 0
    arrivals = []
    previous_prime = x
    total_own = 0
    factor_failure = None
    for p in range(x + 1, m + 1):
        if not primes[p]:
            continue
        ticks = clock.ticks(p)
        charge = (n - p) * ticks
        arrivals.append((x * (area(n, p) - area(n, previous_prime)), charge))
        previous_prime = p
        jobs += charge
        total_own += (n - p) * max(0, ticks - x)
        if factor_failure is None and total_own > n * n // 13:
            factor_failure = {
                "at_prime": p,
                "prime_groups_used": len(prefix),
                "minimum_buffer": total_own,
            }
        prefix.append(jobs - x * (area(n, p) - area(n, x)))
    last = jobs - x * (area(n, m) - area(n, min(m, x)))
    trailing = x * (area(n, m) - area(n, min(m, previous_prime)))
    return x, n, m, prefix, last, factor_failure, arrivals, trailing


def run(j, find_transition, show_partitions=False):
    x, n, m, prefix, last, factor, arrivals, trailing = prime_prefix(j)
    count = len(prefix) - 1
    allowed = n * n // 13
    assert count and max(prefix) <= allowed
    rows = []
    for causal in (False, True):

        @lru_cache(maxsize=None)
        def price(span):
            return minimum_spent(prefix, last, span, causal)

        if find_transition:
            lower, upper = 0, 1
            while price(upper) > allowed:
                lower, upper = upper, min(2 * upper, count)
                assert upper > lower
            while upper - lower > 1:
                mid = (lower + upper) // 2
                if price(mid) > allowed:
                    lower = mid
                else:
                    upper = mid
            optimum, boundaries = minimum_spent(prefix, last, upper, causal, True)
            assert replay_allocation(arrivals, trailing, boundaries, causal) == optimum
            assert optimum <= allowed and (not lower or price(lower) > allowed)
            result = {
                "smallest_working_maximum_block": upper,
                "cost_at_transition": optimum,
                "one_fewer_cost": price(lower) if lower else None,
                "one_optimal_partition_blocks": len(boundaries),
            }
            if show_partitions:
                result["boundary_arrival_indices"] = [b for _, b in boundaries]
            spans = sorted({1, 2, 4, 8, upper})
        else:
            result = {}
            spans = [1, 4, 16]
        result["within_block"] = "causal" if causal else "all cells of block available immediately"
        result["measured_minima"] = {str(i): price(i) for i in spans}
        rows.append(result)
    return {
        "j": j,
        "n": n,
        "x": x,
        "last_cut": m,
        "prime_count": count,
        "allowed_buffer": allowed,
        "shared_causal_minimum": max(prefix),
        "terminal_signed_error": last,
        "first_multiple_only_failure": factor,
        "models": rows,
    }


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--heads", type=int, nargs="+", default=[4, 5])
    cli.add_argument(
        "--show-partitions",
        action="store_true",
        help="include all optimizing block endpoints for the transition boards",
    )
    args = cli.parse_args()
    if any(j < 4 for j in args.heads):
        cli.error("the first active board has index four")
    print(
        json.dumps(
            {
                "exhaustive_toy_cases": toy_controls(),
                "ten_arrivals": ten_arrivals(),
                "boards": [run(j, j <= 5, args.show_partitions) for j in sorted(set(args.heads))],
            },
            indent=2,
        )
    )
