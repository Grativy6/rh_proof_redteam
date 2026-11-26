"""Certify all prime-board sizes between sparse anchors using convexity of the prime area."""

import argparse
import hashlib
import json
from math import isqrt

from check_pal_dyson_window import SCALE, interval_text, log_int, prime_data
from check_pal_prime_board import audit as initial_boards


def anchors(first, last):
    result = [first]
    while result[-1] < last:
        n = result[-1]
        step = max(1, isqrt(n * isqrt(n)) // 2)
        result.append(min(last, n + step))
    return result


def segmented_readings(heads, segment_width=1 << 20):
    """Enclose theta and sum p log p by counts on short, disjoint integer intervals."""
    last = heads[-1]
    small, _ = prime_data(isqrt(last))
    primes = [p for p in range(2, len(small)) if small[p]]
    theta_lo = theta_hi = weighted_lo = weighted_hi = 0
    count = pos = bins = 0
    target = 0
    for start in range(2, last + 1, segment_width):
        stop = min(start + segment_width, last + 1)
        flags = bytearray([1]) * (stop - start)
        for prime in primes:
            if prime * prime >= stop:
                break
            first = max(prime * prime, -(-start // prime) * prime)
            if first < stop:
                flags[first - start :: prime] = bytes((stop - 1 - first) // prime + 1)

        pos = start
        while pos < stop:
            end = min(stop - 1, heads[target], pos + max(1, isqrt(pos) // 12) - 1)
            hits = flags.count(1, pos - start, end + 1 - start)
            if hits:
                low = log_int(pos)[0]
                high = log_int(end)[1]
                theta_lo += hits * low
                theta_hi += hits * high
                weighted_lo += hits * pos * low
                weighted_hi += hits * end * high
                count += hits
            bins += 1
            if end == heads[target]:
                yield {
                    "n": end,
                    "pi": count,
                    "bins": bins,
                    "theta": (theta_lo, theta_hi),
                    "P": (
                        end * end * SCALE - 2 * (end * theta_hi - weighted_lo),
                        end * end * SCALE - 2 * (end * theta_lo - weighted_hi),
                    ),
                }
                target += 1
            pos = end + 1


def division_prime_count(n):
    """Independent integer sieve on the distinct quotients floor(n/i)."""
    root = isqrt(n)
    large = [n // i for i in range(1, root + 1)]
    values = large + list(range(large[-1] - 1, 0, -1))
    remaining = {v: v - 1 for v in values}
    for prime in range(2, root + 1):
        before = remaining[prime - 1]
        if remaining[prime] == before:
            continue
        for v in values:
            if v < prime * prime:
                break
            remaining[v] -= remaining[v // prime] - before
    return remaining[n]


def base_crosscheck(reading):
    n = reading["n"]
    flags, _ = prime_data(n)
    lower = upper = 0
    for p in range(2, n + 1):
        if flags[p]:
            lo, hi = log_int(p)
            lower += (n - p) * lo
            upper += (n - p) * hi
    exact_lo, exact_hi = n * n * SCALE - 2 * upper, n * n * SCALE - 2 * lower
    assert reading["P"][0] <= exact_lo <= exact_hi <= reading["P"][1]
    return interval_text((exact_lo, exact_hi), 4)


def certify(first=100000, last=10**9):
    if last <= first:
        raise ValueError("the last board must exceed the initial cutoff")
    initial_boards(first, min(5000, first))
    readings = iter(segmented_readings(anchors(first, last)))
    left = next(readings)
    small_check = base_crosscheck(left)
    log_two = log_int(2)[0]
    digest = hashlib.sha256()
    examples = []
    minimum_paid = minimum_reserve = None
    certificates = 0
    for right in readings:
        a, b = left["n"], right["n"]
        width = b - a
        # P=x^2-2*I_theta. Convexity gives the lower chord bound; the left tangent gives the upper.
        low_four = (
            4 * min(left["P"][0], right["P"][0])
            - width * width * SCALE
            - 4 * b * (SCALE + log_int(b)[1])
        )
        high = (
            left["P"][1] + 2 * width * max(0, a * SCALE - left["theta"][0]) + width * width * SCALE
        )
        reserve = 4 * a * (isqrt(a) + 1) * log_two
        assert low_four > 4 * b * SCALE, ("insufficient paired margin", a, b)
        assert high < reserve, ("excess spare capacity", a, b)
        paid = (low_four - 4 * b * SCALE) * 1000 // (4 * b * (isqrt(b) + 1) * SCALE)
        spare = (reserve - high) * 1000 // (b * (isqrt(b) + 1) * SCALE)
        if minimum_paid is None or paid < minimum_paid[0]:
            minimum_paid = (paid, a, b)
        if minimum_reserve is None or spare < minimum_reserve[0]:
            minimum_reserve = (spare, a, b)
        record = (a, b, low_four, high, reserve)
        digest.update((json.dumps(record, separators=(",", ":")) + "\n").encode())
        certificates += 1
        if certificates == 1 or b == last:
            examples.append(
                {
                    "from": a,
                    "to": b,
                    "length_including_endpoints": width + 1,
                    "lower_log_margin": interval_text((low_four // 4, low_four // 4), 3)[0],
                    "upper_log_margin": interval_text((high, high), 3)[1],
                    "binary_budget_in_nats_lower": interval_text((reserve, reserve), 3)[0],
                }
            )
        left = right
    independent = division_prime_count(last)
    assert left["pi"] == independent
    return {
        "all_positive_sizes_through": last,
        "direct_initial_sizes_through": first,
        "sparse_intervals_after_initial_range": certificates,
        "prime_bins": left["bins"],
        "prime_count_by_segmented_and_quotient_sieves": independent,
        "minimum_excess_over_paired_cost_in_thousandths_of_b_root_b": minimum_paid,
        "minimum_room_below_binary_budget_in_thousandths_of_b_root_b": minimum_reserve,
        "first_and_last_certificates": examples,
        "first_anchor_direct_P": small_check,
        "ordered_integer_certificates_sha256": digest.hexdigest(),
    }


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--limit", type=int, default=10**9)
    args = cli.parse_args()
    print(json.dumps(certify(last=args.limit), indent=2))
