"""Compare erasing five as a distance and as a sieve factor using directed arithmetic."""

from functools import lru_cache
from math import factorial, gcd, isqrt, prod
import json

from check_pal_dyson_window import (
    SCALE,
    ZERO,
    interval_text,
    log_int,
    natural,
    plus,
    minus,
    prime_data,
)
from check_pal_prime_board import layout, encode, decode


@lru_cache(maxsize=120000)
def log_number(value):
    return log_int(value)


def upper_cut(n):
    bits = n.bit_length()
    return -(-3 * n // bits**3)


def exact_demands(n, q):
    root = isqrt(n)
    flags, _ = prime_data(root)
    frame = prod(p for p in range(2, root + 1) if flags[p])
    missing = frame // q if frame % q == 0 else frame

    def demand(stamp):
        return factorial(n) ** n * prod(
            m ** (2 * (n - m)) for m in range(2, n + 1) if gcd(m, stamp) == 1
        )

    clean = demand(frame)
    altered = demand(missing)
    capacity = n ** (n * n)
    assert altered % clean == 0
    return {
        "size": n,
        "frame": frame,
        "frame_without_q": missing,
        "complete_frame_fits": clean <= capacity,
        "altered_frame_fits": altered <= capacity,
        "complete_record_count_bit_length": clean.bit_length(),
        "altered_record_count_bit_length": altered.bit_length(),
        "board_state_count_bit_length": capacity.bit_length(),
    }


def retained_tags(n, q, primes):
    if q > isqrt(n):
        return []
    tags = []
    power = q
    while power <= n:
        tags.append(power)
        for p in primes:
            if p <= isqrt(n):
                continue
            if power * p > n:
                break
            tags.append(power * p)
        power *= q
    assert len(tags) == len(set(tags))
    return sorted(tags)


def margin_and_change(n, q, primes, log_factorial, compare_gcd=False):
    root = isqrt(n)
    retained = [p for p in primes if root < p <= n]
    genuine = ZERO
    for p in retained:
        genuine = plus(genuine, natural(2 * (n - p), log_number(p)))
    margin = minus(minus(natural(n * n, log_number(n)), natural(n, log_factorial)), genuine)
    tags = retained_tags(n, q, primes)
    if compare_gcd:
        stamp = prod(p for p in primes if p <= root)
        weakened = stamp // q if stamp % q == 0 else stamp
        assert tags == [m for m in range(2, n + 1) if gcd(m, weakened) == 1 and gcd(m, stamp) != 1]
    added = ZERO
    for m in tags:
        added = plus(added, natural(2 * (n - m), log_number(m)))
    return margin, added, tags


def all_scale_constants():
    # Check the endpoint arithmetic used in the monotone bounds for larger sizes.
    base = 10**9
    small = 90000
    log_base = log_number(base)
    log_small = log_number(small)
    log_two = log_number(2)
    assert 20 * SCALE < log_base[0] <= log_base[1] < 21 * SCALE
    assert 69 * SCALE < 100 * log_two[0]
    assert 2 * log_small[1] * 1000 < 77 * SCALE * isqrt(small)
    assert 1000 * log_number(small + 1)[1] < small * SCALE
    assert 8 * base > 9 * small * 21**3
    assert 1000 * (2 + 21) * 21**3 < base
    assert 156 * 100 < 85 * 185
    assert 2 * 99 * 3 * 8 > 105 * 5 * 9
    return {
        "base": base,
        "small_theta_threshold": small,
        "outer_cut_examples": [
            [n, n.bit_length(), isqrt(n), upper_cut(n)]
            for n in (81, 256, 2663, 10**9, 10**12, 10**24)
        ],
    }


def orientations():
    cases = []
    for n, cut in [(3, 0), (3, 1), (4, 2), (5, 2), (7, 4), (16, 4), (16, 8)]:
        rows = tuple(tuple((i + j) % n for i in range(n)) for j in range(n))
        pairs, _ = layout(n, cut)
        dials = tuple((r + a + b) % p for r, (a, b, p) in enumerate(pairs))
        tape = encode(n, rows, dials, cut)
        assert decode(n, tape, cut) == (rows, dials)
        cases.append(
            {"n": n, "cut": cut, "recovered_rows": len(rows), "recovered_dials": len(dials)}
        )
    return cases


def audit():
    flags, _ = prime_data(65536)
    primes = [p for p in range(2, len(flags)) if flags[p]]
    heads = {25, 81, 246, 247, 248, 256, 625, 2663, 10000, 65536}
    rows = []
    first = None
    log_factorial = ZERO
    for n in range(1, max(heads) + 1):
        log_factorial = plus(log_factorial, log_number(n))
        if n > 256 and n not in heads:
            continue
        good, extra, ghosts = margin_and_change(n, 5, primes, log_factorial, n <= 2663)
        altered = minus(good, extra)
        if n > 1:
            assert good[0] > 0 and (altered[0] > 0 or altered[1] < 0)
        if altered[1] < 0 and first is None:
            first = n
        if n in heads:
            per_square = extra[0] // (n * n), -(-extra[1] // (n * n))
            row = {
                "n": n,
                "complete_log_margin": interval_text(good, 6),
                "altered_log_margin": interval_text(altered, 6),
                "price_of_missing_frame_five": interval_text(extra, 6),
                "extra_price_per_n_squared": interval_text(per_square, 8),
                "price_of_ordinary_five_dials": interval_text(
                    natural(2 * max(n - 5, 0), log_number(5)), 6
                ),
                "new_distance_count": len(ghosts),
            }
            if n <= 256:
                row["new_distances"] = ghosts
            rows.append(row)
    checks = [exact_demands(n, 5) for n in (25, 81, 246, 247, 256, 625)]
    assert first == 247 and all(x["complete_frame_fits"] for x in checks)
    assert [x["altered_frame_fits"] for x in checks] == [True, True, True, False, False, False]
    return {
        "all_sizes_through_first_failure": first,
        "ordinary_five_change": "2*(n-5)*log(5) for n>=5",
        "erased_frame_five_asymptotic_extra_nats_per_n_squared": "1/4",
        "heads": rows,
        "exact_integer_controls": checks,
        "decoder": orientations(),
        "all_size_outer_board": all_scale_constants(),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
