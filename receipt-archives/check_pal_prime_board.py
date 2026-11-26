"""Price the prime-distance board, its two-cell return, and the first local storage failures."""

import argparse
from bisect import bisect_right
from fractions import Fraction
from functools import lru_cache
from math import factorial, isqrt
import json

from check_pal_dyson_window import (
    SCALE,
    ZERO,
    plus,
    minus,
    natural,
    interval_text,
    log_int,
    prime_data,
)


@lru_cache(maxsize=200000)
def logn(n):
    return log_int(n)


def normalize(lo, hi, e, bits):
    cut = max(0, hi.bit_length() - bits)
    return lo >> cut, (hi + (1 << cut) - 1) >> cut, e + cut


def product(a, b, bits):
    return normalize(a[0] * b[0], a[1] * b[1], a[2] + b[2], bits)


def power(n, k, bits):
    value = (1, 1, 0)
    b = normalize(n, n, 0, bits)
    while k:
        if k % 2:
            value = product(value, b, bits)
        k //= 2
        if k:
            b = product(b, b, bits)
    return value


def compare(a, b):
    # Compare endpoint mantissas using their exact exponents; a large separation needs no shift.
    def order(x, ex, y, ey):
        z = x.bit_length() + ex - y.bit_length() - ey
        if z:
            return 1 if z > 0 else -1
        k = min(ex, ey)
        return (x << (ex - k)) - (y << (ey - k))

    if order(a[1], a[2], b[0], b[2]) < 0:
        return -1
    if order(a[0], a[2], b[1], b[2]) > 0:
        return 1
    return 0


def leading_bits(n, primes, bits=160):
    edges = 2 * sum(n - p for p in primes if p < n)
    board = power(n, n * n, bits)
    perms = power(factorial(n), n, bits)
    ideal = perms
    local = power(n, n * n - edges, bits)
    paired = power(n, n * n - 2 * edges, bits)
    for p in primes:
        if p >= n:
            break
        k = 2 * (n - p)
        ideal = product(ideal, power(p, k, bits), bits)
        local = product(local, power(n // p, k, bits), bits)
        paired = product(paired, power(n * n // p, k, bits), bits)
    return {
        "n": n,
        "mantissa_bits": bits,
        "ideal_capacity_vs_demand": compare(board, ideal),
        "single_cell_capacity_vs_permutations": compare(local, perms),
        "paired_capacity_vs_permutations": compare(paired, perms),
        "bits_needed_by_demand": ideal[0].bit_length() + ideal[2],
        "bits_in_board_count": board[0].bit_length() + board[2],
    }


def permutation_rank(row):
    unused = list(range(len(row)))
    rank = 0
    for v in row:
        at = unused.index(v)
        rank = rank * len(unused) + at
        unused.pop(at)
    return rank


def permutation_unrank(n, rank):
    digits = []
    for radix in range(1, n + 1):
        rank, digit = divmod(rank, radix)
        digits.append(digit)
    if rank:
        raise ValueError("rank outside the permitted permutations")
    unused = list(range(n))
    return tuple(unused.pop(d) for d in reversed(digits))


def layout(n):
    flags, _ = prime_data(n)
    wires = []
    free = []
    for i in range(n):
        for j in range(n):
            p = abs(i - j)
            cell = n * i + j
            if flags[p]:
                wires.append((cell, p))
            else:
                free.append(cell)
    assert len(wires) <= len(free)
    return [(cell, free[k], p) for k, (cell, p) in enumerate(wires)], free[len(wires) :]


def encode(n, rows, digits):
    pairs, other = layout(n)
    if len(rows) != n or len(digits) != len(pairs):
        raise ValueError("wrong input shape")
    rank = 0
    for row in rows:
        if sorted(row) != list(range(n)):
            raise ValueError("row is not a permutation")
        rank = rank * factorial(n) + permutation_rank(row)
    board = [0] * (n * n)
    for (a, b, p), d in zip(pairs, digits):
        if not 0 <= d < p:
            raise ValueError("bad prime digit")
        rank, extra = divmod(rank, n * n // p)
        board[a], board[b] = divmod(p * extra + d, n)
    for a in other:
        rank, board[a] = divmod(rank, n)
    if rank:
        raise ValueError("insufficient board capacity")
    return tuple(board)


def decode(n, board):
    if len(board) != n * n or any(not 0 <= v < n for v in board):
        raise ValueError("bad board")
    pairs, other = layout(n)
    radices = []
    digits = []
    for a, b, p in pairs:
        extra, digit = divmod(n * board[a] + board[b], p)
        if extra >= n * n // p:
            raise ValueError("unassigned two-cell state")
        radices.append((n * n // p, extra))
        digits.append(digit)
    radices.extend((n, board[a]) for a in other)
    rank = 0
    for base, v in reversed(radices):
        rank = rank * base + v
    rows = []
    for _ in range(n):
        rank, row = divmod(rank, factorial(n))
        rows.append(permutation_unrank(n, row))
    if rank:
        raise ValueError("unassigned permutation rank")
    return tuple(reversed(rows)), tuple(digits)


def codec_control():
    from itertools import permutations, product as choices

    perms = list(permutations(range(3)))
    seen = set()
    for rows in choices(perms, repeat=3):
        for digits in choices(range(2), repeat=2):
            tape = encode(3, rows, digits)
            assert decode(3, tape) == (rows, digits) and tape not in seen
            seen.add(tape)
    rows = ((2, 0, 1), (0, 1, 2), (1, 2, 0))
    digits = (0, 1)
    example = encode(3, rows, digits)
    return {
        "exhaustive_size": 3,
        "distinct_encoded_inputs": len(seen),
        "total_board_states": 3**9,
        "rows": rows,
        "dial_digits": digits,
        "encoded_row_major": example,
        "decoded_again": decode(3, example),
    }


def loss_constant(cut=100000):
    # On t in (1/(k+1),1/k], the cost is -log(t)-log(k).
    subtotal = ZERO
    for k in range(2, cut + 1):
        d = minus(logn(k), logn(k - 1))
        coef = 2 * k - 1
        subtotal = plus(subtotal, (coef * d[0] // (k * k), -(-coef * d[1] // (k * k))))
    # (2/k-1/k^2)*[-log(1-1/k)] is between 2/k^2 and 2/k^2+2/k^4.
    low = Fraction(3, 2) - Fraction(subtotal[1], SCALE) - Fraction(2, cut) - Fraction(2, 3 * cut**3)
    high = Fraction(3, 2) - Fraction(subtotal[0], SCALE) - Fraction(2, cut + 1)
    return interval_text((low * SCALE // 1, -(-high * SCALE // 1)), 9)


def initial_prime_areas(x=3000):
    flags, _ = prime_data(x)
    theta = ZERO
    psi = ZERO
    for prime in range(2, x + 1):
        if not flags[prime]:
            continue
        log_prime = logn(prime)
        theta = plus(theta, natural(x - prime, log_prime))
        power_of_prime = prime
        while power_of_prime <= x:
            psi = plus(psi, natural(x - power_of_prime, log_prime))
            power_of_prime *= prime
    center = (SCALE * (x * x - 4) // 2,) * 2
    theta_error = minus(theta, center)
    psi_error = minus(psi, center)
    if x == 3000:
        assert -140000 * SCALE < theta_error[0] <= theta_error[1] < -130000 * SCALE
        assert -2900 * SCALE < psi_error[0] <= psi_error[1] < -2800 * SCALE
    return {
        "x": x,
        "integral_theta_minus_t": interval_text(theta_error, 8),
        "integral_psi_minus_t": interval_text(psi_error, 8),
        "integral_repeated_powers": interval_text(minus(psi, theta), 8),
    }


def audit(limit=100000, local_through=5000):
    prime, _ = prime_data(limit)
    primes = [p for p in range(2, limit + 1) if prime[p]]
    pref = [0]
    for p in primes:
        pref.append(pref[-1] + p)
    total = area = logfac = ZERO
    first_local = None
    first_small = None
    last_upper_failure = None
    last_lower_failure = None
    examples = []
    control_heads = {2, 3, 4, 7, 16, 49, 577, 1562, 1563, 2663, 4242, 4243, 5000, 10000, limit}
    for n in range(1, limit + 1):
        log = logn(n)
        area = plus(area, total)
        logfac = plus(logfac, log)
        k = bisect_right(primes, n)
        edges = 2 * (n * k - pref[k])
        if prime[n]:
            total = plus(total, log)
        if n == 1:
            continue
        gap = minus(minus(natural(n * n, log), natural(n, logfac)), natural(2, area))
        assert 2 * edges <= n * n
        # One auxiliary cell makes the total loss at most edges/n in natural logarithm units.
        if gap[0] * n <= edges * SCALE:
            last_upper_failure = n
        if gap[1] >= 4 * n * (isqrt(n) + 1) * logn(2)[0]:
            last_lower_failure = n
        if n <= 3000:
            assert gap[0] * n > edges * SCALE
        khalf = bisect_right(primes, n // 2)
        big = 2 * ((k - khalf) * n - (pref[k] - pref[khalf]))
        small = n * isqrt(2 * n - 1)
        if first_small is None and big > small:
            first_small = [n, big, small]
        if n <= local_through or n in control_heads:
            local = minus(natural(n * n - edges, log), natural(n, logfac))
            nonprime = n * n - 2 * edges
            h = 1
            while h <= n:
                v = n // h
                end = n // v
                i = bisect_right(primes, h - 1)
                jj = bisect_right(primes, end)
                multiplicity = 2 * ((jj - i) * n - (pref[jj] - pref[i]))
                if multiplicity:
                    local = plus(local, natural(multiplicity, logn(v)))
                h = end + 1
            assert local[1] < 0 or local[0] > 0
            if local[1] < 0 and first_local is None:
                first_local = n
            if n in control_heads:
                pair = minus(natural(nonprime, log), natural(n, logfac))
                for p in primes[:k]:
                    pair = plus(pair, natural(2 * (n - p), logn(n * n // p)))
                examples.append(
                    {
                        "n": n,
                        "prime_distance_cells": edges,
                        "ideal_log_margin": interval_text(gap, 6),
                        "single_cell_log_margin": interval_text(local, 6),
                        "paired_log_margin": interval_text(pair, 6),
                        "large_prime_blocks": big,
                        "available_small_lehmer_digits": small,
                    }
                )
    assert last_upper_failure is None and last_lower_failure is None
    check = [
        leading_bits(n, primes)
        for n in [2, 3, 49, 577, 1563, 2663, 4242, 4243, 10000]
        if n <= limit
    ]
    assert all(
        v["ideal_capacity_vs_demand"] == 1 and v["paired_capacity_vs_permutations"] == 1
        for v in check
    )
    for z in check:
        row = next(x for x in examples if x["n"] == z["n"])
        assert z["single_cell_capacity_vs_permutations"] == (
            1 if Fraction(row["single_cell_log_margin"][0]) > 0 else -1
        )
    return {
        "ideal_and_pair_bound_through": limit,
        "single_cell_exhaustive_through": local_through,
        "first_single_cell_failure": first_local,
        "first_large_block_pigeonhole": first_small,
        "last_unproved_pair_from_loss_allowance": last_upper_failure,
        "last_unproved_binary_allowance": last_lower_failure,
        "examples": examples,
        "initial_integrals": initial_prime_areas(),
        "codec": codec_control(),
        "independent_leading_bit_comparisons": check,
        "single_cell_asymptotic_loss_constant": loss_constant(),
    }


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--limit", type=int, default=100000)
    cli.add_argument("--local-through", type=int, default=5000)
    args = cli.parse_args()
    if args.limit < 2 or not 2 <= args.local_through <= args.limit:
        cli.error("require 2 <= local-through <= limit")
    print(json.dumps(audit(args.limit, args.local_through), indent=2))
