"""Exact whole-board square-root transports, prime switches and positive ruler fits."""

import json
from fractions import Fraction as F
from itertools import accumulate
from math import isqrt

from check_pal_doubled_ruler import q, stop
from check_pal_dyson_window import prime_data
from check_pal_growing_brackets import enclosure, mobius


def square_signs(a, primes):
    mask = 0
    for i, p in enumerate(primes):
        while a % p == 0:
            a //= p
            mask ^= 1 << i
    return mask


def whole_board(n, all_choices=True, chosen=(2, 3, 5, 7, 11, 13, 17)):
    """Switches are signs. Unvaried primes have switch +1. Every sign is fixed over the board."""
    flags, _ = prime_data(max(2, isqrt(n - 1)))
    roots = [p for p in range(2, len(flags)) if flags[p]]
    primes = roots if all_choices else [p for p in chosen if p in roots]
    mu = mobius(n)
    original = [0, *accumulate(mu[1:n])]
    steps = [0] * n
    owners = [[] for _ in primes]
    marks = [0] * (isqrt(n - 1) + 1)
    for a in range(1, len(marks)):
        mask = square_signs(a, primes)
        marks[a] = mask
        for d in range(1, (n - 1) // (a * a) + 1):
            if not mu[d]:
                continue
            j = a * a * d
            assert steps[j] == 0
            steps[j] = mu[d]
            for i in range(len(primes)):
                if mask & (1 << i):
                    owners[i].append(j)
    assert all(abs(z) == 1 for z in steps[1:])
    all_positive_steps = steps[:]
    old = 0
    best = None
    fixed = {}
    base = None
    positive_min = None
    negative_min = None
    for j in range(1 << len(primes)):
        gray = j ^ (j >> 1)
        if j:
            changed = (old ^ gray).bit_length() - 1
            for idx in owners[changed]:
                steps[idx] = -steps[idx]
        old = gray
        walk = list(accumulate(steps))
        unsigned = sum(map(abs, walk))
        signed = sum(walk)
        pos = (unsigned + signed) // 2
        neg = (unsigned - signed) // 2
        assert pos + neg == unsigned
        if not j:
            base = [pos, neg]
        option = (min(pos, neg), gray, 1 if pos <= neg else -1)
        if best is None or option < best:
            best = option
        positive_min = pos if positive_min is None else min(positive_min, pos)
        negative_min = neg if negative_min is None else min(negative_min, neg)
        if 17 in primes:
            side = (gray >> primes.index(17)) & 1
            if side not in fixed or option < fixed[side]:
                fixed[side] = option
    cost, mask, orientation = best
    # Independently rebuild the chosen stream by summing whole smaller Mobius walks.
    cuts = sorted(
        {1, min(17, n - 1), n // 2, n - 1, *(range(1, n) if n <= 2048 else ())}
    )
    for v in cuts:
        amt = sum(
            (-1) ** ((mask & m).bit_count()) * original[v // (a * a)]
            for a, m in enumerate(marks[1 : isqrt(v) + 1], 1)
        )
        direct = (
            sum(
                all_positive_steps[k]
                * (-1) ** ((mask & marks[square_part(k)]).bit_count())
                for k in range(1, v + 1)
            )
            if len(cuts) < 10
            else None
        )
        if direct is not None:
            assert amt == direct
    bsteps = all_positive_steps[:]
    for i, xs in enumerate(owners):
        if (mask >> i) & 1:
            for idx in xs:
                bsteps[idx] = -bsteps[idx]
    computed = list(accumulate(bsteps))
    assert sum(max(orientation * x, 0) for x in computed) == cost
    for v in cuts:
        assert computed[v] == sum(
            (-1) ** ((mask & marks[a]).bit_count()) * original[v // (a * a)]
            for a in range(1, isqrt(v) + 1)
        )
    return {
        "head": n,
        "variables": primes,
        "all_open_prime_signs_varied": all_choices,
        "configurations": 1 << len(primes),
        "all_plus_areas": base,
        "best_area": cost,
        "best_by_side": [positive_min, negative_min],
        "chosen_orientation": orientation,
        "negative_prime_switches": [p for i, p in enumerate(primes) if mask >> i & 1],
        "best_with_17_positive_or_negative": {
            str(1 - 2 * i): row[0] for i, row in fixed.items()
        },
        "normalized_cost_squared": str(F(cost**2, n**3)),
    }


def square_part(n):
    # Used only in the independent small set of direct path reconstructions.
    root = 1
    p = 2
    while p * p <= n:
        while n % (p * p) == 0:
            root *= p
            n //= p * p
        p += 1
    return root


def turns(n, full):
    y = full[:n]
    squares = sum(x * x for x in y)
    rows = []
    for a in range(2, 18):
        par = [a * y[x // (a * a)] for x in range(n)]
        dot = sum(v * w for v, w in zip(y, par))
        pp = sum(w * w for w in par)
        use = min(F(1), max(F(-1), F(dot, pp))) if pp else F(0)
        err = squares - 2 * use * dot + use * use * pp
        rows.append((err, a, use, squares - 2 * dot + pp))
    z = rows[-1]
    win = min(rows)
    return {
        "head": n,
        "uncorrected": str(F(squares, n * n)),
        "fixed_17": str(F(z[3], n * n)),
        "optimized_single_17": str(z[0] / n**2),
        "signed_17_coefficient": str(z[2]),
        "best_individual_scale": win[1],
        "best_individual_coefficient": str(win[2]),
        "best_individual": str(win[0] / n**2),
    }


def w(v):
    return F(0) if v > 1 else stop(F(v))


def brackets(N, mu, M):
    assert N % 2 == 0
    L = F(sum(abs(v) for v in M[:N]), N)
    guard = F(64, 5) * (1 + L)
    area = sum(F(mu[j], 7) * (F(1, j) - F(1, N)) for j in range(1, N))
    width = 4 * guard / (7 * N)
    for t in (F(1, 2 * N), F(1, N), F(2, N), F(3, 2 * N), F(1), F(1, 3), F(4, 7)):
        val = sum(mu[j] * (w(j * t) - w(N * t)) for j in range(1, N))
        target = q(t)
        assert val - guard * w(N * t / 2) <= target <= val + guard * w(N * t / 2)
        if t >= F(1, N):
            assert val == target
    assert area - width / 2 <= 0 <= area + width / 2
    return {
        "even_head": N,
        "mean_absolute_mobius": str(L),
        "rational_guard": str(guard),
        "signed_integral_outward": enclosure(area, area),
        "total_bracket_width": str(width),
    }


def audit():
    N = 2**18
    mu = mobius(N)
    M = [0, *accumulate(mu[1:])]
    # The freedom to read the current answer as a fresh per-row coefficient
    # vacates the test through this actual range.
    assert all(
        abs(M[n]) <= isqrt(n) and M[n // isqrt(n) ** 2] == 1 for n in range(9, N + 1)
    )
    assert 2 * w(F(2, 3)) == F(22, 729)
    return {
        "all_sign_choices": [whole_board(n) for n in (290, 867, 1933)],
        "fixed_seven_prime_catalog": [
            whole_board(n, False) for n in (4096, 16384, 65536)
        ],
        "single_parents": [
            turns(n, M) for n in (289, 1024, 1933, 4096, 16384, 65536, 83521, N)
        ],
        "rowwise_zero_residual_through": N,
        "positive_brackets": [brackets(k, mu, M) for k in (34, 128, 512, 1024)],
        "wrong_unsigned_balance_at_3": str(F(22, 729)),
        "units": "one-side areas are integer sums over n=0,...,N-1. Parent energy ratios are sums of squared residuals divided by N^2.",
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
