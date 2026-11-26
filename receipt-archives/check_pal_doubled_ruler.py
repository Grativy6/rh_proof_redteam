"""Integer and directed-log replay of the doubled ruler and its seven-eighths cutoff."""

from bisect import bisect_right
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt
import json

from check_pal_crossing_refund import HEIGHT, ORDINATE_MASS, SHORT_WIDTH, HIGH_FACTOR, SHORT_PASSES
from check_pal_dyson_window import SCALE, log_int, prime_data
from check_pal_moving_endpoint import upper_text


def extra(n, d):
    N = 2 * n
    if d > N:
        return 0
    if d > n:
        return (N - d) ** 5 * (7 * d - N)
    m, r = divmod(N, d)
    numerator = (
        d**6 * m * (4 * m * m - 1)
        + 12 * r * d**5 * m * m
        + 15 * m * r * r * d * d * (d * d - r * r)
        + 6 * m * r**5 * (3 * d - r)
        + 3 * r**5 * (2 * d - r)
    )
    out, remainder = divmod(numerator, 6)
    assert remainder == 0 and out >= 0
    return out


def q(u):
    return (1 - u) ** 5 * (7 * u - 1)


def stop(v):
    """E(V-v)_+ for rational v in [0,1]. V is half the endpoint factor."""
    if v == 0:
        return F(1, 2)
    a, b = v.numerator, v.denominator
    # The polynomial sum is evaluated by the six-power remainder formula.
    m, r = divmod(b, a)
    six_residual = (
        a**6 * m * (4 * m * m - 1)
        + 12 * r * a**5 * m * m
        + 15 * m * r * r * a * a * (a * a - r * r)
        + 6 * m * r**5 * (3 * a - r)
        + 3 * r**5 * (2 * a - r)
    )
    return F(1, 2) - v + F(six_residual, 6 * b**6)


def three_halves(steps):
    # Convex interpolation of v^(3/2) on the rational knots (i/steps)^2.
    total = F(0)
    previous_slope = F(0)
    for i in range(steps):
        slope = F((i + 1) ** 3 - i**3, steps * ((i + 1) ** 2 - i * i))
        total += (slope - previous_slope) * stop(F(i * i, steps * steps))
        previous_slope = slope
    unit = 10**12
    root_upper = F(isqrt(2 * unit**2) + 1, unit)
    return 2 * root_upper * total


def small_ledger():
    for n in range(1, 65):
        N = 2 * n
        flags, powers = prime_data(N)
        for d in range(1, N + 2):
            signed = sum((N - m) ** 5 * (7 * m - N) for m in range(d, N + 1, d))
            assert extra(n, d) == signed - N**5 * max(0, n - d)
        ordinary_exponents = {}
        for m in range(2, N + 1):
            rest = m
            for p in range(2, m + 1):
                while rest % p == 0:
                    ordinary_exponents[p] = ordinary_exponents.get(p, 0) + (N - m) ** 5 * (
                        7 * m - N
                    )
                    rest //= p
                if rest == 1:
                    break
        for prime in range(2, N + 1):
            if not flags[prime]:
                continue
            # Each log prime is its own independent formal symbol.
            powers_list = [prime]
            while powers_list[-1] * prime <= N:
                powers_list.append(powers_list[-1] * prime)
            raw = sum(N**5 * max(0, n - d) + extra(n, d) for d in powers_list)
            assert raw == ordinary_exponents[prime]
        assert all(p <= N for p in powers)
    for d in range(1, 51):
        v = F(d, 51)
        assert stop(v) == sum(q(j * v) for j in range(1, 51 // d + 1))
    return {
        "all_address_formulas_and_labelled_divisor_regroupings_through_n": 64,
        "extra_n2_in_label_order": [extra(2, d) for d in range(1, 5)],
        "denominator_at_two": 4**5,
        "boundary_mass_at_mesh_16": str(F(sum(j**6 for j in range(16)), 16**7)),
    }


def margin_text(q, up):
    scale = 10**10
    k = -(-q.numerator * scale // q.denominator) if up else q.numerator * scale // q.denominator
    sign = "-" if k < 0 else ""
    a = abs(k)
    return f"{sign}{a // scale}.{a % scale:010d}"


def small_comparisons(max_root):
    top = 2 * max_root**4
    flags, _ = prime_data(top)
    primes = [d for d in range(2, top + 1) if flags[d]]
    stored_log = lru_cache(maxsize=None)(log_int)
    examples = {}
    failures = []
    smallest = None
    for k in range(1, max_root + 1):
        n = k**4
        N = 2 * n
        lo = hi = 0
        kept = 0
        for idx in range(bisect_right(primes, N)):
            prime = primes[idx]
            if prime**8 <= n**7:
                continue
            kept += 1
            weight = extra(n, prime)
            lower, upper = stored_log(prime)
            lo += weight * lower
            hi += weight * upper
        ticks = N**5 * n * (n - k**2) ** 2
        nlo, nhi = stored_log(n)
        n1lo, n1hi = stored_log(n + 1)
        margin_low = 14 * lo - ticks * (n1hi - nlo)
        margin_high = 14 * hi - ticks * (n1lo - nhi)
        assert margin_low >= 0 or margin_high < 0, k
        if margin_high < 0:
            failures.append(k)
        unit = 14 * SCALE * N**5 * k**6
        low, high = F(margin_low, unit), F(margin_high, unit)
        if smallest is None or low < smallest[0]:
            smallest = (low, k)
        if k in (1, 2, 3, 5, 16, max_root):
            examples[str(k)] = {
                "n": n,
                "kept_primes": kept,
                "normalized_log_margin": [margin_text(low, False), margin_text(high, True)],
            }
    assert not failures, failures
    return {
        "checked_root_range": [1, max_root],
        "strict_failures": failures,
        "examples": examples,
        "smallest_lower_margin_at": smallest[1],
    }


def intermediate_range(first=25, last=512):
    """Count every repeated power, and price earlier first powers by their cubic moment."""
    upper_prime = max(2**19, isqrt(2 * last**4))
    flags, _ = prime_data(upper_prime)
    primes = [p for p in range(2, upper_prime + 1) if flags[p]]
    logs = [log_int(p)[1] for p in primes]
    moments = [0]
    for p, lp in zip(primes, logs):
        moments.append(moments[-1] + p**3 * lp)
    ambiguous = []
    worst = (F(0), 0)
    for k in range(first, last + 1):
        n = k**4
        N = 2 * n
        D = isqrt(isqrt(isqrt(n**7)))
        assert D**8 <= n**7 < (D + 1) ** 8
        if D <= upper_prime:
            low_primes = F(2 * moments[bisect_right(primes, D)], 3 * SCALE * N**2 * k**6)
        else:
            assert 599 < D < 10**26
            ell = F(log_int(D)[1], SCALE)
            ratio = F(1, 4) + F(13, 7) * ell**2 / (24 * isqrt(D)) + 2 * ell / D + 3 * F(599, D) ** 4
            low_primes = ratio / 6
        repeats = 0
        for idx in range(bisect_right(primes, isqrt(N))):
            p = primes[idx]
            d = p * p
            while d <= N:
                repeats += extra(n, d) * logs[idx]
                d *= p
        spent = (
            F(4622, 100000)
            + F(repeats, SCALE * N**5 * k**6)
            + low_primes
            + F(4 * 14 + 1, 14 * k * k)
        )
        if spent > worst[0]:
            worst = (spent, k)
        if spent >= F(1, 7):
            ambiguous.append(k)
    assert not ambiguous, ambiguous
    return {
        "root_range": [first, last],
        "insufficient_upper_bounds": ambiguous,
        "largest_upper_bound_at": worst[1],
        "largest_upper_bound": upper_text(worst[0]),
    }


def middle_slabs(moment):
    # Throughout 2^36 <= n <= 2^120 use the largest contribution at the
    # left endpoint for each square, higher-power and low-prime error bound.
    v = SHORT_PASSES * SHORT_WIDTH**2 / 3
    root = 2**60
    raw = (
        F(root, 2) * v / (1 - v) + ORDINATE_MASS + F(10 * root, HEIGHT) * HIGH_FACTOR**SHORT_PASSES
    )
    assert raw < F(4622, 100000)
    square_sup = max(F(599, 2**18), F(6, 5) * 13**2 / (24 * 512) + F(13, 2**18))
    square = F(2, 3) * (moment - 1) + F(5, 16) * square_sup
    assert 5162**3 > 2**37 and 610**4 > 2**37 and 170**5 > 2**37
    higher = F(5, 32) * F(7, 5) * F(5162 + 610 + 37 * 170, 2**18)
    # The theta estimate of Johnston decreases above 2^26 in relative units.
    # 26 log(2)<18.2, and the FKS row at e^50 overlaps the finite theorem.
    assert F(182, 10) ** 2 / (24 * 2**13) + F(182, 10 * 2**26) < F(2, 1000)
    mass3 = F(1, 4) + F(7, 4) * F(2, 1000) + F(3, 2**20)
    small = mass3 / 6
    fee = F(4 * 14 + 1, 14 * 2**18)
    total = raw + square + higher + small + fee
    assert total < F(1, 7)
    return {
        "board_interval": [2**36, 2**120],
        "square_return_upper": upper_text(square),
        "higher_return_upper": upper_text(higher),
        "raw_upper": upper_text(raw),
        "removed_primes_upper": upper_text(small),
        "all_prices_upper": upper_text(total),
    }


def late_range():
    moment = three_halves(96)
    assert moment < F(1057, 1000)
    # Spectral input from the preceding positive 21-move estimate.
    xmax = 2**144
    v = SHORT_PASSES * SHORT_WIDTH**2 / 3
    raw = (
        F(isqrt(xmax), 2) * v / (1 - v)
        + ORDINATE_MASS
        + F(10 * isqrt(xmax), HEIGHT) * HIGH_FACTOR**SHORT_PASSES
    )
    assert raw < F(585, 10000)
    # For t >= 2^80 use Johnston's theta bound at sqrt(t). The function
    # log^2(u)/sqrt(u) is decreasing here. Prime powers >= cubes add the two terms.
    assert F(28**2, 24 * 2**20) + F(28, 2**40) + F(7, 5) * (F(1, 2**13) + F(80, 2**20)) < F(1, 2000)
    # The finite Schoenfeld-shaped upper endpoint is at least 10^26.
    assert 2**73 < 10**26
    # For smaller t the elementary absolute error integrates to <2^135.
    assert (145**2 + 1) * 2**120 < 2**135
    repeated = F(2, 3) * (moment - 1) + F(2, 3 * 2000) * (moment + 1) + F(2**136, 2**180)
    assert repeated < F(389, 10000)
    # theta(u) differs from u by at most 10^-6 u for u >=2^80 (FKS, row 50).
    eps = F(1, 10**6)
    moment3 = F(1, 4) + F(7, 4) * eps + F(3 * (2**80) ** 4, (2**105) ** 4)
    assert moment3 < F(251, 1000)
    smallprimes = F(1, 6) * moment3 + F(18 * 7, 5 * 16 * 2**30)
    assert smallprimes < F(419, 10000)
    # A lower estimate on the signed ordinary-integer quadrature, including
    # n/14 from the exact square frame, in units of the original n^(3/2).
    quadrature = F(64 * (1 + 145) + 1, 2**60)
    assert raw + repeated + smallprimes + quadrature < F(1, 7)
    return {
        "nominal_board_interval": [2**120, 2**144],
        "all_fourth_power_indices": [2**30, 2**36],
        "moment_3_over_2_upper": upper_text(moment),
        "raw_area_excess_upper": upper_text(raw),
        "repeat_return_upper": upper_text(repeated),
        "removed_initial_primes_upper": upper_text(smallprimes),
        "ordinary_sum_and_clock_rounding_upper": upper_text(quadrature),
        "total_fraction_of_n_to_three_halves_upper": upper_text(
            raw + repeated + smallprimes + quadrature
        ),
        "available_fraction": "1/7",
    }


def audit():
    n = 2**36
    assert 2**26 <= F(4, 1000) * n
    assert (F(1, 14) - F(1, 800) - F(1, 4 * isqrt(n))) * 15 > 1
    assert (F(1, 14) + F(1, 800)) * 13 < F(95, 100)
    assert F(n, n + 1) * (1 - F(1, isqrt(n))) ** 2 > F(99, 100)
    return {
        "fifteen_copies": "all positive fourth-power indices",
        "thirteen_fail_for_all_indices_at_least": 512,
        "small_ledger": small_ledger(),
        "early_clock": small_comparisons(24),
        "late_clock": late_range(),
        "middle_clock": middle_slabs(three_halves(96)),
        "intermediate_clock": intermediate_range(),
        "variance_of_endpoint": "1/7",
        "continuum_charge_per_n_squared": "1/14",
        "critical_removal_exponent": "7/8",
        "cost_at_that_cut_per_n_to_three_halves": "1/24",
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
