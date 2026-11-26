"""Outward first-digit and discrepancy calculations for primorials and their factorial quotient."""

import argparse
import json
from fractions import Fraction as Q
from math import factorial, prod

from check_pal_dyson_window import prime_data
from pal_product_clock import LogGrid
from check_pal_returned_horizon import log_ratio_interval
from check_pal_dense_square_payment import display

UNIT = 10**15


def first_primes(n):
    top = max(16, 16 * n)
    while True:
        flags, _ = prime_data(top)
        p = [i for i in range(2, top + 1) if flags[i]]
        if len(p) >= n:
            return p[:n]
        top *= 2


def decimal_phase(log_value, log_ten, exact_ratio=None):
    lo, hi = log_value
    low_ten, high_ten = log_ten
    assert lo >= 0
    left = lo * UNIT // high_ten
    right = -(-hi * UNIT // low_ten)
    decade = left // UNIT
    if right // UNIT != decade:
        if exact_ratio is None:
            raise ValueError("an exact ratio is required at a decade boundary")
        numerator, denominator = exact_ratio()
        decade, power = exact_decade(numerator, denominator, decade)
        if numerator == power * denominator:
            return 0, 0, decade
    return max(0, left - decade * UNIT), min(UNIT, right - decade * UNIT), decade


def exact_decade(num, den, estimate):
    assert num >= den > 0
    decade = max(0, estimate)
    power = 10**decade
    while num >= 10 * power * den:
        power *= 10
        decade += 1
    while power > 1 and num < power * den:
        power //= 10
        decade -= 1
    assert power * den <= num < 10 * power * den
    return decade, power


def exact_digit(num, den, estimate):
    _, power = exact_decade(num, den, estimate)
    return num // (power * den)


def discrepancy(lefts, rights):
    N = len(lefts)
    lower = upper = 0
    for i, (lo, hi) in enumerate(zip(sorted(lefts), sorted(rights)), 1):
        lower = max(lower, i * UNIT - N * hi, N * lo - (i - 1) * UNIT)
        upper = max(upper, i * UNIT - N * lo, N * hi - (i - 1) * UNIT)
    return display((Q(lower, N * UNIT), Q(upper, N * UNIT)), 10)


def critical_profiles(grid, readings, centers):
    records = []
    S = grid.scale
    for N in centers:
        qlo, qhi, step_low, step_high = readings[N]
        ll, lu = grid.logarithm(N)
        samples = []
        for numerator in (4, 5, 6, 7, 8):
            n = N * numerator // 4
            lo, hi, _, _ = readings[n]
            if n == N:
                value = (Q(0), Q(0))
            else:
                estimates = [
                    w * k
                    for w in (lo - qhi - (n - N) * step_high, hi - qlo - (n - N) * step_low)
                    for k in (ll, lu)
                ]
                value = Q(min(estimates), N * S * S), Q(max(estimates), N * S * S)
            t = Q(numerator, 4)
            log_t = (0, 0) if t == 1 else log_ratio_interval(t.numerator, t.denominator, 50)
            curve = t * log_t[0] - t + 1, t * log_t[1] - t + 1
            samples.append(
                {
                    "t": str(t),
                    "actual_centered_phase": display(value, 10),
                    "limiting_curve": display(curve, 10),
                }
            )
        records.append({"start": N, "samples": samples})
    return records


def run(heads):
    primes = first_primes(heads[-1])
    grid = LogGrid(2, 36)
    ten = grid.logarithm(10)
    assert decimal_phase(grid.logarithm(100), ten, lambda: (100, 1)) == (0, 0, 2)
    thresholds = [None, (0, 0)] + [decimal_phase(grid.logarithm(i), ten)[:2] for i in range(2, 10)]
    thresholds.append((UNIT, UNIT))
    prime_low = prime_high = ratio_low = ratio_high = 0
    phase_lists = [([], []), ([], [])]
    hist = [[0] * 9, [0] * 9]
    checks = 0
    exact_fallbacks = 0
    nums = dens = 1
    decreasing = 0
    crossings = []
    results = []
    centers = [n for n in (1024, 4096, 32768, 131072) if 2 * n <= heads[-1]]
    needed = {n * t // 4 for n in centers for t in (4, 5, 6, 7, 8)}
    readings = {}
    for i, p in enumerate(primes, 1):
        pl, pu = grid.logarithm(p)
        il, iu = (0, 0) if i == 1 else grid.logarithm(i)
        prime_low, prime_high = prime_low + pl, prime_high + pu
        ratio_low, ratio_high = ratio_low + pl - iu, ratio_high + pu - il
        if i in needed:
            readings[i] = (ratio_low, ratio_high, pl - iu, pu - il)
        if i <= 256:
            nums *= p
            dens *= i
        if 4096 < i <= 8192:
            prev = primes[i - 2]
            decreasing += p * (i - 1) < prev * i
            if (p > 10 * i) != (prev > 10 * (i - 1)):
                crossings.append(i)
        for k, logs in enumerate(((prime_low, prime_high), (ratio_low, ratio_high))):

            def exact_ratio():
                numerator = nums if i <= 256 else prod(primes[:i])
                divisor = 1 if k == 0 else (dens if i <= 256 else factorial(i))
                return numerator, divisor

            lo, hi, e = decimal_phase(logs, ten, exact_ratio)
            determined = next(
                (d for d in range(1, 10) if lo >= thresholds[d][1] and hi < thresholds[d + 1][0]),
                None,
            )
            if determined is None:
                determined = exact_digit(*exact_ratio(), e)
                exact_fallbacks += 1
            if i <= 256:
                assert determined == exact_digit(nums, 1 if k == 0 else dens, e)
                checks += 1
            phase_lists[k][0].append(lo)
            phase_lists[k][1].append(hi)
            hist[k][determined - 1] += 1
        if i in heads:
            results.append(
                {
                    "N": i,
                    "last_prime": p,
                    "primorial": {
                        "counts": hist[0].copy(),
                        "star_discrepancy": discrepancy(*phase_lists[0]),
                    },
                    "primorial_divided_by_factorial": {
                        "counts": hist[1].copy(),
                        "star_discrepancy": discrepancy(*phase_lists[1]),
                    },
                }
            )
    return {
        "samples": results,
        "centered_dyadic_phases": critical_profiles(grid, readings, centers),
        "independent_exact_integer_leading_digits": checks,
        "exact_endpoint_fallbacks": exact_fallbacks,
        "resonance_interval": {
            "first_index": 4096,
            "last_index": min(8192, heads[-1]),
            "decreasing_p_over_n_steps": decreasing,
            "crossings_of_p_over_n_equal_ten": crossings,
        }
        if heads[-1] > 4096
        else None,
    }


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--heads", type=int, nargs="+", default=[4096, 8192, 65536, 262144])
    args = cli.parse_args()
    if any(n < 1 for n in args.heads):
        cli.error("use positive sample sizes")
    print(json.dumps(run(sorted(set(args.heads))), indent=2))
