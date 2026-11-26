"""Measure the prime pairs admitted when a factorial sieve cutoff moves below the square root."""

from bisect import bisect_right
from fractions import Fraction
from math import factorial, gcd, isqrt, prod
import json

from check_pal_dyson_window import (
    SCALE,
    ZERO,
    plus,
    minus,
    natural,
    log_int,
    interval_text,
    prime_data,
    integer_box,
)


def floor_cuberoot(n):
    low, high = 0, 1 << ((n.bit_length() + 2) // 3)
    while low + 1 < high:
        mid = (low + high) // 2
        if mid**3 <= n:
            low = mid
        else:
            high = mid
    return high if high**3 <= n else low


def ordered_products(n):
    x = isqrt(n)
    return 2 * sum(n // m for m in range(1, x + 1)) - x * x


def sieve_segment(lo, hi):
    if hi < lo:
        return []
    lo = max(2, lo)
    flags = bytearray([1]) * (hi - lo + 1)
    small, _ = prime_data(isqrt(hi))
    for p in range(2, len(small)):
        if small[p]:
            first = max(p * p, -(-lo // p) * p)
            if first <= hi:
                flags[first - lo :: p] = bytes((hi - first) // p + 1)
    return [a + lo for a, flag in enumerate(flags) if flag]


def price_at_root(k):
    n = k**4
    x = k * k
    lattice = ordered_products(n)
    h = floor_cuberoot((5 * lattice) // 8)
    assert 8 * h**3 <= 5 * lattice < 8 * (h + 1) ** 3
    c = max(0, x - h)
    primes = sieve_segment(c + 1, n // (c + 1))
    assert (c + 1) ** 3 > n
    logp = [log_int(p) for p in primes]
    prefix = [0]
    lower = [0]
    upper = [0]
    weighted_lower = [0]
    weighted_upper = [0]
    for p, (lo, hi) in zip(primes, logp):
        prefix.append(prefix[-1] + p)
        lower.append(lower[-1] + lo)
        upper.append(upper[-1] + hi)
        weighted_lower.append(weighted_lower[-1] + p * lo)
        weighted_upper.append(weighted_upper[-1] + p * hi)
    composite = ZERO
    extra_primes = ZERO
    pairs = 0
    diagonal = 0
    for i, p in enumerate(primes):
        if p > x:
            break
        extra_primes = plus(extra_primes, natural(2 * (n - p), logp[i]))
        end = bisect_right(primes, n // p)
        count = end - i
        pairs += count
        diagonal += 1
        left_multiplier = n * count - p * (prefix[end] - prefix[i])
        right = (
            n * (lower[end] - lower[i]) - p * (weighted_upper[end] - weighted_upper[i]),
            n * (upper[end] - upper[i]) - p * (weighted_lower[end] - weighted_lower[i]),
        )
        composite = plus(composite, natural(2, plus(natural(left_multiplier, logp[i]), right)))
    total = plus(composite, extra_primes)
    # Direct classification of every positive label, independent of grouping and prefix differences.
    if n <= 65536:
        fa, fr = factorial(c), factorial(x)
        direct = ZERO
        seen = 0
        for m in range(2, n + 1):
            if gcd(m, fa) == 1 and gcd(m, fr) != 1:
                direct = plus(direct, natural(2 * (n - m), log_int(m)))
                seen += 1
        assert max(total[0], direct[0]) <= min(total[1], direct[1])
        assert seen == pairs + bisect_right(primes, x)
    scale = n * x

    def normalized(value):
        return interval_text((value[0] // scale, -(-value[1] // scale)), 8)

    return {
        "k": k,
        "n": n,
        "hyperbola_pairs": lattice,
        "removed_sieve_width": h,
        "cut": c,
        "extra_prime_labels": bisect_right(primes, x),
        "extra_semiprime_labels": pairs,
        "unordered_diagonal": diagonal,
        "semiprime_log_cost_per_n_root_n": normalized(composite),
        "extra_prime_log_cost_per_n_root_n": normalized(extra_primes),
        "total_log_cost_per_n_root_n": normalized(total),
        "total_log_cost": total,
    }


def half_log_tau_interval():
    from check_pal_dense_square_payment import arctan_inverse, ln, mul, sub, box

    pi = sub(mul(box(16), arctan_inverse(5)), mul(box(4), arctan_inverse(239)))
    precision = 10**12
    low_pi = Fraction(int(pi[0] * precision), precision)
    high_pi = Fraction(-(-pi[1] * precision // 1), precision)
    half_log_tau = integer_box((ln(2 * low_pi)[0] / 2, ln(2 * high_pi)[1] / 2))
    return half_log_tau


def finite_margins(rows):
    half_log_tau = half_log_tau_interval()
    heads = sorted(r["n"] for r in rows if r["k"] <= 80)
    flags, _ = prime_data(heads[-1])
    look = {row["n"]: row for row in rows}
    theta = weight = ZERO
    primes = []
    for n in range(2, heads[-1] + 1):
        if flags[n]:
            reading = log_int(n)
            theta = plus(theta, reading)
            weight = plus(weight, natural(n, reading))
            primes.append(n)
        if n not in look:
            continue
        row = look[n]
        x = isqrt(n)
        small_cost = ZERO
        for p in primes[: bisect_right(primes, x)]:
            small_cost = plus(small_cost, natural(2 * (n - p), log_int(p)))
        area = minus(natural(n, theta), weight)
        P = minus((n * n * SCALE, n * n * SCALE), natural(2, area))
        # The Stirling main term prices the row orders. For H_n use
        # 0.5*log(2*pi*n) < H_n < 0.5*log(2*pi*n)+1/(12n).
        half_log_n = (log_int(n)[0] // 2, -(-log_int(n)[1] // 2))
        H = plus(plus(half_log_tau, half_log_n), (0, -(-SCALE // (12 * n))))
        G = minus(P, natural(n, H))
        margin = minus(plus(G, small_cost), row["total_log_cost"])
        row["critical_margin_per_n_root_n"] = interval_text(
            (margin[0] // (n * x), -(-margin[1] // (n * x))), 8
        )
        row["critical_board_fits"] = margin[0] > 0
        assert margin[0] > 0 or margin[1] < 0


def cutoff_control():
    n = 256
    frame = 6006
    labels = [m for m in range(2, n + 1) if gcd(m, frame) == 1]
    inputs = factorial(n) ** n * prod(m ** (2 * (n - m)) for m in labels)
    space = n ** (n * n)
    trial = inputs
    first = 0
    for cut in range(n + 1):
        if cut in labels:
            trial //= cut ** (2 * (n - cut))
        if trial <= space:
            first = cut
            break
    assert first == 5 and inputs > space and trial * 5**502 == inputs
    assert len([m for m in labels if m > first and (gcd(m, 30030) != 1)]) == 11
    return {
        "n": n,
        "damaged_frame": frame,
        "first_fitting_payload_cut": first,
        "still_admitted_false_labels": [m for m in labels if m > first and gcd(m, 30030) != 1],
        "spare_whole_bits_after_second_change": (space // trial).bit_length() - 1,
        "extra_bits_before_second_change": (inputs - 1).bit_length() - (space - 1).bit_length(),
    }


def analytic_prices():
    # Enclose Euler's constant by a finite harmonic sum and its integral-test remainder.
    count = 200000
    harmonic = sum(SCALE // j for j in range(1, count + 1))
    gamma = minus((harmonic - (-(-SCALE // count)), harmonic + count), log_int(count))
    half_tau = half_log_tau_interval()
    # log(4*pi) = log(2) + log(2*pi).
    trace = minus(plus((2 * SCALE, 2 * SCALE), gamma), plus(log_int(2), natural(2, half_tau)))
    assert 0 < trace[0] and 15 * trace[1] < log_int(2)[0]
    from check_pal_rise_direction import sqrt_box

    height = Fraction(1413474, 100000)
    upper = sqrt_box((height**2 + Fraction(1, 4)) * (height**2 + Fraction(9, 4)))[1]
    residue = 2 / upper
    assert 70 * residue > Fraction(log_int(2)[1], SCALE)
    return {
        "trace_2_plus_gamma_minus_log4pi": interval_text(trace, 9),
        "critical_zero_residue_modulus_lower": interval_text(integer_box((residue, residue)), 9)[0],
        "unconditionally_insufficient_bits_per_n_root_n": "1/70",
        "eventually_sufficient_bits_per_n_root_n_under_RH": "2/15",
        "trace_upper_below_log2_over_15": True,
    }


def audit():
    roots = [8, 12, 16, 20, 24, 32, 40, 48, 64, 80, 128, 256, 577, 1000, 2663, 4096, 10000]
    rows = [price_at_root(k) for k in roots]
    finite_margins(rows)
    for row in rows:
        del row["total_log_cost"]
    return {
        "critical_integer_cut": "8*h^3 <= 5*sum(floor(n/r), r=1..n) < 8*(h+1)^3",
        "limiting_extra_semiprime_cost_per_n_root_n": "10/3",
        "complete_margins_at_selected_roots": [k for k in roots if k <= 80],
        "least_cut_control": cutoff_control(),
        "spectral_prices": analytic_prices(),
        "heads": rows,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
