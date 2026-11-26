"""Check elementary constants and independently evaluate the Gaussian prime-area identity."""

from fractions import Fraction as F
from math import ceil, erfc, exp, fsum, lcm, log, pi, sqrt
import json

from check_pal_dyson_window import SCALE, log_int, prime_data
from check_pal_moving_endpoint import upper_text


def curvature(z):
    if z > 1:
        return curvature(1 / z) / z**3
    # Terms after index 12 have exponent <= -169*pi throughout this branch.
    terms = []
    for j in range(1, 13):
        a = pi * (j / z) ** 2
        terms.append((4 * a * a - 6 * a) * exp(-a) / (z * z))
    return fsum(terms)


def simpson(f, left, right, panels):
    h = (right - left) / panels
    odd = fsum(f(left + i * h) for i in range(1, panels, 2))
    even = fsum(f(left + i * h) for i in range(2, panels, 2))
    return h / 3 * (f(left) + 4 * odd + 2 * even + f(right))


def two_ways(x):
    c = pi / 3
    X = c * x

    def q(u):
        return -exp(-pi * u * u) + 2 * pi * u * erfc(sqrt(pi) * u)

    logs = 2 * x * fsum(log(m) * q(m / X) for m in range(2, ceil(8 * X) + 1))
    zmin, zmax = 1 / 8, 8
    top = ceil(X / zmin)
    primes, powers = prime_data(top)
    marks = [
        (d, log(d if primes[d] else powers[d][0]))
        for d in range(2, top + 1)
        if primes[d] or d in powers
    ]
    # Split at the actual prime-power hinges and at the modular reflection.
    cuts = sorted({zmin, 1.0, zmax, *[X / d for d, _ in marks if zmin < X / d < zmax]})

    def physical(z):
        y = X / z
        return z * z * curvature(z) / (pi / 6) * fsum((y - d) * v for d, v in marks if d < y)

    def integrate(n):
        return fsum(simpson(physical, lo, hi, n) for lo, hi in zip(cuts, cuts[1:]))

    rough, fine = integrate(64), integrate(128)
    assert abs(fine - rough) < 1e-5 and abs(fine - logs) < 1e-6
    return {
        "head": x,
        "integer_log_sum": round(logs, 9),
        "direct_ramp_quadrature": round(fine, 9),
        "absolute_difference": float(f"{abs(fine - logs):.3g}"),
        "type": "Floating illustration on the displayed truncations. The proof uses the analytic identities.",
    }


def auditable_constants():
    # Multiply the quotient by 1+t^2 to check the integral for 22/7-pi.
    q = [4, 0, -4, 0, 5, -4, 1]
    polynomial = [0] * (len(q) + 2)
    for i, a in enumerate(q):
        polynomial[i] += a
        polynomial[i + 2] += a
    polynomial[0] -= 4
    assert polynomial == [0, 0, 0, 0, 1, -4, 6, -4, 1]
    assert sum(F(a, i + 1) for i, a in enumerate(q)) == F(22, 7)
    gap = F(1, 18) * F(2, 9) ** 4 / (1 + F(2, 3) ** 2)
    charged = F(5, 2**16) + (10 + 8 * 33 * F(7, 10)) / 2**32
    assert charged < gap
    assert F(1, 20) + F(1, 24) + F(2, 3) * F(7, 100) < F(1, 7)
    assert F(8, 7) < F(107, 100) ** 2
    assert F(17, 30) + F(1, 20) < F(2, 3) < F(3, 4) < F(99, 100)
    assert F(3, 4) + F(2, 3) < F(3, 2) and 3 * F(3, 4) - 1 < F(3, 2)
    assert 4**2 > 5 and 4**2 * 5 < 16**2
    return {
        "two_thirds_funding_from_integer_head": 2**32,
        "gross_charge": "n^2/14",
        "elementary_comparison_coefficient": "4/7 - pi/6",
        "positive_rational_gap_over_two_thirds_of_gross": str(gap),
        "all_explicit_debits_upper_at_first_head": upper_text(charged),
        "sufficient_raw_area_upper_in_three_halves_units": "1/20",
        "block_window_in_quartic_indices": "[K, 2 K (log(2K))^(1/4)] for all sufficiently large K",
    }


def drift_at(n):
    m = lcm(*range(1, n + 1))
    a, b = log_int(m)
    return F(a, SCALE) - n - F(1, 2), F(b, SCALE) - n - F(1, 2)


def audit():
    first = drift_at(32)
    second = drift_at(33)
    assert first[0] > 0 and second[1] < 0 and first[0] - second[0] == 1
    return {
        "constants": auditable_constants(),
        "same_prime_power_total_at_32_and_33": lcm(*range(1, 34)),
        "drift_positive_at": 32,
        "drift_negative_at": 33,
        "numerical_illustrations": [two_ways(x) for x in (4, 16)],
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
