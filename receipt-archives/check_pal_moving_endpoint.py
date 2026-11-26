"""Reproduce the finite convex prime-area bounds with integers and rational bounds."""

import json
from decimal import Decimal, localcontext
from fractions import Fraction as F
from math import comb, isqrt, prod

from check_pal_dyson_window import SCALE, interval_text, log_int, prime_data

HEIGHT = 3 * 10**12
PASSES = 45
WIDTH = F(2, HEIGHT)
ORDINATE_MASS = F(4621, 100000)
SMALL = 2**16


def upper_text(q, places=12):
    unit = 10**places
    scaled = -(-q.numerator * unit // q.denominator)
    return f"{scaled // unit}.{scaled % unit:0{places}d}"


def small_boards():
    primes, _ = prime_data(SMALL)
    factorial_hi = 0
    pascal_lo = 0
    theta_hi = 0
    area_hi = 0
    minimum = None
    min_head = None
    for n in range(1, SMALL + 1):
        area_hi += theta_hi
        lo, hi = log_int(n)
        factorial_hi += hi
        pascal_lo += n * lo - factorial_hi
        if primes[n]:
            theta_hi += hi
        assert theta_hi < n * SCALE
        if n > 1:
            margin = pascal_lo - area_hi
            assert margin > 0, n
            if minimum is None or margin < minimum:
                minimum, min_head = margin, n
        if n <= 64:
            all_prime = prod(p ** (n - p) for p in range(2, n + 1) if primes[p])
            subsets = prod(comb(n, j) for j in range(n + 1))
            assert all_prime <= subsets and (n == 1 or all_prime < subsets)
    assert minimum is not None and min_head == 2
    return {
        "range": [1, SMALL],
        "least_proved_log_margin_after_one_at": min_head,
        "least_margin_lower_endpoint": interval_text((minimum, minimum), 10)[0],
        "theta_strictly_below_head_through": SMALL,
        "direct_integer_product_repeat_through": 64,
    }


def spectral_bound(exponent):
    # All fractions bound positive terms from above. The cutoff is inclusive.
    assert exponent % 2 == 0
    root = 2 ** (exponent // 2)
    step = PASSES * WIDTH**2 / 3
    variance = step / (1 - step)
    cosh_cap = 1 / (1 - 2 * WIDTH)
    curvature = root * variance / 2
    low = ORDINATE_MASS * (1 + variance)
    high = root * F(10, HEIGHT) * (cosh_cap / 2) ** PASSES
    return curvature, low, high


def decimal_repeat(exponent, enclosure):
    # Evaluate the unrounded moment and both spectral majorants via exp().
    with localcontext() as ctx:
        ctx.prec = 105
        one = Decimal(1)
        root = Decimal(2) ** (exponent // 2)
        h = Decimal(2) / HEIGHT
        p = h.exp()
        q = (-h).exp()
        m = (p - q) / (2 * h)
        second = (h * (p + q) / (p - q)) ** PASSES
        low_moment = (
            ((3 * h / 2).exp() - (-3 * h / 2).exp()) / (3 * h * m ** Decimal("1.5"))
        ) ** PASSES
        high_factor = ((2 * h).exp() + (-2 * h).exp()) / 4
        components = (
            root * (second - one) / 2,
            Decimal("0.04621") * low_moment,
            root * 10 / HEIGHT * high_factor**PASSES,
        )
        for actual, bound in zip(components, enclosure):
            assert actual < Decimal(bound.numerator) / Decimal(bound.denominator)
        return [str(v.quantize(Decimal("0.000000000001"))) for v in components]


def adaptive_prices():
    h = WIDTH
    alpha = 1 / (2 * (1 - 2 * h))
    assert 2 * alpha**2 < 1 and 0 < 1 - h**2 / 4 < 1
    assert F(1, 16) > ORDINATE_MASS
    assert F(3, 2) ** 4 <= F(4**4, 16) and F(3, 2) ** 2 <= 4**2
    assert 3 * h / F(1, 2) == F(4, 10**12)
    assert ORDINATE_MASS + F(10, HEIGHT) < F(4622, 100000)
    assert ORDINATE_MASS + F(4622, 100000) + F(2, 20**2) < F(1, 10)
    v = 145 * h**2 / 3
    coarse_root = 3 * 2**71
    assert 2**145 < coarse_root**2
    upper = coarse_root * v / (2 * (1 - v))
    assert upper < F(77, 1000)
    # h*cosh(h)-sinh(h) >= h^3/3, and sinh(h)<=h/(1-h^2/6).
    lower = F(2**73 * 146, 6) * h**2 * (1 - h**2 / 6)
    assert lower > F(1, 10)
    close = 40 * h
    assert 30**4 == 2**4 * 3**4 * 5**4
    assert 30**4 < 32**4 == 2**20 and 2**20 * close / (1 - close) < 1
    step20 = 20 * h * h / 3
    charged = F((2**20) ** 2, 2) * step20 / (1 - step20)
    assert charged < 2**20 * h / 24
    return {
        "opposite_signed_heads": {"positive": 30**4, "negative": 32**4},
        "passes_at_x": "ceil(log2(x))",
        "centered_upper_in_x_to_three_halves_units": "0.04622",
        "centered_normalized_limit": 0,
        "worth_of_one_high_pass_at_most": upper_text(alpha),
        "time_dependent_low_pass_saving_at_least": "h^2/4 per factor in its modulus bound",
        "lower_index_in_fixed_tenth_test": 20,
        "gross_variance_covers_all_real_heads_through": 2**145,
        "upper_at_that_head_using_a_rational_square_root_bound": upper_text(upper),
        "gross_variance_above_one_tenth_at": 2**146,
    }


def audit():
    # BPT Example 1, doubled for the negative ordinates. log(T)<29, pi>3,
    # and log(2*pi)>1 give the following upper bound for T times the tail.
    assert F(29, 3) + 2 * (F(14, 100) + F(56, 100) * 29) / HEIGHT < 10
    # Endpoint support is inside x*exp(+-2*r*h); x>=4 implies xY>2.
    assert 2 * PASSES * WIDTH < F(1, 2)

    # Independent small case: at the kink p^a=4 the two-endpoint Jensen excess
    # over the central reading is log(2)/2. Vectors count log(2) and log(3).
    def area_23(n):
        return (max(n - 2, 0) + max(n - 4, 0), max(n - 3, 0))

    excess = [a + c - 2 * b for a, b, c in zip(area_23(3), area_23(4), area_23(5))]
    assert excess == [1, 0]

    outputs = {}
    credit = F(49, 75)
    early_cost = credit * 11**3
    for exponent, cap in [(154, F(565, 1000)), (156, F(1083, 1000))]:
        components = spectral_bound(exponent)
        assert sum(components) < cap
        outputs[str(exponent)] = {
            "curvature_upper": upper_text(components[0]),
            "low_zeros_upper": upper_text(components[1]),
            "high_zeros_upper": upper_text(components[2]),
            "sum_upper": upper_text(sum(components)),
            "decimal_repeat": decimal_repeat(exponent, components),
        }
    assert credit - F(565, 1000) - early_cost / (SMALL * isqrt(SMALL)) > F(2, 25)
    assert F(156**2, 2**25) < F(1, 100)
    assert F(97, 100) * (1 - F(1, 2**77)) > F(96, 100)
    assert credit + F(96, 100) - F(1083, 1000) - early_cost / 2**231 > F(2, 25)
    assert F(1, 2) + 16 * F(7, 10) < F(2, 25) * isqrt(SMALL)
    assert 25 < isqrt(SMALL)
    assert 2**156 == (2**39) ** 4
    return {
        "height": HEIGHT,
        "log_width": "2/T",
        "passes": PASSES,
        "mass_both_signs_upper": "0.04621",
        "unrestricted_tail_mass_upper": "10/T",
        "two_endpoint_twice_excess": {"log2": excess[0], "log3": excess[1]},
        "small_boards": small_boards(),
        "adaptive": adaptive_prices(),
        "upper_prime_power_area_excess_in_x_to_three_halves_units": outputs,
        "every_untrimmed_head_through": 2**154,
        "every_sqrt_trimmed_head_through": 2**156,
        "every_fourth_power_index_through": 2**39,
        "next_exponent_control": {
            "exponent": 158,
            "same_envelope_upper": upper_text(sum(spectral_bound(158))),
            "meaning": "The evaluated upper bound exceeds the two credits used here.",
        },
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
