"""Exact prices for a second endpoint reading and a direct prime-table cross-check."""

import json
from fractions import Fraction as F
from math import comb, factorial, isqrt

from check_pal_moving_endpoint import HEIGHT, ORDINATE_MASS, WIDTH, upper_text

SHORT_WIDTH = F(51, 20 * HEIGHT)
SHORT_PASSES = 21
HIGH_FACTOR = F(22, 100)
SPLIT = 100000


def trig_bounds(x, first):
    # The next Taylor term encloses the remainder on our inputs 2.55 and 4.5.
    terms = [(-1) ** j * x ** (2 * j + first) / factorial(2 * j + first) for j in range(15)]
    ends = sum(terms), sum(terms[:-1])
    assert x * x < 28 * 29
    return min(ends), max(ends)


def sinc_price():
    x = F(51, 20)
    assert trig_bounds(x, 1)[1] / x < F(219, 1000)
    v = F(9, 2)
    sin_lo, _ = trig_bounds(v, 1)
    cos_lo, cos_hi = trig_bounds(v, 0)
    assert -sin_lo < F(978, 1000) and F(2107, 10000) < -cos_hi <= -cos_lo < F(2109, 10000)
    assert 1 - F(314, 400) < F(219, 1000)
    tangent = F(2109, 10000) + (F(978, 1000) - v * F(2107, 10000)) / 4
    assert tangent < F(219, 1000)
    assert F(219, 1000) + 3 * SHORT_WIDTH / x < HIGH_FACTOR
    return upper_text(tangent)


def root_upper(e):
    scale = 10**12
    square = 2**e * scale**2
    a = isqrt(square)
    return F(a + (a * a < square), scale)


def mean_abs_uniform_sum(r):
    numerator = sum((-1) ** j * comb(r, j) * (r - 2 * j) ** (r + 1) for j in range(r // 2 + 1))
    return F(4 * numerator, 2 ** (r + 1) * factorial(r + 1))


def raw_table_repeat():
    log_two_lower = sum(F(2, (2 * j + 1) * 3 ** (2 * j + 1)) for j in range(4))
    assert log_two_lower > F(693, 1000)
    assert mean_abs_uniform_sum(1) == F(1, 2)
    assert mean_abs_uniform_sum(2) == F(2, 3)
    result = {}
    for r, base, numerator in [(146, 100, 20097), (147, 101, 20047)]:
        assert (r - 1) * log_two_lower - 2 * r * WIDTH > base
        mean = mean_abs_uniform_sum(r)
        expected = (WIDTH * mean + r * WIDTH**2 / 5) / (1 - 4 * r * WIDTH)
        # The source bounds are 2.0097e-12 and 2.0047e-12.
        price = F(numerator, 10**16) * root_upper(r) * expected
        assert price < F(1, 10)
        result[str(r)] = {
            "prime_table_log_cutoff": base,
            "expected_absolute_uniform_sum_upper": upper_text(mean),
            "unpaid_upper": upper_text(price),
        }
    return result


def audit():
    tangent = sinc_price()
    # BPT's two-sided tail estimate at the intermediate split. log(1e5)<12.
    assert F(12, 3) + 2 * (F(14, 100) + F(56, 100) * 12) / SPLIT < 5
    # Both low heads use the same ordinates and the same x^(i gamma).
    low = ORDINATE_MASS * (SHORT_PASSES + 150) * 2 * SHORT_WIDTH * (SPLIT + 2) / (
        1 - 4 * SHORT_WIDTH
    ) + F(10, SPLIT)
    assert low < F(102, 10**6)
    v = SHORT_PASSES * SHORT_WIDTH**2 / 3
    short_variance = v / (1 - v)
    late_elementary = F(1, 3 * 2**217)
    rows = {}
    exact_at_148 = None
    for e in (148, 150, 151, 155, 158, 160):
        root = root_upper(e)
        curve = root * short_variance / 2
        high = root * F(10, HEIGHT) * HIGH_FACTOR**SHORT_PASSES
        usual = curve + ORDINATE_MASS + high
        # Cancellation of the two low parts is proved for r<=150.
        unpaid = curve + low + high + F(10, HEIGHT) + late_elementary if e <= 150 else None
        rows[str(e)] = {
            "curvature_upper": upper_text(curve),
            "short_high_upper": upper_text(high),
            "original_prime_power_area_upper": upper_text(usual),
        }
        if unpaid is not None:
            rows[str(e)]["unpaid_crossing_upper"] = upper_text(unpaid)
            assert unpaid < F(1, 10)
        if e == 148:
            assert unpaid is not None
            gross_lower = F(2**74 * 148, 6) * WIDTH**2 * (1 - WIDTH**2 / 6)
            assert unpaid < gross_lower / 4
            refund = gross_lower - unpaid
            assert refund > F(158, 1000) and gross_lower > F(207, 1000)
            exact_at_148 = {
                "gross_lower_strict": "0.207",
                "unpaid_upper": upper_text(unpaid),
                "actual_crossings_lower_strict": "0.158",
            }
        if e == 155:
            assert usual < F(598, 1000)
        if e == 158:
            assert usual < F(1607, 1000)
    assert F(49, 75) - F(598, 1000) > F(5, 100)
    assert F(158**2, 2**25) < F(1, 100)
    assert F(49, 75) + F(96, 100) - F(1607, 1000) > F(6, 1000)
    # Enough to pay both the 121-cutoff constant and the Pascal log remainder.
    assert F(49 * 1331, 75 * 2**231) + F(159, 2**77) < F(1, 1000)
    assert exact_at_148
    return {
        "finite_zero_height": HEIGHT,
        "original_width": "2/T",
        "comparison_width": "51/(20*T)",
        "comparison_passes": SHORT_PASSES,
        "middle_ordinate_split": SPLIT,
        "maximum_two_low_parts_difference": upper_text(low),
        "sinc_tangent_upper": tangent,
        "prices": rows,
        "return_at_x_equal_two_to_148": exact_at_148,
        "prime_table_independent_repeat": raw_table_repeat(),
        "fixed_tenth_all_real_heads_through": 2**150,
        "full_pascal_product_through": 2**155,
        "filtered_pascal_product_through": 2**158,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
