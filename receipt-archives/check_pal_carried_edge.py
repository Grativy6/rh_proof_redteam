"""Replay the carried edge with integer sieving and rational physical readings."""
import json
from fractions import Fraction
from math import gcd

from check_pal_growth_windows import sieve
from check_pal_tapered_newton import balance


def census(k):
    return k - k // 2 - k // 3 + k // 6


def physical_error(coefficients, row):
    return 1 - sum(
        value * census(row // divisor)
        for divisor, value in enumerate(coefficients)
        if divisor and value
    )


def small_trajectory(limit=192):
    raw, _, _ = sieve(2 * (limit + 2))
    marks = [v if gcd(n, 6) == 1 else 0 for n, v in enumerate(raw)]
    band = 0
    price = Fraction(1)
    prices = []
    first_example = {}
    for h in range(1, limit + 3):
        coefficients, direct = balance(h, marks)
        assert price == direct
        assert band == sum(marks[h + 1 : 2 * h + 1])
        assert coefficients[2 * h] == -2 * price
        if h <= 40:
            before = physical_error(coefficients, h)
            for n in range(h + 1, 2 * h + 1):
                after = physical_error(coefficients, n)
                assert after - before + coefficients[n] == marks[n]
                before = after
            left = physical_error(coefficients, 2 * h - 1)
            right = physical_error(coefficients, 2 * h)
            assert right - left == 2 * price
            if h == 4:
                first_example = dict(side=h, left=str(left), right=str(right), slope=str(price))
        prices.append(price)
        if h == limit + 2:
            break
        price += Fraction(band, h * (h + 1)) + Fraction(marks[2 * h + 1], (2 * h + 1) * (h + 1))
        band += marks[2 * h + 1] - marks[h + 1]
    bends = [
        (prices[h + 1] - 2 * prices[h] + prices[h - 1]) * h * (h + 1)
        for h in range(1, limit + 1)
    ]
    assert max(abs(bend) for bend in bends) <= 6
    return {
        "prices_rebuilt": len(prices),
        "every_physical_row_checked_for_sides_through": 40,
        "first_example": first_example,
        "scaled_curvature_min": str(min(bends)),
        "scaled_curvature_max": str(max(bends)),
    }


def sampled_edges():
    # All observations share one independently accumulated integer divisor-count sieve.
    # Directed division of D*m(n) by n encloses each sharp harmonic sum.
    denominator = 10**17
    cubes = {j**3 for j in range(1, 196)}
    fourths = {j**4 for j in range(1, 53)}
    samples = cubes | fourths
    events = sorted(samples | {2 * h for h in samples})
    mu, _, _ = sieve(events[-1])
    totals = {}
    previous = lower = inexact = mass = 0
    for stop in events:
        for residue in (1, 5):
            start = previous + 1 + (residue - previous - 1) % 6
            for n in range(start, stop + 1, 6):
                if mu[n]:
                    q, r = divmod(denominator * mu[n], n)
                    lower += q
                    inexact += bool(r)
                    mass += mu[n]
        totals[stop] = lower, lower + inexact, mass
        previous = stop

    def enclosure(h):
        lo, hi, before = totals[h]
        lo2, hi2, after = totals[2 * h]
        correction = Fraction(after - before, h)
        return (Fraction(2 * lo2 - hi, denominator) - correction,
                Fraction(2 * hi2 - lo, denominator) - correction)

    examples = {
        str(j): [str(x) for x in enclosure(j**4)] for j in (49, 50, 51, 52)
    }
    assert enclosure(50**4)[0] > 0 and enclosure(51**4)[1] < 0 and enclosure(52**4)[0] > 0
    return {
        "rounding_denominator": denominator,
        "largest_integer_sieved": events[-1],
        "cube_indices_tested": [1, 195],
        "strictly_negative_cube_indices": [j for j in range(1, 196) if enclosure(j**3)[1] < 0],
        "fourth_power_indices_tested": [1, 52],
        "strictly_negative_fourth_power_indices": [j for j in range(1, 53) if enclosure(j**4)[1] < 0],
        "slope_bounds_at_fourth_powers": examples,
    }


if __name__ == "__main__":
    print(json.dumps({"unit_steps": small_trajectory(), "sparse_samples": sampled_edges()}, indent=2))
