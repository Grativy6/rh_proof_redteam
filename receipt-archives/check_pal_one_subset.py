"""Read the same finite alternating prime signal by prime powers and by all divisor labels."""

from fractions import Fraction
from functools import lru_cache
import json

from check_pal_dyson_window import (
    SCALE,
    ZERO,
    integer_box,
    interval_text,
    log_int,
    minus,
    natural,
    plus,
    prime_data,
    times,
)


def rational(q):
    return integer_box((Fraction(q), Fraction(q)))


@lru_cache(maxsize=100000)
def log_number(n):
    return log_int(n)


def logarithm(q):
    return minus(log_number(q.numerator), log_number(q.denominator))


def interval_intersection(a, b):
    assert max(a[0], b[0]) <= min(a[1], b[1])
    return max(a[0], b[0]), min(a[1], b[1])


def prefix(limit):
    flags, powers = prime_data(limit)
    arithmetic = [(ZERO, ZERO, ZERO)]
    ordinary = [(ZERO, ZERO, ZERO)]
    harmonics = [ZERO]
    for d in range(1, limit + 1):
        log = log_number(d)
        base = log if flags[d] else log_number(powers[d][0]) if d in powers else ZERO

        def advance(prev, weight):
            return (
                plus(prev[0], weight),
                plus(prev[1], natural(d, weight)),
                plus(prev[2], times(weight, log)),
            )

        arithmetic.append(advance(arithmetic[-1], base))
        ordinary.append(advance(ordinary[-1], log))
        harmonics.append(plus(harmonics[-1], rational(Fraction(1, d))))
    return arithmetic, ordinary, harmonics


def terms(x, table):
    if x < 1:
        return ZERO, ZERO
    weight, linear, log_weight = table[x.numerator // x.denominator]
    per_x = times(linear, rational(1 / x))
    V = minus(weight, per_x)
    primitive = plus(minus(times(minus(logarithm(x), rational(1)), weight), log_weight), per_x)
    return V, primitive


def physical(x, arithmetic):
    if x < 1:
        return ZERO, ZERO
    V, primitive = terms(x, arithmetic)
    return minus(V, rational(x / 2)), minus(primitive, rational((x - 1) / 2))


def all_divisors(x, ordinary, harmonics):
    if x < 1:
        return ZERO, ZERO
    V, primitive = terms(x, ordinary)
    n = x.numerator // x.denominator
    center = times(rational(x / 2), harmonics[n])
    return minus(V, center), minus(primitive, minus(center, rational(Fraction(n, 2))))


def head(x, arithmetic, ordinary, harmonics):
    v = primitive = ZERO
    for r in range(1, x.numerator // x.denominator + 1):
        a, b = physical(x / r, arithmetic)
        signed = plus if r % 2 else minus
        v = signed(v, a)
        primitive = signed(primitive, b)
    top = all_divisors(x, ordinary, harmonics)
    half = all_divisors(x / 2, ordinary, harmonics)
    reduced = [minus(u, natural(2, w)) for u, w in zip(top, half)]
    v = interval_intersection(v, reduced[0])
    primitive = interval_intersection(primitive, reduced[1])
    assert v[0] >= 0 or v[0] ** 2 <= 144 * x * SCALE**2
    assert primitive[0] >= 0 or primitive[0] ** 2 <= 576 * x * SCALE**2
    source, cumulative = physical(x, arithmetic)
    return {
        "head": str(x),
        "centered_prime_reading": interval_text(source, 8),
        "primitive": interval_text(cumulative, 8),
        "alternate_prime_or_all_integer": interval_text(v, 8),
        "alternate_primitive_or_all_integer": interval_text(primitive, 8),
    }


def audit():
    xs = [Fraction(h) for h in (1, 2, 3, 4, 16, 49, 577, 2663, 10000)]
    xs += [Fraction(5, 2), Fraction(99, 2), Fraction(8017, 3)]
    data = prefix(10000)
    return {
        "heads": [head(x, *data) for x in xs],
        "comparison": "finite prime-power labels and independently regrouped log(m) and harmonic rows",
        "proved_alternate_lower_multiple_of_sqrt": -12,
        "proved_integrated_alternate_lower_multiple_of_sqrt": -24,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
