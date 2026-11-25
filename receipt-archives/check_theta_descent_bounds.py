"""Finite checks for label rigidity, the limit example, and the local ideal.

All bounds over unbounded levels, traits, and germs are proved in the
companion receipts. These integer computations exercise the boundary cases.
"""

from collections import Counter
from fractions import Fraction
from itertools import product


def q(x, y):
    return x * x + x * y + y * y


def check_label_symmetry():
    modulus, base = 9, 3
    # If q(x,y)<=3, then x^2,y^2<=4 by completing the square.
    small = {
        (x % modulus, y % modulus): q(x, y)
        for x, y in product(range(-2, 3), repeat=2)
        if q(x, y) <= 3
    }
    transformations = []
    congruent = 0
    for a, b, c, d in product(range(modulus), repeat=4):
        if (a * d - b * c) % modulus != 1 or (
            a % base,
            b % base,
            c % base,
            d % base,
        ) != (1, 0, 0, 1):
            continue
        congruent += 1
        if all(
            small.get(((a * x + b * y) % modulus, (c * x + d * y) % modulus)) == size
            for (x, y), size in small.items()
        ):
            transformations.append((a, b, c, d))
    assert congruent == 27 and transformations == [(1, 0, 0, 1)]
    print(
        "At level 9, 1 of 27 determinant-one maps fixing level 3 preserves the short labels."
    )


def class_changes(level, last):
    modulus = 7 ** (level + 1)
    changes = Counter()
    for j in range(1, last + 1):
        changes[0, j] += 1
        changes[(7 ** (j + 1)) % modulus, j] -= 1
    return {place: count for place, count in changes.items() if count}


def check_coherent_limits():
    for i in range(1, 8):
        expected = class_changes(i, i - 1)
        assert expected == class_changes(i, 12)
        coarse_modulus = 7 ** (i + 1)
        reduced = Counter()
        for (residue, j), count in class_changes(i + 1, 12).items():
            reduced[residue % coarse_modulus, j] += count
        assert {k: v for k, v in reduced.items() if v} == expected
        degree = 3 * 7**i
        assert pow(2, degree, 7 ** (i + 1)) == 1
        assert pow(2, degree // 7, 7 ** (i + 1)) != 1
        assert pow(2, degree // 3, 7 ** (i + 1)) != 1
    assert pow(2, 3, 7) == 1 and pow(2, 3, 49) != 1
    print(
        "The formal corrections cancel at every tested coarse level; Frobenius fixes level 7 and moves level 49."
    )


def required_approximation(a, k):
    return k if k <= a else a * (k - a) + 1


def all_monomials_fit(a, k, e):
    # For u<a use the smallest v for which 2^u T^v passes every trait.
    d = min(a, e)
    for u in range(a):
        v = max(0, (e * (d - u) + d - 1) // d)
        if u + v < k:
            return False
    return True


def check_divisor_precision():
    for a in range(1, 16):
        for k in range(1, 20):
            result = required_approximation(a, k)
            assert all_monomials_fit(a, k, result)
            if result > 1:
                assert not all_monomials_fit(a, k, result - 1)
    # With D=(2^4) and k=8, the near-boundary monomial 2^3 T^4 passes
    # the e=16 test but has order 7 at the center. At e=17 it fails.
    assert required_approximation(4, 8) == 17
    for e, passes in [(16, True), (17, False)]:
        valuation = Fraction(4, e)
        assert ((3 + 4 * valuation) >= min(4, e * valuation)) == passes
    print("For D=(2^4) and requested order 8 the sharp correction exponent is 17.")


def node_required_precision(n, k):
    return k if k < n else n * (k - n + 1)


def node_cutoff(n, e):
    # The right side is piecewise linear; 0 and n are limiting slopes.
    slopes = {Fraction(0), Fraction(n), Fraction(1), Fraction(n, e + 1)}
    if 0 < n - e < n:
        slopes.add(Fraction(n - e))
    tests = [(t, min(n - t, e, e * t)) for t in slopes]
    least = e  # The term y^e always qualifies.
    for i in range(n):
        # At any positive slope, i + v*t >= target bounds v from below.
        lower = max((target - i) / t for t, target in tests if t)
        v = max(0, -(-lower.numerator // lower.denominator))
        least = min(least, i + v)
    return least


def check_singular_node():
    for n in range(2, 13):
        for k in range(1, 16):
            needed = node_required_precision(n, k)
            assert node_cutoff(n, needed) >= k
            if needed > 1:
                assert node_cutoff(n, needed - 1) < k
    for e, passes in [(8, True), (9, False)]:
        slope = Fraction(3, e + 1)
        assert (2 + 2 * slope >= min(3 - slope, e, e * slope)) == passes
    print(
        "For xy=2^3 and requested order 5, the last false positive 4y^2 passes at 8 and fails at 9."
    )


def blowup_order(a, b, s):
    if s <= 1:
        return a * s
    if s < 2:
        return a * (2 - s) + b * (s - 1)
    return Fraction(b)


def check_blowup():
    slopes = sorted({Fraction(i, j) for j in range(1, 8) for i in range(1, 5 * j)})
    for a in range(1, 6):
        for b in range(a, 2 * a + 1):
            for s in slopes:
                generators = (a * s, (2 * a - b) + (b - a) * s, Fraction(b))
                assert min(generators) == blowup_order(a, b, s)
    a, b = 1, 3
    # F=T works everywhere for error exponent 1, and at integer slopes for 2.
    for s in slopes:
        assert s >= min(blowup_order(a, b, s), min(1, s))
        if s.denominator == 1:
            assert s >= min(blowup_order(a, b, s), 2 * min(1, s))
    slope = Fraction(4, 3)
    required = min(blowup_order(a, b, slope), 2 * min(1, slope))
    assert required == Fraction(5, 3)
    assert max(1, slope) < required
    print(
        "The arc T=2^(4/3) rejects the putative pullback with exceptional orders 1 and 3 at exponent 2."
    )


if __name__ == "__main__":
    check_label_symmetry()
    check_coherent_limits()
    check_divisor_precision()
    check_singular_node()
    check_blowup()
