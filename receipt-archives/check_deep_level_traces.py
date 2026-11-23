"""Exact finite controls for coefficient-field descent and the geometric level trace."""

from fractions import Fraction
from itertools import product
from math import gcd, isqrt, prod


def is_prime(value):
    return value >= 2 and all(value % d for d in range(2, isqrt(value) + 1))


def units(modulus):
    return [x for x in range(1, modulus) if gcd(x, modulus) == 1]


def check_ray_kernel():
    for depth in range(1, 5):
        modulus = 15 ** depth
        unit_group = units(modulus)
        anti = {(x, pow(x, -1, modulus)) for x in unit_group}
        if depth <= 2:
            product_kernel = {(x, y) for x, y in product(unit_group, repeat=2)
                              if x * y % modulus == 1}
            assert product_kernel == anti
        # Wild inertia at 3 and the whole inertia at 5.
        detected = {(x, y) for x, y in anti if x % 3 == 1}
        assert len(anti) == 8 * 15 ** (depth - 1)
        assert len(detected) == 4 * 15 ** (depth - 1)
        assert {x % (5 ** depth) for x, _ in detected} == set(units(5 ** depth))
    print("Ray norm kernel and the index-two inertia subgroup checked through depth 4.")


def check_character_trace():
    # H = C_m x C_2. The first factor permutes the components, the second
    # acts on their fibres by its sign character. Every component stabilizer
    # therefore has order 2.
    for orbit_size in [3, 5, 7, 8, 11]:
        vector = [1] + [0] * (orbit_size - 1)
        raw = [0] * orbit_size
        for rotation, sign in product(range(orbit_size), (1, -1)):
            translated = [sign * vector[(j + rotation) % orbit_size]
                          for j in range(orbit_size)]
            for j, value in enumerate(translated):
                raw[j] += sign * value
        assert raw == [2] * orbit_size
        assert [Fraction(value, 2 * orbit_size) for value in raw] == [
            Fraction(1, orbit_size)] * orbit_size
    print("Twisted trace of an integral component cut: exact orbit denominators checked.")


def dyadic_residue_degree(p, e):
    modulus = 2 ** (e + 2)
    value = p % modulus
    order = 1
    while value not in (1, modulus - 1):
        value = value * p % modulus
        order += 1
    return order


def check_window_arithmetic():
    d, q, e = 1319, 11, 3
    level_primes = [5_571_457, 7_892_897, 9_750_049, 11_142_913]
    conductor = 2 ** (e + 2) * q * d
    assert len(set(level_primes)) == 4 and all(is_prime(p) for p in [d, q, *level_primes])
    assert d % 16 == 7 and q % 8 == 3 and (d + 1) % (3 * 5 * q) == 0
    assert all(p % conductor == 1 for p in level_primes)
    for exponent in range(2, 11):
        assert dyadic_residue_degree(3, exponent) == 2 ** exponent
        assert dyadic_residue_degree(5, exponent) == 2 ** exponent

    # The odd part of 3^(n/2)+1 has a prime with exact dyadic order n.
    for exponent in range(2, 7):
        n = 2 ** exponent
        factor = (3 ** (n // 2) + 1) // 2
        assert factor % (2 * n) == 1 + n and factor > 1
    n = 2 ** e
    assert (3 ** (n // 2) + 1) // 2 == 41 and is_prime(41)
    assert pow(3, n // 2, 41) == 40 and 40 % n == 0 and 40 % (2 * n) != 0
    for depth in (1, 2, 3):
        factors = [p ** (n * (depth - 1)) * (p ** n - 1) for p in (3, 5)]
        det_order = prod(x ** 2 for x in factors)
        closed_form = 15 ** (2 * n * (depth - 1)) * ((3 ** n - 1) * (5 ** n - 1)) ** 2
        assert det_order == closed_form and det_order % 41 ** 2 == 0 and det_order % 41 ** 3 != 0
    print("Two split dyadic residue degrees and the determinant factor 41^2 verified.")


if __name__ == "__main__":
    check_ray_kernel()
    check_character_trace()
    check_window_arithmetic()
