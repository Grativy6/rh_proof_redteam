"""Exact factorial-weighted pairings on a power-substituted block and its trace test."""

from fractions import Fraction
from math import comb, factorial, prod


def valuation(p, a):
    value = Fraction(a)
    assert value != 0
    n, d = abs(value.numerator), value.denominator
    order = 0
    while n % p == 0:
        n //= p
        order += 1
    while d % p == 0:
        d //= p
        order -= 1
    return order


def gamma(power, residue, digit):
    return Fraction(factorial(residue + power * digit),
                    factorial(residue) * factorial(digit) * factorial(power)**digit)


def one_pair(p, depth, covector_power):
    power = p**depth
    n = power
    g = gamma(power, 1, 1)
    assert g == power + 1
    # The two high monomial norms, divided by the common factorial.
    common = factorial(power) * factorial(covector_power)
    first = Fraction(factorial(power + 1) * factorial(covector_power), common)
    second = Fraction(factorial(power) * factorial(covector_power), common)
    assert (first, second) == (g, 1)
    assert (1 - g) / n == -1
    assert first - g * second == 0
    assert first / g - g * second == -power
    avg = (1 / g + n - 1) / n
    assert avg == Fraction(power, power + 1)
    assert valuation(p, 1 - avg) == 0
    print(f'p={p}, n={n}: uncorrected pairing 0, corrected normalized pairing {-power}, '
          f'invariant coefficient {avg}, traceless coefficient is a unit.')


def many_pairs(p, depths):
    deviations = []
    for depth in depths:
        power = p**depth
        low = power // p
        g = comb(power + low, low)
        assert g % (p*p) == 1 + p
        deviations.append(Fraction(1, g) - 1)
    assert valuation(p, prod(deviations)) == len(depths)
    print(f'{len(depths)} pairs: the extreme-weight coefficient has valuation {len(depths)}.')


def symmetric_pair(p):
    degree = p - 1
    first = gamma(p, 1, degree) * gamma(p, 0, degree)
    second = gamma(p, 0, degree)**2
    ratio = first / second
    assert ratio == 1 + p * degree
    assert valuation(p, (1 - ratio) / p) == 0
    assert first - ratio * second == 0
    assert first / first - ratio * second / second == -p * degree
    print(f'p={p}, two coordinates, symmetric degree {degree}: primitive trace component, '
          f'uncorrected pairing 0.')


if __name__ == '__main__':
    one_pair(5, 1, 5)
    one_pair(17, 2, 17)
    many_pairs(5, (1, 2, 3))
    symmetric_pair(17)
