"""Exact leading coefficients for two depths of an E8 theta projector at 2.

The theta series converges p-adically. The finite checks establish the data
needed for its first digits; the receipt bounds every omitted lattice term.
Run from any directory with Python 3.8 or later. No external packages.
"""

from fractions import Fraction
from math import isqrt


EDGES = ((0, 2), (1, 3), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7))
GRAM = [[2 * (i == j) for j in range(8)] for i in range(8)]
for i, j in EDGES:
    GRAM[i][j] = GRAM[j][i] = -1
ZERO = (0,) * 8
R = (1, 0, 0, 0, 0, 0, 0, 0)
S = (0, 0, -1, 0, 0, 0, 0, 0)


def inner(x, y):
    return sum(
        x[i] * c * y[j] for i, row in enumerate(GRAM) for j, c in enumerate(row) if c
    )


def add(x, y, factor=1):
    return tuple(a + factor * b for a, b in zip(x, y))


def scale(x, factor):
    return tuple(factor * a for a in x)


def check_lattice():
    # Positive pivots certify positive definiteness and their product is det B.
    matrix = [[Fraction(x) for x in row] for row in GRAM]
    determinant = Fraction(1)
    lower = [[Fraction(i == j) for j in range(8)] for i in range(8)]
    pivots = []
    for i in range(8):
        pivot = matrix[i][i]
        assert pivot > 0
        determinant *= pivot
        pivots.append(pivot)
        for k in range(i + 1, 8):
            multiple = matrix[k][i] / pivot
            lower[k][i] = multiple
            for j in range(i + 1, 8):
                matrix[k][j] -= multiple * matrix[i][j]
    assert determinant == 1
    assert (inner(R, R), inner(R, S), inner(S, S)) == (2, 1, 2)
    perpendicular = add(scale(S, 2), R, -1)
    assert inner(perpendicular, perpendicular) == 6 and inner(perpendicular, R) == 0
    return lower, pivots


def short_vectors(lower, pivots):
    # Enumerate the full norm <= 2 shell by exact completing of squares.
    x = [0] * 8

    def visit(i, remaining):
        if i < 0:
            yield tuple(x)
            return
        offset = sum(lower[j][i] * x[j] for j in range(i + 1, 8))
        remaining_square = remaining / pivots[i]
        radius = isqrt(remaining_square.numerator // remaining_square.denominator) + 1
        floor_center = (-offset).numerator // (-offset).denominator
        for value in range(floor_center - radius, floor_center + radius + 2):
            cost = pivots[i] * (value + offset) ** 2
            if cost <= remaining:
                x[i] = value
                yield from visit(i - 1, remaining - cost)

    return list(visit(7, Fraction(2)))


# The polynomial is X^5+X^2+1. Setting modulus to 2 gives the residue
# field; modulus 4 gives a two-digit unramified ring with the same basis.
ONE = (1, 0, 0, 0, 0)
X = (0, 1, 0, 0, 0)


def ring_product(a, b, modulus):
    result = [0] * 9
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            result[i + j] += u * v
    for k in range(8, 4, -1):
        result[k - 5] -= result[k]
        result[k - 3] -= result[k]
    return tuple(x % modulus for x in result[:5])


def ring_power(a, n, modulus):
    result = ONE
    while n:
        if n & 1:
            result = ring_product(result, a, modulus)
        a = ring_product(a, a, modulus)
        n //= 2
    return result


def leading_pair(base, relative_level):
    m = base * relative_level
    first = scale(add(S, R, (relative_level - 1) // 2), base)
    second = add(first, R, -m)
    y = scale(S, base)
    h = (m * m + 7 * base * base) // 2
    exponents = [(20 * inner(y, y) + inner(x, y)) % 31 for x in (first, second)]
    assert inner(first, first) + inner(y, y) == inner(second, second) + inner(y, y) == h
    assert all((a - b) % m == 0 for a, b in zip(first, second))
    assert any((a - b) % (7 * m) != 0 for a, b in zip(first, second))
    # These inequalities handle every other representative, by the norm
    # estimates in the receipt. The y-coset has just one shortest vector.
    assert 6 * (relative_level - 1) ** 2 > 2 * relative_level**2 + 6
    assert (relative_level - 1) ** 2 > 1
    return m, h, exponents


def main():
    lower, pivots = check_lattice()
    shell = short_vectors(lower, pivots)
    assert len(shell) == 241 and set(inner(w, w) for w in shell) == {0, 2}
    center = add(S, R, 24)
    # Any w making this norm no larger has norm squared <= 2 + 6/49^2.
    matches = {
        w
        for w in shell
        if inner(add(center, w, 49), add(center, w, 49)) <= inner(center, center)
    }
    assert matches == {ZERO, scale(R, -1)}
    elements = {ring_power(X, i, 2) for i in range(31)}
    assert (
        len(elements) == 31 and ring_power(X, 31, 2) == ONE and (0,) * 5 not in elements
    )
    # Raising X to 32 gives the order-31 Teichmuller lift modulo 4.
    zeta = ring_power(X, 32, 4)
    assert ring_power(zeta, 31, 4) == ONE
    base = 7**5
    assert pow(7, 15, 31) == 1 and all(pow(7, 15 // p, 31) != 1 for p in (3, 5))
    for k in (2, 17, 32, 47):
        m, h, exponents = leading_pair(base, 7**k)
        assert exponents == [7, 22]
        assert Fraction(h, m * m) == Fraction(1, 2) + Fraction(7, 2 * 7 ** (2 * k))
    m, h, _ = leading_pair(base, 49)
    first, second = [ring_power(zeta, exponent, 4) for exponent in (7, 22)]
    summed = tuple((a + b) % 4 for a, b in zip(first, second))
    assert summed == (1, 2, 0, 0, 2)
    assert tuple(x % 2 for x in first) != tuple(x % 2 for x in second)
    assert tuple(x % 2 for x in summed) == ONE and summed != ONE
    assert all(ring_power(w, 3, 2) != ONE for w in elements if w != ONE)
    print(f"Base torsion {base}, coarse level {m}, valuation {h}.")
    print("True residues are g^7 and g^22 in F_32; their sum is 1.")
    print("Two-digit sum in the power basis modulo 4:", summed)
    print("The next 7-power projection separates the same two vectors.")


if __name__ == "__main__":
    main()
