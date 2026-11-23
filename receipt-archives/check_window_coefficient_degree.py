"""Finite controls for the window coefficient-field degree audit. Standard-library Python 3."""

from fractions import Fraction as F
from itertools import combinations, permutations
from math import gcd, isqrt, prod


def determinant(matrix):
    n = len(matrix)
    total = 0
    for perm in permutations(range(n)):
        sign = (-1)**sum(a > b for a, b in combinations(perm, 2))
        total += sign * prod(matrix[i][j] for i, j in enumerate(perm))
    return total


def multiply(left, right):
    return [[sum(a*b for a, b in zip(row, col)) for col in zip(*right)] for row in left]


def divide(matrix, denominator):
    return [[F(x, denominator) for x in row] for row in matrix]


def prime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n)+1))


def check_oriented_ideals():
    d = 5368439
    primes = (3, 5, 7, 11)
    assert prime(d) and d % 16 == 7
    assert (d+1) % (4*prod(primes)) == 0 and d > 4*prod(primes)**2
    divisors = sorted(prod(subset) for r in range(len(primes)+1) for subset in combinations(primes, r))
    forms = [(a, 1, (d+1)//(4*a)) for a in divisors]
    assert len(set(forms)) == 16
    for a, b, c in forms:
        assert b*b-4*a*c == -d
        assert gcd(gcd(a, b), c) == 1 and abs(b) <= a < c
    print(f"Discriminant -{d}: 16 distinct reduced forms; first {forms[0]}, last {forms[-1]}.")


def check_trace_bases():
    # O_E coordinates (1 in each copy, then w in each copy), w=(1+sqrt(13))/2.
    gram = [[2, 0, 1, 0], [0, 2, 0, 1], [1, 0, 7, 0], [0, 1, 0, 7]]
    identity = [[int(i == j) for j in range(4)] for i in range(4)]
    diagonalize = [[0, 0, 7, 0], [0, 0, 0, 7], [1, 0, -1, 0], [0, 1, 0, -1]]
    mix = divide([[13, 0, 0, 0], [0, 13, 0, 0], [0, 0, 2, -3], [0, 0, 3, 2]], 13)
    quaternion = divide([[2, -1, -1, -1], [1, 2, -1, 1], [1, 1, 2, -1], [1, -1, 1, 2]], 7)
    reference = multiply(multiply(diagonalize, mix), quaternion)
    sqrt_basis = [[1, 0, -1, 0], [0, 1, 0, -1], [0, 0, 2, 0], [0, 0, 0, 2]]
    odd_basis = multiply(sqrt_basis, divide([[13, 13, 0, 0], [13, -13, 0, 0],
                                            [0, 0, 1, -5], [0, 0, 5, 1]], 26))
    for basis, expected_det in [(reference, F(1, 13)), (odd_basis, F(-1, 13))]:
        assert multiply(list(zip(*basis)), multiply(gram, basis)) == identity
        assert determinant(basis) == expected_det
    assert all(x.denominator % 2 for row in reference for x in row)
    assert all(26 % x.denominator == 0 for row in odd_basis for x in row)
    # At 13, c = (13/alpha)*(4+s)/(4-s) has additive valuations -1 and 0.
    assert 21**2+4*439 == 13**3 and 4**2+439 == 5*7*13
    assert ((21+2*(-4)) % 13, (21+2*4) % 13) == (0, 3)
    assert ((4-4) % 13, (4+4) % 13) == (0, 8)
    assert 1+2*(-1) == -1 and 1+2*0 == 1
    orders = [6//gcd(6, t) for t in range(1, 7)]
    assert orders == [6, 3, 2, 3, 6, 1]
    print(f"Trace-reference determinants 1/13 and -1/13 verified. Degrees for 1..6 repeated four-dimensional blocks: {orders}.")


if __name__ == "__main__":
    check_oriented_ideals()
    check_trace_bases()
