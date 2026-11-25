"""Exact finite checks for the theta zero, its first unpaired term, and the rank certificate.

Run with Python 3.8 or later. The convergent series, its exact zero and
the uniform lattice inequalities are established in the companion proofs.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import gcd

from check_e8_theta_refinement import (
    ONE,
    R,
    S,
    X,
    ZERO,
    add,
    check_lattice,
    inner,
    ring_power,
    scale,
    short_vectors,
)


def check_supported_orbit():
    b = 7**5
    d = b + 1
    for k in (1, 3, 5, 7, 9, 15):
        m = b * 7**k
        a = (m - b) // 2
        assert (a % b, d % b) == (0, 1) and gcd(a, d) == 1

        def weight(x, y):
            return 2 * (d * (x * x + y * y) + b * x * y)

        h = weight(a, d)
        w = Fraction(2 * d) - Fraction(b * b, 2 * d)
        assert h == weight(a - m, d) == Fraction(d, 2) * (m * m + 4 * d * d - b * b)
        assert weight(a + m, d) - h == 4 * d * m * m
        assert w * (m - d) ** 2 - h > Fraction(d * m * m, 2) > 11
        assert d * m * m > 11 and h > 4 * d
        assert (2 * m * d) % 32 == 16
        assert 6 * d % 31 == b % 31
        if k == 1:
            u, w_col = -282492055, -94169621
            assert u * d - w_col * a == 1 and (u % b, w_col % b) == (1, 0)
            residues = [(2 * (x * x + d * d) + 12 * x * d) % 31 for x in (a, a - m)]
            assert residues == [21, 21] and h == 123445073616832
            print(
                f"Supported zero: two minima of weight {h}, reference tuple weight {4 * d}."
            )
    # Sharp lower bound for an off-root lift in the Euclidean E8 frame.
    for m in range(2, 18):
        a = m // 2
        excess = Fraction(2 * (a - 2 * m) ** 2 + 6 * a * a, 4) - 2 * a * a
        assert excess == m * m + (m if m % 2 else 0)


def check_shells():
    roots = [z for z in short_vectors(*check_lattice()) if z != ZERO]
    rows = [t for t in roots if inner(R, t) == 1]
    columns = [z for z in roots if inner(R, z) == 0]
    assert (len(rows), len(columns)) == (56, 126)
    for t in rows:
        assert Counter(inner(t, z) for z in columns) == {1: 27, 0: 72, -1: 27}
    b, m_ratio = 7**5, 49
    m = b * m_ratio
    x = scale(add(S, R, (m_ratio - 1) // 2), b)
    z = (0, 0, 0, 0, 0, 0, 0, 1)
    assert inner(z, R) == inner(z, S) == 0
    y = scale(z, b)
    h = inner(x, x) + inner(y, y)
    j = b * b * m_ratio * (m_ratio - 3)
    next_gap = b * b * m_ratio * (m_ratio - 1)
    weights = Counter()
    phases = Counter()
    for shift in [ZERO, *roots]:
        w = add(x, shift, m)
        gap = inner(w, w) + inner(y, y) - h
        weights[gap] += 1
        if gap == next_gap:
            phases[(20 * inner(y, y) + inner(w, y)) % 31] += 1
    assert sorted(weights.items())[:3] == [(0, 2), (j, 1), (next_gap, 27)]
    assert phases[8] == 15 and sorted(phases.values()) == [6, 6, 15]
    assert next_gap < 2 * j and j - 1 == 636699211245
    field = {i: ring_power(X, i, 2) for i in range(31)}
    assert field[0] == ONE and len(set(field.values())) == 31
    diagonal_difference = tuple(a ^ b for a, b in zip(field[4], field[28]))
    assert diagonal_difference == field[19] and (-24) % 31 == 7
    print(
        f"Coarse half and true fine coefficient agree in exactly {j - 1} normalized binary digits."
    )


def pairing(pair, column):
    if len(column) == 2:
        positive, negative = column
        return int(positive in pair) - int(negative in pair)
    return 1 - sum(i in column for i in pair)


def binary_field_rank(table):
    elements = [
        sum(c << i for i, c in enumerate(ring_power(X, j, 2))) for j in range(31)
    ]
    logs = {a: i for i, a in enumerate(elements)}

    def multiply(a, b):
        return elements[(logs[a] + logs[b]) % 31] if a and b else 0

    basis = {}
    for row in table:
        v = [elements[(8 + 25 * j) % 31] for j in row]
        for k in sorted(basis):
            if v[k]:
                factor = v[k]
                v = [x ^ multiply(factor, y) for x, y in zip(v, basis[k])]
        pivot = next((k for k, x in enumerate(v) if x), None)
        if pivot is not None:
            inv = elements[-logs[v[pivot]] % 31]
            basis[pivot] = [multiply(x, inv) for x in v]
    return len(basis)


def determinant(matrix):
    """Fraction-free elimination with row pivoting over the integers."""
    a = [row.copy() for row in matrix]
    n = len(a)
    previous, sign = 1, 1
    for k in range(n - 1):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                value = a[k][k] * a[i][j] - a[i][k] * a[k][j]
                assert value % previous == 0
                a[i][j] = value // previous
        previous = a[k][k]
    return sign * a[-1][-1]


def check_rank():
    pairs = list(combinations(range(8), 2))
    columns = list(permutations(range(8), 2)) + list(combinations(range(8), 4))
    table = [
        [sign * pairing(pair, col) for col in columns]
        for sign in (1, -1)
        for pair in pairs
    ]
    assert Counter(j for row in table for j in row) == {-1: 1512, 0: 4032, 1: 1512}
    assert binary_field_rank(table) == 28
    selected = [
        0,
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        9,
        10,
        11,
        12,
        14,
        16,
        17,
        18,
        19,
        22,
        24,
        25,
        26,
        28,
        32,
        33,
        35,
        40,
        42,
        56,
        57,
        58,
        59,
        60,
        61,
        71,
    ]
    matrix = [[int(table[i][j] == 1) for j in selected] for i in range(35)]
    cert = determinant(matrix)
    assert cert == -27 * 2**7
    # An independent three-value specialization checks the transformation
    # determinant from the proof; this calculation is over the integers.
    pos, mid, neg = 4, 3, 1
    three = {1: pos, 0: mid, -1: neg}
    transformed = [[three[table[i][j]] for j in selected] for i in range(35)]
    scalar_times_three = (
        (pos - neg) ** 7 * (pos + neg - 2 * mid) ** 27 * (3 * pos + 3 * neg + 8 * mid)
    )
    assert 3 * determinant(transformed) == cert * scalar_times_three
    print(
        f"The 56 by 126 residue table has rank 28. The 35 by 35 integer minor is {cert}."
    )


if __name__ == "__main__":
    check_supported_orbit()
    check_shells()
    check_rank()
