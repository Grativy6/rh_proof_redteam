"""Exact checks for the weighted triangle and the nonsplit polarization kernel.

The elliptic curve is y^2=x^3+1 over F_5[s]/(s^2-2). The unbounded
statements and the connection to the released maps are proved in the papers.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import factorial


def add(x, y):
    return ((x[0] + y[0]) % 5, (x[1] + y[1]) % 5)


def neg(x):
    return (-x[0] % 5, -x[1] % 5)


def mul(x, y):
    a, b = x
    c, d = y
    return ((a * c + 2 * b * d) % 5, (a * d + b * c) % 5)


def inverse(x):
    norm = (x[0] * x[0] - 2 * x[1] * x[1]) % 5
    scale = pow(norm, -1, 5)
    return (x[0] * scale % 5, -x[1] * scale % 5)


ONE = (1, 0)
ZERO = (0, 0)


def point_add(p, q):
    if p is None:
        return q
    if q is None:
        return p
    x, y = p
    X, Y = q
    if x == X and y == neg(Y):
        return None
    if p == q:
        slope = mul(mul((3, 0), mul(x, x)), inverse(add(y, y)))
    else:
        slope = mul(add(Y, neg(y)), inverse(add(X, neg(x))))
    rx = add(mul(slope, slope), neg(add(x, X)))
    return (rx, add(mul(slope, add(x, neg(rx))), neg(y)))


def check_elliptic_phase():
    field = list(product(range(5), repeat=2))
    curve = {None} | {
        (x, y)
        for x, y in product(field, repeat=2)
        if mul(y, y) == add(mul(mul(x, x), x), ONE)
    }
    p = (ZERO, ONE)
    q = (ONE, (0, 1))
    assert len(curve) == 36 and p in curve and q in curve
    tors = {v for v in curve if point_add(v, point_add(v, v)) is None}
    generated = {
        point_add(v, w)
        for v in [None, p, point_add(p, p)]
        for w in [None, q, point_add(q, q)]
    }
    assert tors == generated and len(tors) == 9
    y = q[1]
    zeta = mul(add(ONE, neg(y)), inverse(add(ONE, y)))
    assert zeta == (2, 2) and add(add(mul(zeta, zeta), zeta), ONE) == ZERO
    return zeta


def carry_add(u, v, k):
    a, b, i, j = u
    c, d, m, n = v
    return (
        (a + c) % k,
        (b + d) % k,
        (i + m - (b + d) // k) % k,
        (j + n + (a + c) // k) % k,
    )


def check_kernel(k):
    elems = list(product(range(k), repeat=4))

    def to_pair(u):
        a, b, i, j = u
        return (a + k * j, (b - k * i) % (k * k))

    assert len({to_pair(u) for u in elems}) == k**4
    counts = Counter()
    for u in elems:
        a, b = to_pair(u)
        z = (0, 0, 0, 0)
        for order in range(1, k * k + 1):
            z = carry_add(z, u, k)
            if z == (0, 0, 0, 0):
                break
        assert z == (0, 0, 0, 0)
        counts[order] += 1
        if k == 3:
            for v in elems:
                c, d = to_pair(v)
                assert to_pair(carry_add(u, v, k)) == (
                    (a + c) % (k * k),
                    (b + d) % (k * k),
                )
    if k == 3:
        assert counts == {1: 1, 3: 8, 9: 72}
    return counts


def triangle_full(x, y, z):
    x, y, z = sorted((Fraction(x), Fraction(y), Fraction(z)), reverse=True)
    return x + y + max(0, (x + y) * z - x * y) ** 2 / (4 * x * y * z)


def check_triangles():
    # For the root shell the pairwise cosines are half-integers. Positivity
    # of the 3-by-3 Gram matrix gives an independent finite upper bound.
    cosines = [Fraction(i, 2) for i in range(-2, 3)]
    gram = [
        (a, b, c)
        for a, b, c in product(cosines, repeat=3)
        if 1 + 2 * a * b * c - a * a - b * b - c * c >= 0
    ]
    for x, y, z in product(range(1, 5), repeat=3):
        hi, mid, lo = sorted((x, y, z), reverse=True)
        root = max((x * (1 - a) + y * (1 - b) + z * (1 - c)) / 2 for a, b, c in gram)
        assert root == max(hi + mid, Fraction(3, 4) * (x + y + z))
        assert root <= triangle_full(x, y, z)
    assert triangle_full(1, 1, 1) == Fraction(9, 4)
    assert triangle_full(1, 1, Fraction(3, 4)) == Fraction(25, 12)
    assert Fraction(25, 12) - Fraction(33, 16) == Fraction(1, 48)
    assert triangle_full(1, 1, Fraction(1, 2)) == 2


def check_gates(g, r, n):
    assert g % 2 == 0 and n > 1 + 2 * g * 2 ** (g // 2)
    assert r * 2 ** (g // 2) > g * 3**g * factorial(g) * n**g
    assert r * n > 6 * n**g * factorial(g)


def check_integral_frame():
    from check_e8_theta_refinement import GRAM, R, S, add as vec_add, inner, scale

    v = (4, 5, 7, 10, 8, 6, 4, 2)
    assert tuple(sum(a * b for a, b in zip(row, v)) for row in GRAM) == R
    tri = (R, scale(S, -1), vec_add(S, R, -1))
    assert all(inner(u, w) == (2 if u == w else -1) for u, w in product(tri, repeat=2))
    assert all(not any((z * z + 1) % k == 0 for z in range(k)) for k in (3, 9, 27))
    assert (3 * 1 - 1**2) == 2
    check_gates(24, 3**400, 3**12)
    m = 9 * 3**412
    check_gates(24, 3**20100, m * m)
    assert m * m > 30 * (3**412 - 1) ** 2


if __name__ == "__main__":
    print("Primitive cubic Weil value over F25:", check_elliptic_phase())
    print("Orders in the order-81 kernel:", dict(sorted(check_kernel(3).items())))
    check_kernel(5)
    check_triangles()
    check_integral_frame()
    print("The three-quarter triangle gap is 1/48. The E8 contraction gives 2*4-7=1.")
