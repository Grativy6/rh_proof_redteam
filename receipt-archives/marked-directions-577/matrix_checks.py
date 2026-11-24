"""Integer checks for the symmetric mark, the two trace words, and the first compatible relation terms."""

from fractions import Fraction
from itertools import product
import numpy as np


def E(i, j):
    mat = np.zeros((3, 3), dtype=object)
    mat[i - 1, j - 1] = 1
    return mat


identity = E(1, 1) + E(2, 2) + E(3, 3)
J = E(1, 3) + E(2, 2) + E(3, 1)
L = E(2, 1) - E(3, 2)
U = E(1, 2) + E(2, 3)
V = E(1, 3)


def inv(m):
    a = m.tolist()
    cof = np.empty((3, 3), dtype=object)
    for i, j in product(range(3), repeat=2):
        u = [k for k in range(3) if k != i]
        v = [k for k in range(3) if k != j]
        cof[i, j] = (-1) ** (i + j) * (
            a[u[0]][v[0]] * a[u[1]][v[1]] - a[u[0]][v[1]] * a[u[1]][v[0]]
        )
    det = sum(m[0, j] * cof[0, j] for j in range(3))
    assert det != 0
    return cof.T * Fraction(1, det)


def dag(m):
    return J @ m.T @ J


def theta(m):
    return dag(inv(m))


def old_mark(m):
    return m - dag(m)


def mark(m):
    return old_mark(m) - old_mark(inv(m))


def bracket(a, b):
    return a @ b - b @ a


def exp_root(m, t):
    assert not np.any(m @ m @ m)
    return identity + t * m + Fraction(t * t, 2) * (m @ m)


def terms(limit):
    return sorted(
        (a + b + c, a, b, c)
        for a, b, c in product(range(limit + 1), repeat=3)
        if a + b + c <= limit and -a + b + 2 * c == -1 and (b + c) % 2 == 0
    )


def main():
    equal = np.array_equal
    assert equal(-dag(L), L) and equal(-dag(U), -U) and equal(-dag(V), -V)
    assert equal(bracket(L, V), U)
    assert equal(bracket(bracket(U, bracket(bracket(U, L), L)), L), 3 * L)
    x = 7
    assert equal(theta(exp_root(L, x)), exp_root(L, x))
    assert equal(theta(exp_root(U, x)), exp_root(U, -x))
    assert equal(theta(exp_root(V, x)), exp_root(V, -x))
    s = Fraction(4)
    q = 577
    m = np.diag([s, 1, 1 / s]) + q * (E(1, 2) + E(2, 3))
    assert equal(old_mark(m), np.diag([s - 1 / s, 0, 1 / s - s]))
    assert old_mark(theta(m))[0, 1] == -q * (s - 1 / s)
    assert equal(mark(m), mark(theta(m)))
    assert terms(7) == [(1, 1, 0, 0), (5, 3, 2, 0), (6, 4, 1, 1), (7, 5, 0, 2)]
    # Use a diagonal mark so that its spectral projectors have literal entries.
    g = np.diag([s, 1, 1 / s])
    W = mark(g)
    projectors = []
    for i in range(3):
        h = identity.copy()
        for j in range(3):
            if i != j:
                h = h @ (W - W[j, j] * identity) * Fraction(1, W[i, i] - W[j, j])
        assert equal(h, E(i + 1, i + 1))
        projectors.append(h)
    p1, p2, p3 = projectors
    mat = (
        (identity + 2 * E(2, 1))
        @ (identity + 3 * E(3, 2))
        @ (identity + 5 * E(1, 2))
        @ (identity + 7 * E(1, 3))
    )
    found = []
    for M in [mat, theta(mat)]:
        A = (M + theta(M)) * Fraction(1, 2)
        B = (M - theta(M)) * Fraction(1, 2)
        x, u, v = A[1, 0], B[0, 1], B[0, 2]
        assert x and u and v
        pair = np.trace(p2 @ A @ p1 @ B)
        triple = np.trace(p2 @ A @ p1 @ B @ p3 @ dag(A))
        assert pair == x * u and triple == x * x * v
        found.append((pair, triple))
    assert found[1] == tuple(-x for x in found[0])
    print("First compatible nonlinear terms have degrees 5, 6, 7.")
    print("The pair and triple trace expressions change sign under duality:", found)


if __name__ == "__main__":
    main()
