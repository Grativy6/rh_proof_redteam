"""Evaluate the three global commutators directly in F_577[t]/(t^3)."""

from math import comb
from pathlib import Path
import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from artin_units import P, upper_units
from boundary_bracket import coefficients, L


def residue(matrix):
    def convert(value):
        return int(value.numerator) * pow(int(value.denominator), -1, P) % P

    return np.array([[convert(x) for x in row] for row in matrix], dtype=np.int64)


IDENTITY = np.eye(3, dtype=np.int64)
ZERO = np.zeros((3, 3), dtype=np.int64)
LOWER = residue(L)


def product(a, b):
    return tuple(
        sum((a[j] @ b[i - j] for j in range(i + 1)), start=ZERO.copy()) % P
        for i in range(3)
    )


def inverse(a):
    # In this replay the constant term is identity or unipotent of index 3.
    n = a[0] - IDENTITY
    a0 = (IDENTITY - n + n @ n) % P
    assert np.array_equal(a0 @ a[0] % P, IDENTITY)
    a1 = -a0 @ a[1] @ a0 % P
    a2 = -(a0 @ (a[2] @ a0 + a[1] @ a1)) % P
    out = (a0, a1, a2)
    assert all(
        np.array_equal(x, y) for x, y in zip(product(a, out), (IDENTITY, ZERO, ZERO))
    )
    return out


def conjugate(g, h):
    return product(product(g, h), inverse(g))


def commutator(g, h):
    return product(conjugate(g, h), inverse(h))


def exponential(tangent, second):
    return (IDENTITY, tangent % P, (tangent @ tangent * pow(2, -1, P) + second) % P)


def rank(rows):
    work = np.array(rows, dtype=np.int64).copy() % P
    pivot = 0
    for i in range(work.shape[1]):
        which = np.flatnonzero(work[pivot:, i])
        if not len(which):
            continue
        j = pivot + int(which[0])
        work[[pivot, j]] = work[[j, pivot]]
        work[pivot] = work[pivot] * pow(int(work[pivot, i]), -1, P) % P
        for j in range(len(work)):
            if j != pivot:
                work[j] = (work[j] - work[j, i] * work[pivot]) % P
        pivot += 1
    return pivot


def frame_traces(a, b, gu, gv, residual_translation):
    # theta(g) = J g^(-t) J. Conjugation by the multiplier -1 element
    # gives theta(g), and [c,g] has trivial residual image at both units.
    J = np.fliplr(IDENTITY)
    mark = np.diag([4, 1, pow(4, -1, P)])
    residual_h = residual_translation @ mark % P
    h = (residual_h, np.arange(9, dtype=np.int64).reshape(3, 3), ZERO)
    for unit, target in ((gu, 341 * a), (gv, 394 * b)):
        theta = tuple(J @ x.T @ J for x in inverse(unit))
        comm = product(theta, inverse(unit))
        test = product(comm, h)
        assert np.array_equal(test[0], h[0])
        assert int(np.trace(test[1] - h[1])) % P == target % P
    assert 341 * 394 % P == 490


def main():
    even, odd = (list(map(residue, basis)) for basis in coefficients())
    u, v = upper_units()
    R = (IDENTITY + LOWER + pow(2, -1, P) * (LOWER @ LOWER)) % P
    for d in [3, 4]:
        translations = [
            [comb(d, i) * pow(-t, d - i, P) % P for i in range(d + 1)]
            for t in range(d + 1)
        ]
        assert rank(translations) == d + 1

        def bracket(i, j):
            return (odd[i] @ odd[j] - odd[j] @ odd[i]) % P

        alternating = np.array(
            [[int(bracket(i, j)[1, 0]) for j in range(d + 1)] for i in range(d + 1)]
        )
        assert rank(alternating) == 4
        for i in range(2, d + 1):
            for j in range(2, d + 1):
                val = bracket(i, j)
                assert val[1, 0] == 0 and val[0, 0] == 0
        all_brackets = [
            bracket(i, j).ravel() for i in range(d + 1) for j in range(i + 1, d + 1)
        ]
        assert rank(all_brackets) == 3
    for a, b in ((1, 0), (0, 1), (1, 1), (17, 31), (0, 0)):
        # Arbitrary allowed even corrections at the input units and arbitrary
        # odd corrections on the translating lift drop out of the commutators.
        tau = product(exponential(odd[2] + 3 * odd[4], even[1]), (R, ZERO, ZERO))
        gu = exponential(u * a * odd[3], 7 * even[2] + 4 * even[1])
        gv = exponential(v * b * odd[4], 5 * even[0])
        frame_traces(a, b, gu, gv, R)
        for g, h, expected in (
            (gu, gu, 167 * a * a),
            (gu, gv, 247 * a * b),
            (gv, gv, 163 * b * b),
        ):
            pair = commutator(g, conjugate(tau, h))
            result = commutator(tau, commutator(tau, pair))
            assert all(
                np.array_equal(x, y)
                for x, y in zip(result, (IDENTITY, ZERO, expected * LOWER % P))
            )
    print(
        "Raw trace derivatives on the linked subgroup are 341 a and 394 b. Determinant 490."
    )
    print(
        "Second-order lower entries on the three global words are 167 a^2, 247 a b, and 163 b^2 modulo 577."
    )
    print(
        "A pure U tangent has four first-order image dimensions. A V component gives five. The central bracket spans three."
    )


if __name__ == "__main__":
    main()
