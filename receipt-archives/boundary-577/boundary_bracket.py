"""Exact polynomial model and the ordinary quadratic bracket at the nonsplit residue."""

from fractions import Fraction
from math import comb
from pathlib import Path
import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "marked-directions-577"))
from matrix_checks import E, L, V, bracket, dag


def chain(top, degree):
    basis = [None] * (degree + 1)
    basis[degree] = top
    for i in range(degree, 0, -1):
        basis[i - 1] = bracket(L, basis[i]) * Fraction(-1, i)
    return basis


def coefficients():
    even = chain(E(1, 2) - E(2, 3), 2)
    odd = chain(V, 4)
    ans = {}
    for i, A in enumerate(odd):
        assert np.array_equal(dag(A), A)
        for j, B in enumerate(odd[i + 1 :], i + 1):
            C = bracket(A, B)
            if not np.any(C):
                continue
            degree = i + j - 3
            scalar = next(
                Fraction(a, b) for a, b in zip(C.flat, even[degree].flat) if b
            )
            assert np.array_equal(C, scalar * even[degree])
            ans[i, j] = (degree, scalar)
    assert ans == {
        (0, 3): (0, Fraction(-1, 8)),
        (0, 4): (1, Fraction(-1, 2)),
        (1, 2): (0, Fraction(1, 16)),
        (1, 3): (1, Fraction(1, 16)),
        (1, 4): (2, Fraction(-1, 8)),
        (2, 3): (2, Fraction(1, 16)),
    }
    return even, odd


def test_translation(basis, shift):
    identity = np.eye(3, dtype=object)
    r = identity + shift * L + Fraction(shift * shift, 2) * (L @ L)
    ri = identity - shift * L + Fraction(shift * shift, 2) * (L @ L)
    for j, b in enumerate(basis):
        polynomial = sum(
            (comb(j, i) * (-shift) ** (j - i) * basis[i] for i in range(j + 1)),
            start=np.zeros((3, 3), dtype=object),
        )
        assert np.array_equal(r @ b @ ri, polynomial)


def main():
    even, odd = coefficients()
    for b in [even, odd]:
        test_translation(b, 7)
    assert all(np.array_equal(-dag(b), b) for b in even)
    assert np.array_equal(bracket(E(1, 2) + E(2, 3), V), np.zeros((3, 3), dtype=object))
    print(
        "The even module is the translated quadratic polynomials, the odd module the translated quartics."
    )
    print(
        "At the ordinary prime the two upper odd lines commute; six distinct quartic coefficient pairs give global even brackets."
    )


if __name__ == "__main__":
    main()
