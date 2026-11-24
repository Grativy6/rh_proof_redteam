"""Compute the actual exterior-power norm obstructions at 577.

The local decomposition planes come from the two Artin generators. The
global identification with a norm quotient uses Tate's class-field theorem.
The four unknown norm-test directions are not input to this replay.
"""

from itertools import combinations
from math import comb
import numpy as np

from artin_units import P, upper_units
from boundary_bracket import coefficients
from quadratic_words import rank, residue


def translate(d, t, size=5):
    return np.array(
        [comb(d, i) * pow(-t, d - i, P) % P if i <= d else 0 for i in range(size)],
        dtype=np.int64,
    )


PAIRS = list(combinations(range(5), 2))


def wedge(x, y):
    return np.array([(x[i] * y[j] - x[j] * y[i]) % P for i, j in PAIRS], dtype=np.int64)


def bracket_table():
    even, odd = coefficients()
    even = np.array([residue(t) for t in even])
    odd = np.array([residue(t) for t in odd])
    table = np.zeros((len(PAIRS), 3), dtype=np.int64)
    for row, (i, j) in enumerate(PAIRS):
        matrix = (odd[i] @ odd[j] - odd[j] @ odd[i]) % P
        if not np.any(matrix):
            continue
        d = i + j - 3
        k = next(index for index in np.ndindex(3, 3) if even[d][index])
        scale = int(matrix[k]) * pow(int(even[d][k]), -1, P) % P
        assert np.array_equal(matrix, scale * even[d] % P)
        table[row, d] = scale
    return table


def check_radicals(table):
    # Compare all five Pfaffian minors with the coefficients of a quadratic
    # polynomial squared. Test every projective dual direction over F_577.
    u, v = np.indices((P, P), dtype=np.int64)
    directions = np.vstack(
        (
            np.column_stack((np.ones(P * P, dtype=np.int64), u.ravel(), v.ravel())),
            np.column_stack(
                (np.zeros(P, dtype=np.int64), np.ones(P, dtype=np.int64), np.arange(P))
            ),
            [0, 0, 1],
        )
    )
    u, v, w = directions.T
    entries = (16 * table @ directions.T) % P
    form = {ij: entry for ij, entry in zip(PAIRS, entries)}
    minors = []
    for i in range(5):
        a, b, c, d = [k for k in range(5) if k != i]
        pf = form[a, b] * form[c, d] - form[a, c] * form[b, d] + form[a, d] * form[b, c]
        minors.append((-1) ** i * pf % P)
    expected = (
        -2 * np.array([w * w, -4 * v * w, 2 * u * w + 4 * v * v, -4 * v * u, u * u]) % P
    )
    assert np.array_equal(minors, expected) and np.all(np.any(expected, axis=0))
    for i in range(5):
        action = sum(
            (form[i, j] * minors[j] if i < j else -form[j, i] * minors[j])
            for j in range(5)
            if j != i
        )
        assert np.all(action % P == 0)
    assert len(directions) == 333507
    print(
        "All",
        len(directions),
        "dual directions have rank four. Number of rank-four quotients:",
        sum(P**i for i in range(5)),
    )


def compute_knots():
    table = bracket_table()
    u, v = upper_units()
    local = []
    joint = []
    for t in range(P):
        c = translate(3, t)
        d = translate(4, t)
        local.append(wedge(c, d))
        joint.append(np.outer(c[:4], d).ravel())
    assert rank(local) == 7 and rank(joint) == 8
    assert not np.any(np.array(local) @ table % P) and rank(table) == 3
    rows = np.array(
        [wedge(u * translate(3, 0), v * translate(4, t)) @ table % P for t in (1, 2, 3)]
    )
    assert (
        rows.tolist() == [[467, 357, 330], [548, 548, 166], [322, 407, 85]]
        and rank(rows) == 3
    )
    det = (
        sum(
            rows[0, i]
            * (
                rows[1, (i + 1) % 3] * rows[2, (i + 2) % 3]
                - rows[1, (i + 2) % 3] * rows[2, (i + 1) % 3]
            )
            for i in range(3)
        )
        % P
    )
    assert det == 40
    assert (comb(4, 2), comb(5, 2), comb(5, 2) - 7, comb(9, 2) - 8) == (6, 10, 3, 28)
    print("Norm-defect dimensions U, V, mixed, joint:", 6, 10, 3, 28)
    print(
        "Three mixed commutators in the even basis:", rows.tolist(), "determinant", det
    )
    check_radicals(table)


def four_slopes(row_vectors):
    """Whether four rank-one readings of binary quadratics admit a linear ratio.

    The vectors may be scaled separately. A zero vector is an actual sampled
    common root. A nonsampled common quadratic root is also detected.
    """
    if any(x % P == y % P == 0 for x, y in row_vectors):
        return True
    matrix = [[y, s * y, -x, -s * x] for s, (x, y) in enumerate(row_vectors, 1)]
    return rank(matrix) < 4


def check_bicyclic_preimage():
    u, v = upper_units()
    table = bracket_table()
    for slope in (1, 2, 3, 4):
        for t in range(P):
            cubic = u * translate(3, -t) % P
            quartic = slope * v * translate(4, -t) % P
            determinant = (cubic[0] * quartic[1] - cubic[1] * quartic[0]) % P
            assert determinant == u * v * slope * pow(t, 6, P) % P
            if not t:
                assert cubic[:3].tolist() == [0, 0, 0] and cubic[3] == 35
                assert not np.any(quartic[:4])
    # Transporting an Artin element to the reference place uses inverse
    # conjugation. Read its A0 bracket directly in the original matrix basis.
    for i, j, h2, h3 in [(1, 0, 0, 1), (0, 1, 1, 0), (35, 387, 94, 462)]:
        left = np.array([i, j, 0, 0, 0])
        right = np.array([0, 0, h2, h3, 0])
        correction = int(-wedge(left, right) @ table[:, 0]) % P
        assert correction == (2 * i * h3 - j * h2) * pow(16, -1, P) % P
    print(
        "Bicyclic preimage test: local projection has rank two off the origin; only the cubic line remains at zero."
    )


def check_criterion():
    for e in (1, 2, 5, 19):
        xs = [1, 2, 3, 4]
        assert not four_slopes([(s * s, 1) for s in xs])
        assert four_slopes([((s - e) * s, s - e) for s in xs])
        assert four_slopes([(s * s - 5, e * (s * s - 5)) for s in xs])
        assert not four_slopes(
            [((s * s + 3) * t, t) for s, t in zip(xs, (17, 21, 42, 31))]
        )
    assert pow(5, (P - 1) // 2, P) == P - 1
    y_d = 82 * pow(511, -1, P) % P
    h_lower = -2 * 94 % P
    h_diag = 2 * (-144) * 413 % P
    assert (y_d, h_lower, h_diag) == (296, 389, 495)
    assert (
        h_lower * 495 + h_diag * 188
    ) % P == 0 and h_diag * 35 % P == 2 * y_d % P == 15
    print(
        "Local-reading controls: (495,188,0) and (0,35,0); the four actual norm kernels still need evaluation."
    )


if __name__ == "__main__":
    compute_knots()
    check_bicyclic_preimage()
    check_criterion()
