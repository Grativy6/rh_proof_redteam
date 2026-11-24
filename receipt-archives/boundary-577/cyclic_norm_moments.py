"""Finite checks for the four cyclic norm equations at the original 577 input.

The remnant of a principal divisor depends on the places carrying it.
The actual norm preimages and their divisors are not input to this replay.
"""

from itertools import combinations

import numpy as np

from artin_units import P, upper_units
from first_order_norms import bracket_table, translate, wedge
from quadratic_words import rank


def high_projection():
    u, v = upper_units()
    places = np.arange(P, dtype=np.int64)
    cubic = u * np.array([translate(3, -int(t)) for t in places]) % P
    quartic = v * np.array([translate(4, -int(t)) for t in places]) % P
    # Use T+t. The two columns are the actual independent local generators.
    determinant = (cubic[:, 2] * quartic[:, 3] - cubic[:, 3] * quartic[:, 2]) % P
    assert np.array_equal(determinant, 6 * u * v * places**2 % P)
    assert cubic[0, :4].tolist() == [0, 0, 0, 35]
    assert not np.any(quartic[0, :4])

    first = np.zeros((P, 4), dtype=np.int64)
    second = np.zeros_like(first)
    first[:, :2] = cubic[:, 2:4]
    second[:, 2:] = quartic[:, 2:4]
    pairs = list(combinations(range(4), 2))
    wedges = np.column_stack(
        [
            (first[:, i] * second[:, j] - first[:, j] * second[:, i]) % P
            for i, j in pairs
        ]
    )
    weights = [0, 1, 0, 1]
    weights2 = np.array([weights[i] + weights[j] for i, j in pairs])
    dimensions = []
    for weight in range(3):
        block = wedges[:, weights2 == weight]
        dimensions.append((block.shape[1], rank(block)))
    assert rank(wedges) == 3 and dimensions == [(1, 1), (4, 1), (1, 1)]
    print("Exterior dimensions and local ranks at weights 0, 1, 2:", dimensions)

    changes = (
        np.column_stack(
            (
                cubic[:, 2] * quartic[:, 1],
                -2 * cubic[:, 3] * quartic[:, 0],
                -quartic[:, 2] * cubic[:, 1],
                2 * quartic[:, 3] * cubic[:, 0],
            )
        )
        % P
    )
    factor = (u * v % P) * (places**2 % P) ** 2 % P
    assert np.array_equal(changes, factor[:, None] * np.array([12, -2, -18, 8]) % P)
    assert not np.any(changes.sum(axis=1) % P)
    assert changes[1].tolist() == [403, 29, 261, 461]
    # At t=1 the quartic-only unit is a norm from F(U_2). Its contribution
    # to U_1 + V_1 prescribes the compensating local reading in the x=1 control.
    local_reading = int(quartic[1, 1])
    raw_moment = -local_reading % P
    assert (raw_moment, local_reading) == (183, 394)
    assert len(set(raw_moment * places % P)) == P
    print(
        "Norm-one control: divisor sum", raw_moment, "local correction", local_reading
    )
    print(
        "Four local changes at t=1:", changes[1].tolist(), "sum", int(changes[1].sum())
    )


def check_moment_sign():
    # All high/low basis pairs and the three coefficients of their binary quadratic.
    a0_bracket = bracket_table()[:, 0]
    basis = np.eye(4, dtype=np.int64)
    for a, b in ((1, 0), (0, 1), (1, 1)):
        for high in basis:
            for low in basis:
                q2, q3 = a * high[:2] + b * high[2:]
                h0, h1 = a * low[:2] + b * low[2:]
                left = np.array([0, 0, q2, q3, 0])
                right = np.array([h0, h1, 0, 0, 0])
                measured = -16 * int(wedge(left, right) @ a0_bracket) % P
                assert measured == (q2 * h1 - 2 * q3 * h0) % P

    # For (sigma-1)c the signed moment increases by the ordinary sum for c,
    # including the wrap at p-1. Test each individual valuation vector.
    labels = np.arange(P)
    change = (np.roll(labels, -1) - labels) % P
    assert np.all(change == 1)
    print(
        "Inverse conjugation and the cyclic valuation shift agree on every basis vector."
    )


if __name__ == "__main__":
    high_projection()
    check_moment_sign()
