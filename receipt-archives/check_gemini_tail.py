"""Exact controls for the Gemini Neon tail review. Run with Python 3."""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product


def omega_power(exponent):
    """Return the coefficients of 1 and omega, where omega^2 = -1 - omega."""
    return ((1, 0), (0, 1), (-1, -1))[exponent % 3]


def chirp_overlap_squared(left, right):
    """Squared overlap after multiplying the first coordinate by sqrt(11/10)."""
    a, b = left
    c, d = right
    phases = [omega_power((c - a) * j * j + (d - b) * j) for j in (1, 2)]
    x = 11 + 10 * sum(u for u, v in phases)
    y = 10 * sum(v for u, v in phases)
    return F(x * x - x * y + y * y, 31**2)


def check_frames():
    chirps = list(product(range(3), repeat=2))
    axis_weights = [F(11, 31), F(10, 31), F(10, 31)]
    assert sum(axis_weights) == 1

    overlaps = [chirp_overlap_squared(u, v) for u, v in combinations(chirps, 2)]
    # Three pairs of coordinate axes, and each axis against each of nine chirps.
    overlaps += [F(0)] * 3
    overlaps += [w for w in axis_weights for _ in chirps]
    assert len(overlaps) == 66
    peak = max(overlaps)
    sg, eta0, dimension, total_rank = F(1, 4), F(1, 8), 3, 12
    assert peak == F(11, 31) < (1 + eta0) / dimension
    assert eta0 == sg / 2 and dimension / sg == total_rank

    # Off-diagonal entries of the sum of chirp projectors vanish exactly.
    for j, k in combinations(range(dimension), 2):
        phases = [omega_power(a * (j*j - k*k) + b * (j-k)) for a, b in chirps]
        assert tuple(map(sum, zip(*phases))) == (0, 0)
    diagonal = [F(dimension, total_rank) * (1 + len(chirps) * w) for w in axis_weights]
    assert diagonal == [F(65, 62), F(121, 124), F(121, 124)]
    swapped = [diagonal[1], diagonal[0], diagonal[2]]
    assert sum(diagonal) == sum(swapped) == dimension
    assert sum(x*x for x in diagonal) == sum(x*x for x in swapped)
    assert diagonal[0] - swapped[0] == F(9, 124)
    hs_squared = sum((x - 1)**2 for x in diagonal)
    assert hs_squared / dimension == F(9, 7688) < 5 * sg
    # Equality in the centered projector bound on the first axis.
    assert (diagonal[0] - 1)**2 == F(2, 3) * hs_squared
    print(f"Frame: {len(overlaps)} overlaps, maximum {peak}, fixed-axis change {diagonal[0]-swapped[0]}.")
    print(f"Normalized operator: {diagonal}. Centered squared norm / dimension: {hs_squared / dimension}.")


def check_character_shares():
    counts = Counter(t % 2 for t in (0, 1))  # TT inside Z/4, modulo {0,2}.
    p0, p1 = (F(counts[i], sum(counts.values())) for i in range(2))
    assert p0 - p1 == 0
    assert max(abs(p0 - F(4, 7)), abs(p1 - F(3, 7))) == F(1, 14)
    # In Q[T]/Phi_5, reduce T^4 = -(1 + T + T^2 + T^3).
    for k in (1, 3, 100):
        c = [4*k, 3*k+1, 3*k, 3*k, 3*k-1]
        reflected = [c[0], *reversed(c[1:])]
        assert sum(c) == sum(reflected) == 16*k
        assert [c[j] - c[4] for j in range(4)] != [reflected[j] - reflected[4] for j in range(4)]
        assert max(abs(F(x, 16*k) - F(y, 16)) for x, y in zip(c, (4, 3, 3, 3, 3))) == F(1, 16*k)
    print("Character shares: the order-two coefficient vanishes at tolerance 1/14; the order-five samples distinguish conjugation.")


def check_splitting_and_scales():
    squares = {i*i % 3 for i in range(3)}
    assert (-1) % 3 not in squares and (-7) % 3 not in squares and 7 % 3 in squares
    assert F(1, 50) > F(1, 52)
    for exponent in (4, 6, 8, 10):
        assert (10**exponent)**3 < 26**400   # x^(3 epsilon/8) < 26 for epsilon = 1/50.
    print("At 3 the three quadratic characters have signs (-,-,+). All four injected-zero scales miss the size threshold.")


if __name__ == "__main__":
    check_frames()
    check_character_shares()
    check_splitting_and_scales()
