"""Local Artin generators, the nine completions of the affine field and discriminants."""

from math import comb, gcd
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "marked-directions-577"))
from residual_directions import P, local_digit


def order(value, modulus):
    result = 1
    x = value % modulus
    while x != 1:
        x = x * value % modulus
        result += 1
    return result


def upper_units():
    assert (P % 256, pow(5, 48, 256), pow(510, 48, P)) == (65, 65, 553)
    assert (order(P, 1792), order(5, P), order(4, P)) == (12, 576, 72)
    assert pow(P - 7, (P - 1) // 2, P) == P - 1
    field_degree = 72 * 2
    comparison_degree = (P - 1) * 12 // field_degree
    assert comparison_degree == 48
    values = []
    for a in (1, 2):
        artin_depth = 296 * a % (P - 1)
        kummer_depth = (1 - 296 * a) % (P - 1)
        assert artin_depth + kummer_depth == P
        hilbert = artin_depth * 12 * local_digit(a) % P
        values.append(hilbert * pow(comparison_degree, -1, P) % P)
    assert values == [35, 387]
    return values


def scalar_local_rows(t, a, coefficient):
    degree = {1: 3, 2: 4}[a]
    if coefficient > degree:
        return 0
    return comb(degree, coefficient) * pow(t, degree - coefficient, P) % P


def main():
    u, v = upper_units()
    reps = [0] + [pow(5, i, P) for i in range(8)]
    orbits = [{t * pow(4, n, P) % P for n in range(72)} for t in reps]
    assert [len(a) for a in orbits] == [1] + [72] * 8
    assert len(set.union(*orbits)) == P
    assert pow(5, 296, P) == 4 and pow(4, 2, P) == 16 and pow(4, P, P) == 4
    tame = {pow(4, n, P) for n in range(72)}
    for t in reps[1:]:
        assert {g for g in tame if g * t % P == t} == {1}
    print(
        "Squared inertia on the frame",
        16,
        "and on the eight nonzero point stabilizers",
        1,
    )
    results = [
        (t, u * scalar_local_rows(t, 1, 0) % P, v * scalar_local_rows(t, 2, 0) % P)
        for t in reps
    ]
    assert results == [
        (0, 0, 0),
        (1, 35, 387),
        (5, 336, 112),
        (25, 456, 183),
        (125, 454, 129),
        (48, 204, 422),
        (240, 112, 61),
        (46, 152, 43),
        (230, 536, 333),
    ]
    for t, a, b in results:
        print("affine orbit", t, "scalar unit readings", a, b)
    ordinary_depths = (280 // 8, 576 // 8)
    assert ordinary_depths == (35, 72)
    # The old lower radical uses Y after raising to 576. Its global pth
    # root-of-unity generator maps to Z^256 in that local embedding.
    lower_Z = -280 * 12 * pow(48, -1, P) % P
    lower_old = lower_Z * pow(256, -1, P) % P
    weight = -(2 * 72) % P
    assert (lower_Z, lower_old, weight) == (507, 446, 433)
    assert (lower_old * 497 % P, weight * 117 % P) == (94, 462)
    print("lower and diagonal integral controls in the stated conventions", 94, 462)
    tame_two = sum((i + 2) * 2 ** (i - 1) for i in range(1, 6))
    assert tame_two == 191 and gcd(576, 296 * 2) == 16
    d2 = P * 4023 + 18 * tame_two
    d7 = P * (P - 1) // 2
    for break_at_p in [2, 37]:
        dp = P * 568 + 16 * 35 + 8 * (P - 1) * (break_at_p + 1)
        assert (d2, d7, dp) == (2324709, 166176, {2: 342120, 37: 503400}[break_at_p])
        print(
            "degree",
            P**2,
            "local break",
            break_at_p,
            "discriminant exponents",
            d2,
            d7,
            dp,
        )
    assert P**2 == P + 2 * d7


if __name__ == "__main__":
    main()
