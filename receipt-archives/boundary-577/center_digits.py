"""Locate the relaxed 577-adic weight by exact finite divisor sums.

Use --direct 3 to repeat the third-digit test by a single pass through the
units modulo 577**3. The normal replay also tests the second digit directly.
"""

import argparse
from functools import lru_cache
from math import comb

P = 577
C = 256
BASE_TWIST = 296
WEIGHT_STEP = P - 1
EXPECTED = (460, 487, 236, 23, 70, 140, 361, 374, 458, 573, 243)


def tame_character(modulus, depth):
    """Values of psi inverse, with the value zero on even residues."""
    root = pow(5, P ** (depth - 1), modulus)
    values = [0] * C
    for i in range(64):
        a = pow(5, i, C)
        values[a] = values[-a % C] = pow(root, -351 * i, modulus)
    return values


def power_sums(count, degree, modulus):
    """Sums of x**j over 0 <= x < count, for 0 <= j <= degree."""
    result = []
    for j in range(degree + 1):
        lower = sum(comb(j + 1, i) * result[i] for i in range(j))
        result.append(
            (pow(count, j + 1, modulus) - lower) * pow(j + 1, -1, modulus) % modulus
        )
    return result


@lru_cache(maxsize=None)
def moments(depth):
    if not 1 <= depth < P:
        raise ValueError("Power-sum denominators must be units")
    modulus = P**depth
    char = tame_character(modulus, depth)
    upper = [
        sum(char[(a + modulus * j) % C] for j in range(C // 2, C)) % modulus
        for a in range(C)
    ]
    count, extra = divmod(P ** (depth - 1), C)
    short = power_sums(count, depth - 1, modulus)
    long = power_sums(count + 1, depth - 1, modulus)
    by_residue = []
    for v in range(C):
        sums = long if v < extra else short
        by_residue.append(
            [
                sum(
                    comb(j, i) * pow(v, j - i, modulus) * pow(C, i, modulus) * sums[i]
                    for i in range(j + 1)
                )
                % modulus
                for j in range(depth)
            ]
        )
    return [
        [
            sum(upper[(r + P * v) % C] * by_residue[v][j] for v in range(C)) % modulus
            for j in range(depth)
        ]
        for r in range(C)
    ]


def half_sum(depth, twist):
    """Sum psi(a)^-1 a^(-twist-1) on the upper half of units modulo C*p^depth."""
    modulus = P**depth
    table = moments(depth)
    coeff = [1]
    for j in range(1, depth):
        coeff.append(coeff[-1] * (-twist - j) * pow(j, -1, modulus) % modulus)
    total = 0
    for r in range(1, P):
        step = P * pow(r, -1, modulus) % modulus
        series = 0
        for j in reversed(range(depth)):
            series = (series * step + coeff[j] * table[r % C][j]) % modulus
        total += series * pow(r, -twist - 1, modulus)
    return total % modulus


def direct(depth, twist):
    """Enumerate the cyclic units, using CRT to impose the half interval."""
    modulus = P**depth
    order = (P - 1) * P ** (depth - 1)
    assert all(pow(5, order // q, modulus) != 1 for q in (2, 3, P) if order % q == 0)
    char = tame_character(modulus, depth)
    inverse = pow(modulus, -1, C)
    weights = [
        sum(char[a] for a in range(1, C, 2) if (a - r) * inverse % C >= C // 2)
        % modulus
        for r in range(C)
    ]
    step = pow(5, -twist - 1, modulus)
    a = weight = 1
    total = 0
    for _ in range(order):
        total += weights[a % C] * weight
        a = a * 5 % modulus
        weight = weight * step % modulus
    assert (a, weight) == (1, 1)
    return total % modulus


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--direct", choices=(2, 3), type=int, default=2)
    args = parser.parse_args()
    assert half_sum(1, BASE_TWIST) == 0
    assert half_sum(2, BASE_TWIST) == direct(2, BASE_TWIST) == 287 * P
    u = 0
    print("depth   next digit   least twist at this depth")
    for depth, expected in enumerate(EXPECTED, start=2):
        unit = P ** (depth - 1)
        stride = P ** (depth - 2)
        twist = BASE_TWIST + WEIGHT_STEP * u
        residue = half_sum(depth, twist)
        assert residue % unit == 0
        slope = (half_sum(depth, twist + WEIGHT_STEP * stride) - residue) % (unit * P)
        assert slope == 540 * unit
        digit = -(residue // unit) * pow(540, -1, P) % P
        assert digit == expected
        u += digit * stride
        new_twist = BASE_TWIST + WEIGHT_STEP * u
        assert half_sum(depth, new_twist) == 0
        if depth == args.direct:
            assert direct(depth, new_twist) == 0
        print(depth, digit, new_twist)
    assert half_sum(3, 265256) == 132 * P**2
    assert half_sum(4, 162120680) == 77 * P**3
    print("At twist 162120680 the relaxed length is exactly three.")


if __name__ == "__main__":
    main()
