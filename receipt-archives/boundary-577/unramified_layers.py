"""Check the affine ideal-class chains and the four unramified Frobenius controls.

The proof of the rank bound uses the norm and extension of ideals in the
specified unramified cyclic CM extension. This program checks its finite
weight calculation and the global and local Kummer symbols used to choose
the four ideal-class generators.
"""

from math import comb, factorial, gcd
from pathlib import Path
import sys

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "marked-directions-577"))
from residual_directions import P, local_digit, upper
from bounds import char2, prime
from fourier_witness import primitive, roots
from class_tower import abelian_moments

WEIGHTS = (276, 336, 407, 447)
ORDER = P - 1


def check_layers():
    # For weight b outside the four generators, all four allowed degrees
    # are positive. A relation starts at least one degree after its source.
    lengths = [(a - WEIGHTS[j - 1]) % ORDER for j, a in enumerate(WEIGHTS)]
    assert lengths == [405, 60, 71, 40]
    first = [
        (a - d) % ORDER for a, length in zip(WEIGHTS, lengths) for d in range(length)
    ]
    assert sorted(first) == list(range(ORDER))
    for b in set(range(ORDER)).difference(WEIGHTS):
        positions = [(a - b) % ORDER for a in WEIGHTS]
        minimum = min(positions)
        for source, deg in zip(WEIGHTS, positions):
            assert deg > 0
            for target in WEIGHTS:
                shift = (target - source) % ORDER or ORDER
                assert deg + shift > minimum
                if deg + shift < P:
                    assert deg + shift == (target - b) % ORDER
    for j in range(5):
        b = j - 2
        ds = [(a - b) % ORDER for a in WEIGHTS]
        assert ds == [278 - j, 338 - j, 409 - j, 449 - j] and min(ds) > 4
    # The coefficient field of eta*z^-2 picks 144 odd weights.
    selected = {(-2 * i) % ORDER for i in range(1, ORDER // 2, 2)}
    assert len(selected) == 144 and selected.isdisjoint(WEIGHTS)
    print(
        "Minimum chain lengths",
        lengths,
        "sum",
        sum(lengths),
        "order valuation at least",
        4 + ORDER,
    )


def direct_residue(a, r, expected):
    """Multiply the actual conjugates, then take just one residue symbol."""
    tame = char2(a)
    D = 7 * len(tame)
    g = primitive(r)
    assert (r - 1) % (D * P) == 0
    Y = roots(pow(g, ((r - 1) // D) * pow(P, -1, D), r), D, r)
    Z = roots(pow(g, ((r - 1) // P) * pow(D, -1, P), r), P, r)
    units = np.array([v for v in range(D) if gcd(v, D) == 1])
    wild = np.arange(1, P)
    base = (1 - Y[units, None] * Z[None, 1:]) % r
    eta = np.array([0, 1, 1, -1, 1, -1, -1], dtype=np.int64)
    phi = eta[units % 7] * np.array(tame, dtype=np.int64)[units % len(tame)]
    twist = np.array([pow(int(t), 296 * a - 1, P) for t in wild])
    exponent = phi[:, None] * twist[None, :] % P
    values = np.ones_like(base)
    while np.any(exponent):
        values = np.where(exponent % 2, values * base % r, values)
        exponent //= 2
        base = base * base % r
    values = values.ravel()
    while len(values) > 1:
        if len(values) % 2:
            values = np.append(values, 1)
        values = values[::2] * values[1::2] % r
    symbol = pow(int(values[0]), (r - 1) // P, r)
    assert symbol == pow(g, expected * ((r - 1) // P), r)


def check_generators():
    controls = {12407809: (404, 80, 387, 203), 19645697: (100, 567, 82, 205)}
    bernoulli = abelian_moments(False)
    for a in (*WEIGHTS, 1, 2):
        n = (1 - 296 * a) % ORDER
        assert local_digit(a) * factorial(n) % P == bernoulli[a] % P
    assert all(local_digit(a) == 0 for a in WEIGHTS)
    for r, target in controls.items():
        values = tuple(upper(a, r) for a in WEIGHTS)
        assert values == target
        for a, value in zip(WEIGHTS, values):
            direct_residue(a, r, value)
        comm = tuple(-2 * v % P for v in values)
        expected = (346, 417, 380, 171) if r == 12407809 else (377, 20, 413, 167)
        assert comm == expected
        # For the shortest class chain we tie the extra character's scale to
        # the unramified character below. Translation by one reads 1/278!.
        separate = comm[0] * pow(factorial(278), -1, P) % P
        assert separate == (534 if r == 12407809 else 275)
        print(
            "prime",
            r,
            "unramified characters",
            values,
            "commutator",
            comm,
            "degree-278 reading",
            separate,
        )


def check_split_prime():
    r = 3360449
    a = WEIGHTS[0]
    assert prime(r) and r == 13 * (7 * 64 * P) + 1
    z = char2()[r % 256] * pow(r, 296, P) % P
    assert z == 24 and z * z % P == P - 1
    assert pow(z, a, P) == 1 and r % 7 == 1 and gcd(r, 2 * 7 * P) == 1
    level_one = upper(a, r)
    assert level_one == 389 and 4 * level_one % P == 402
    direct_residue(a, r, level_one)
    fake = 4 * level_one * pow(factorial(278), -1, P) % P
    assert fake == 457
    shifted = [fake * comb(278, j) % P for j in range(5)]
    assert shifted == [457, 106, 256, 472, 138]
    print("Quartic coefficients after translating the excess character by one", shifted)
    print(
        "prime splitting in the affine extension over MK",
        r,
        "base residue",
        level_one,
        "upper residue",
        4 * level_one % P,
    )
    print(
        "At its projected translated Frobenius the genuine quartic gives 0 and the extra character gives",
        fake,
    )


if __name__ == "__main__":
    check_layers()
    check_generators()
    check_split_prime()
