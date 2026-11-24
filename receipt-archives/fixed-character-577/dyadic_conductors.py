"""Carry sums for all even twists of pure two-power characters at 577.

Requires NumPy. Two evaluations of the high-conductor sums use, respectively,
short translated intervals and CRT representatives of the full unit orbit.
The proof that 144 exponents cover every higher conductor is in the receipt.
"""

from math import comb, isqrt

import numpy as np


P = 577
EVEN = range(0, P - 1, 2)
OFFSETS = (1, 3, 5)


def residue_powers(modulus, lift=1):
    # A row indexed by zero contributes nothing to a sum over units.
    return np.array(
        [
            [pow(a, -lift * (j + 1), modulus) if a else 0 for j in EVEN]
            for a in range(P)
        ],
        dtype=np.int64,
    )


def transform64():
    base = pow(5, 9, P)
    assert pow(base, 32, P) == P - 1
    return np.array(
        [[pow(base, b * k, P) for k in range(64)] for b in range(1, 64, 2)],
        dtype=np.int64,
    )


def cyclic_intervals(powers):
    starts = np.arange(P)
    sums = np.zeros_like(powers)
    for b in range(289, P):
        sums += powers[(starts + b) % P]
    return sums % P


def periodic_row(s, a, transform, powers, intervals):
    # t = a + 2^(s-6) u is the positive dyadic representative.
    u = (31 * a * np.arange(64)) % 64
    c_inv = pow(2, -s, P)
    t = (a * c_inv + u * pow(64, -1, P)) % P
    other = (1 - t) % P
    endpoints = np.where(
        (u >= 32)[:, None], powers[(288 + t) % P], powers[(288 + other) % P]
    )
    moments = (intervals[t] + intervals[other] + endpoints) % P
    scale = np.array([pow(c_inv, j + 1, P) for j in EVEN])
    return (transform @ moments % P) * scale % P


def crt_row(s, a, transform, powers):
    # Directly form the positive 2-adic class for each k. At even j, pairing
    # n with C*p-n makes the contribution of the negative dyadic class equal.
    c = 2**s
    generator = pow(5, c // 256, c)
    c_inv = pow(c, -1, P)
    units = np.arange(1, P)
    mask = []
    for k in range(64):
        t = a * pow(generator, k, c) % c
        lifts = ((units - t % P) * c_inv) % P
        high = (lifts > 288) | ((lifts == 288) & (2 * t > c))
        mask.append(2 * high)
    return ((transform @ np.array(mask)) % P) @ powers[1:] % P


def check_high_conductors():
    powers = residue_powers(P)
    transform = transform64()
    intervals = cyclic_intervals(powers)
    assert pow(2, 144, P) == 1 and all(pow(2, 144 // r, P) != 1 for r in (2, 3))
    assert (pow(5, 32, 8192) - 1) // 128 == 31
    totals = [0] * len(OFFSETS)
    last_cases = []
    for s in range(13, 13 + 144):
        live = np.ones((32, len(EVEN)), dtype=bool)
        for i, a in enumerate(OFFSETS):
            reading = periodic_row(s, a, transform, powers, intervals)
            direct = crt_row(s, a, transform, powers)
            assert np.array_equal(reading, direct)
            if a == 5:
                for b, j in np.argwhere(live):
                    last_cases.append(
                        (s % 144, 2 * int(b) + 1, 2 * int(j), int(reading[b, j]))
                    )
            live &= reading == 0
            totals[i] += int(live.sum())
    assert totals == [2274, 5, 0]
    assert sorted(last_cases) == [
        (5, 27, 374, 565),
        (22, 43, 408, 67),
        (83, 35, 468, 412),
        (123, 5, 226, 214),
        (133, 1, 340, 572),
    ]
    for s, first_count in [(9, 15), (10, 9), (11, 15), (12, 19)]:
        live = crt_row(s, 1, transform, powers) == 0
        assert live.sum() == first_count
        assert not np.any(live & (crt_row(s, 3, transform, powers) == 0))
    print(
        "High conductors: 1,327,104 period, root and twist cases; successive zero counts",
        totals,
    )
    print(
        "The five final checks (s mod 144, inverse label, twist, value):",
        sorted(last_cases),
    )


def low_candidates():
    # Compute the actual upper-half divisor sum modulo p^2. The p-adic
    # Teichmuller lift of a residue a is represented by a^p modulo p^2.
    modulus = P * P
    powers = residue_powers(modulus, lift=P)
    matches = {}
    for s in range(3, 9):
        c = 2**s
        order = c // 4
        conductor = c * P
        upper = np.arange(conductor // 2 + 1, conductor, 2, dtype=np.int64)
        upper = upper[upper % P != 0]
        logs = np.zeros(c, dtype=np.int64)
        for i in range(order):
            u = pow(5, i, c)
            logs[u] = logs[c - u] = i
        root = pow(5, P * ((P - 1) // order), modulus)
        inverse = np.array([pow(root, -i, modulus) for i in range(order)])
        matching = []
        for b in range(1, order, 2):
            grouped = np.zeros(P, dtype=np.int64)
            np.add.at(grouped, upper % P, inverse[(logs[upper % c] * b) % order])
            values = ((grouped % modulus) @ powers) % modulus
            for j, value in zip(EVEN, values):
                if value % P == 0:
                    assert value != 0
                    matching.append((b, j, int(value) // P))
        matches[s] = matching
    assert [len(matches[s]) for s in range(3, 9)] == [0, 2, 0, 11, 5, 9]
    direct = crt_row(8, 1, transform64(), residue_powers(P))
    zero_labels = {
        ((-(2 * int(b) + 1)) % 64, 2 * int(j)) for b, j in np.argwhere(direct == 0)
    }
    assert zero_labels == {(b, j) for b, j, _ in matches[8]}
    return matches


def check_bernoulli_lifts(matches):
    # Independent check of 2 B_1 from the full interval, carrying one
    # extra p-adic digit because its denominator is C*p.
    wide = P**3
    residues = np.arange(1, P)
    for s, cases in matches.items():
        c = 2**s
        order = c // 4
        dyadic = np.arange(1, c, 2)
        ns = dyadic[:, None] + c * (
            (residues[None, :] - dyadic[:, None]) * pow(c, -1, P) % P
        )
        generator = pow(5, (P - 1) // order * P**2, wide)
        character = {}
        for i in range(order):
            u = pow(5, i, c)
            character[u] = character[c - u] = pow(generator, i, wide)
        for b, j, digit in cases:
            p_weights = np.array([pow(int(w), -(j + 1) * P**2, wide) for w in residues])
            partial = (ns @ p_weights) % wide
            total = 2 * sum(
                int(v) * pow(character[int(u)], -b, wide)
                for u, v in zip(dyadic, partial)
            )
            numerator = total % wide
            assert numerator % P == 0
            bernoulli = (numerator // P * pow(c, -1, P**2)) % (P**2)
            assert bernoulli == P * digit


def check_principal():
    bernoulli = [1]
    for k in range(1, P - 1):
        numerator = -sum(comb(k + 1, a) * bernoulli[a] for a in range(k))
        bernoulli.append(numerator * pow(k + 1, -1, P) % P)
    assert [k for k in range(2, P - 2, 2) if bernoulli[k] == 0] == [52]
    q, z = 2309, 16
    assert all(q % d for d in range(2, isqrt(q) + 1))
    assert pow(z, P, q) == 1 and z != 1
    unit = 1
    for c in range(1, (P + 1) // 2):
        difference = (pow(z, c, q) - pow(z, -c, q)) % q
        assert difference != 0
        unit = unit * pow(difference, pow(c, P - 1 - 52, q - 1), q) % q
    assert (unit, pow(unit, (q - 1) // P, q)) == (631, 973)
    print(
        "Principal character: irregular index 52; its Vandiver test is 973 modulo 2309."
    )


if __name__ == "__main__":
    check_high_conductors()
    low = low_candidates()
    check_bernoulli_lifts(low)
    print(
        "Low conductors: 27 possible lines; each upper-half multiplier has valuation one."
    )
    for s, cases in low.items():
        print(f"2^{s}:", cases)
    check_principal()
