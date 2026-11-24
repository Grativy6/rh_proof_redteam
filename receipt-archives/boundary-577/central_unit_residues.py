"""Central power residues of the original two point-field units at tame primes.

The split comparison rows can be regenerated with tame_circular_norms.cpp.
Supplying --binary runs that program at all nine primes in place of the rows.
"""

import argparse
from math import comb
import subprocess

import numpy as np

from artin_units import P
from bounds import prime
from fourier_witness import C, F, character, dft, histogram, primitive


# The first two rows determine a virtual unit. The third checks that solve.
# Entries: split prime, least primitive generator, exponents of e_-, R, R_q.
DATA = {
    2309: [
        (590386990849, 7, 172, 124, 457),
        (4132708935937, 5, 483, 135, 47),
        (5116687254017, 3, 567, 108, 576),
    ],
    3463: [
        (2656357924609, 19, 449, 120, 408),
        (4722414088193, 3, 218, 494, 93),
        (16233298428161, 7, 256, 540, 535),
    ],
    20773: [
        (54884853152513, 3, 457, 141, 144),
        (84982998429697, 5, 438, 36, 62),
        (90294435831553, 10, 329, 367, 115),
    ],
}


def mirror_weights():
    a = np.arange(F, dtype=np.int64)
    tame = np.array([pow(character(i), -1, P) if i % 2 else 0 for i in range(C)])
    inertia = np.array([pow(i, -297, P) if i else 0 for i in range(P)])
    return tame[a % C] * inertia[a % P] % P


def logs_at(q, g):
    data = np.zeros(q, dtype=np.int64)
    x = 1
    for j in range(q - 1):
        data[x] = j % P
        x = x * g % q
    assert x == 1
    return data


def carry(q, logs, weights):
    # First sum over the f-part with the q coordinate fixed.
    prefix = np.r_[0, np.cumsum(np.tile(weights, 2))]
    j = np.arange(1, q, dtype=np.int64)
    shift = j * pow(q, -1, F) % F
    upper = prefix[F + shift] - prefix[F // 2 + shift]
    result = int(weights[q % F]) * int(upper @ logs[j]) % P

    # Reverse the CRT grouping and compare three independent Jacobi carries.
    a = np.arange(F, dtype=np.int64)
    rotated = a * pow(F, -1, q) % q
    sums = np.r_[0, np.cumsum(np.tile(logs[F * np.arange(q) % q], 2))]
    for h in (2, 3, 5, 7):
        expected = (
            result
            if h == 2
            else result * (h - pow(int(weights[h]), -1, P)) * pow(2, -1, P) % P
        )
        total = 0
        for k in range(1, h):
            first = (k * F * q - h * a + h * F - 1) // (h * F)
            delta = sums[rotated + q] - sums[rotated + first]
            total += int(weights @ delta)
        assert total % P == expected
    return result


def fit(rows):
    (_, _, x, y, z), (_, _, u, v, w), (_, _, h, j, target) = rows
    det = (x * v - y * u) % P
    a = (z * v - y * w) * pow(det, -1, P) % P
    b = (x * w - z * u) * pow(det, -1, P) % P
    assert (h * a + j * b) % P == target
    return a, b, det


def readings(q, weights, rows):
    g = primitive(q)
    logs = logs_at(q, g)
    d = (1 - int(weights[q % F])) % P
    k = carry(q, logs, weights)
    strict = -231 * k * pow(376 * d, -1, P) % P
    a, b, det = fit(rows)
    normalized = pow((a - 95 * b) % P, -1, P)
    unit = -b * strict * normalized % P
    rho = a * strict * normalized % P
    assert (a * unit + b * rho) % P == 0 and (rho + 95 * unit) % P == strict
    print(
        q,
        "Euler factor, carry:",
        d,
        k,
        "basis coefficients:",
        a,
        b,
        "fit determinant:",
        det,
    )
    print(
        "  point symbols for e_-, R, R0:",
        unit,
        rho,
        strict,
        "unit powers:",
        pow(g, (q - 1) // P * rho, q),
        pow(g, (q - 1) // P * strict, q),
    )
    return rho, strict, int(logs[P])


class ResidueField:
    """Polynomial basis with monic modulus X^degree + sum(low_i X^i)."""

    def __init__(self, q, degree, low):
        self.q, self.degree = q, degree
        self.one = np.eye(1, degree, dtype=np.int64)[0]
        self.x = np.roll(self.one, 1)
        self.reductions = np.zeros((2 * degree - 1, degree), dtype=np.int64)
        self.reductions[:degree] = np.eye(degree, dtype=np.int64)
        for n in range(degree, 2 * degree - 1):
            self.reductions[n] = (
                -sum(c * self.reductions[n - degree + i] for i, c in low.items()) % q
            )

    def mul(self, a, b):
        return (np.convolve(a, b) % self.q) @ self.reductions % self.q

    def power(self, a, n):
        if n < 0:
            assert np.any(a)
            n %= self.q**self.degree - 1
        result = self.one.copy()
        while n:
            if n & 1:
                result = self.mul(result, a)
            a = self.mul(a, a)
            n //= 2
        return result


def point_root(q, degree, modulus, hist):
    # X is a primitive 256th root. Its Frobenius orbit has the field degree.
    field = ResidueField(q, degree, modulus)
    assert all(pow(q, n, C) != 1 for n in range(1, degree)) and pow(q, degree, C) == 1
    assert np.array_equal(field.power(field.x, 128), -field.one % q)
    powers = [field.one]
    for _ in range(1, C):
        powers.append(field.mul(powers[-1], field.x))
    powers = np.array(powers)
    xi = pow(primitive(q), (q - 1) // P, q)
    transformed = hist @ dft(P, pow(xi, pow(C, -1, P), q), q) % q
    group = sorted({pow(i, 297, P) for i in range(1, P)})
    wild = np.array([pow(i, 297, P) for i in range(1, P)])
    e = character(q % C)
    projected = {}
    for h in group:
        if h in projected:
            continue
        prod = field.one.copy()
        for v in range(1, C, 2):
            js = np.flatnonzero(wild * character(v) % P == h) + 1
            powers_v = powers[np.arange(C) * v * pow(P, -1, C) % C]
            values = transformed[:, js].T @ powers_v % q
            for value in values:
                prod = field.mul(prod, value)
        pos, element = h, prod
        while pos not in projected:
            projected[pos] = element
            pos = pos * e % P
            element = field.power(element, q)
        assert pos == h and np.array_equal(element, prod) and np.any(prod)
    weights = {h: pow(h, -1, P) for h in group}
    beta = field.one.copy()
    for h in group:
        beta = field.mul(beta, field.power(projected[h], weights[h]))

    def factor(s):
        result = field.one.copy()
        for h in group:
            n = s * weights[h]
            result = field.mul(result, field.power(projected[h], -(n // P)))
        return result

    B = pow(q - e, -1, P)
    A = (1 - (q - e) * B) // P
    f_e = factor(e)
    s0 = field.mul(field.power(beta, A), field.power(f_e, B))
    assert np.array_equal(field.power(s0, P), beta)
    assert np.array_equal(field.power(s0, q), field.mul(f_e, field.power(s0, e)))
    roots = {}
    for h in group:
        if h in roots:
            continue
        v = field.mul(factor(h), field.power(s0, h))
        j = h
        while j not in roots:
            roots[j] = v
            v = field.power(v, q)
            j = j * e % P
        assert np.array_equal(v, roots[h])
    exp = np.array([pow(xi, i, q) for i in range(P)])
    coords = (
        exp[-511 * np.outer(np.arange(P), group) % P]
        @ np.array([roots[h] for h in group])
        % q
    )
    assert len({tuple(row) for row in coords}) == P
    rational = np.flatnonzero(~np.any(coords[:, 1:], axis=1))
    assert rational.tolist() == [0]
    print(q, "unique rational reduction of theta:", int(coords[0, 0]))
    return int(coords[0, 0])


def solve(matrix, rhs):
    n = len(matrix)
    work = np.column_stack((matrix, rhs)).copy() % P
    det = 1
    for i in range(n):
        pivot = int(work[i, i])
        det = det * pivot % P
        work[i] = work[i] * pow(pivot, -1, P) % P
        for j in range(n):
            if i != j:
                work[j] = (work[j] - work[j, i] * work[i]) % P
    result = work[:, -1]
    assert np.array_equal(matrix @ result % P, rhs % P)
    return result, det


def check_descent(matrix):
    # Old dual rows are u = e_-^523 R^376, v = e_-^251 R^251.
    dual_basis = np.array([[523, 376], [251, 251]], dtype=np.int64)
    tame_change = np.array([[98, 287], [482, 536]], dtype=np.int64)
    assert np.array_equal(
        matrix[:2, :2] @ tame_change % P, -pow(144, -1, P) * np.diag([488, 190]) % P
    )
    for shift in range(P):
        j = 296 + (P - 1) * shift
        old = 231 * np.array([261 + 37 * (j + 1), 202 * (j + 1)]) % P
        (root_unit, rho), _ = solve(dual_basis, old)
        strict = (rho + 95 * root_unit) % P
        assert (rho, strict) == (2, (273 + 190 * (j - 296)) % P)
        tame, _ = solve(matrix[:2, :2], np.array([-rho, -strict]) % P)
        measured = np.array([389, -288 * (413 - j)]) % P
        assert np.array_equal(tame_change @ measured % P, 2 * tame % P)
        # Exactly one residue of the twist admits divisibility by p in
        # the chosen p-split cyclic field, because the first entry fixes a.
        up = (np.array([rho, strict]) + matrix[:2] @ np.array([290, 150, 554])) % P
        assert (not np.any(up)) == (shift == 0)
    q_values = list(DATA)
    c = np.array([290, 150, 554])
    old_carry = (261 + 37 * 297) % P
    carries, euler = [503, 461, 359], [423, 216, 481]
    assert (
        old_carry
        - sum(int(k) * v * pow(d, -1, P) for k, v, d in zip(c, carries, euler))
    ) % P == 0
    assert np.array_equal(matrix @ c % P, np.array([P - 2, P - 273, 0]))
    assert np.prod(q_values) == 166102299791
    # Test Frobenius invariants in the full quartic Lie module.
    for q, expected in zip(q_values, [[], [], [2]]):
        z = character(q % C)
        eta = 1 if q % 7 in (1, 2, 4) else -1
        assert [j for j in range(5) if eta * pow(z, j - 2, P) % P == 1] == expected
        assert pow(z, 4, P) != 1
    for q in q_values[:2]:
        assert all(comb(q - 1, j) % P == 0 for j in range(1, P))
        assert comb(q - 1, P) % P == (q - 1) // P
    assert P * 2 == 1154 and P**2 == 332929
    assert 64 * 32 * 294 % P == 301
    print(
        "All 577 twist residues checked; 296 is the sole gain in the fixed auxiliary field."
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", help="compiled tame_circular_norms program")
    opt = parser.parse_args()
    weights = mirror_weights()
    rows = []
    for q, examples in DATA.items():
        assert prime(q) and q % P == 1
        if opt.binary:
            for row in examples:
                got = subprocess.check_output(
                    [opt.binary, str(q), str(row[0])], text=True
                )
                assert list(map(int, got.split())) == [q, *row]
        rows.append(readings(q, weights, examples))
    assert rows == [(426, 35, 575), (97, 522, 32), (234, 245, 334)]
    m = np.array(rows, dtype=np.int64).T
    hpair = np.array([-2, -273, 0], dtype=np.int64)
    two, det = solve(m[:2, :2], hpair[:2])
    three, det3 = solve(m, hpair)
    assert (two.tolist(), det) == ([481, 374], 294)
    assert (three.tolist(), det3) == ([290, 150, 554], 73)
    print("Tame digit corrections:", two.tolist(), "p-split version:", three.tolist())
    print("Determinants:", det, det3)
    check_descent(m)
    assert -231 * 540 * pow(376, -1, P) % P == 190
    assert 413 * pow(8, -1, P) % P == 268
    hist = histogram()
    assert point_root(2309, 64, {0: 688}, hist) == 73
    assert point_root(3463, 32, {0: -1, 16: 1516}, hist) == 3453
    assert point_root(20773, 64, {0: -1162}, hist) == 9093


if __name__ == "__main__":
    main()
