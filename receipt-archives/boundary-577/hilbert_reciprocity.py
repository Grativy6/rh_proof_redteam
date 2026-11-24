"""Check the two complementary local Hilbert pairings against global reciprocity.

The finite residue field is F_577[x]/(x^12 - 5). This recomputes the Jacobi
logarithms at 577 and uses separate finite-field Frobenius symbols at each of
two split rational primes. All coefficient arrays use signed 64-bit arithmetic.
"""

from math import gcd
from pathlib import Path
import sys

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "fixed-character-577"))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "marked-directions-577"))
from bounds import char2
from fourier_witness import primitive
from group_ring_witness import jj
from residual_directions import local_digit, table, upper

P = 577
DEGREE = 12
Q = P**DEGREE
BIG_D = 7 * 256
ONE = np.eye(1, DEGREE, dtype=np.int64)[0]
X = np.roll(ONE, 1)


def reduce_products(tensor):
    out = np.zeros(tensor.shape[:-2] + (DEGREE,), dtype=np.int64)
    for j in range(DEGREE):
        for k in range(DEGREE):
            out[..., (j + k) % DEGREE] += tensor[..., j, k] * (
                5 if j + k >= DEGREE else 1
            )
    return out % P


def mul(a, b):
    return reduce_products(a[..., :, None] * b[..., None, :])


def power(a, exponent):
    result = np.broadcast_to(ONE, a.shape).copy()
    while exponent:
        if exponent % 2:
            result = mul(result, a)
        a = mul(a, a)
        exponent //= 2
    return result


def roots_of_unity():
    # Since 5 is primitive in F_p and p = 1 mod 12, x^12-5 is irreducible.
    assert primitive(P) == 5
    y = power(X, 27 * 33)
    assert np.array_equal(power(y, 4), 20 * ONE)
    for c in range(1, P):
        z = power(X + c * ONE, (Q - 1) // 7)
        if not np.array_equal(z, ONE):
            break
    else:
        raise AssertionError("No seventh root found")
    root = mul(power(y, pow(7, -1, 256)), z)
    values = np.empty((BIG_D, DEGREE), dtype=np.int64)
    values[0] = ONE
    for j in range(1, BIG_D):
        values[j] = mul(values[j - 1], root)
    assert np.array_equal(mul(values[-1], root), ONE)
    assert all(not np.array_equal(values[BIG_D // r], ONE) for r in (2, 7))
    # Frobenius is diagonal since 12 divides p-1.
    frob = np.array([pow(5, (P - 1) * j // DEGREE, P) for j in range(DEGREE)])
    assert np.array_equal(power(root, P), root * frob % P)
    return values, frob


def exponent_moments(histogram, D, highest):
    f = D * P
    h = histogram.reshape(-1, f).sum(axis=0, dtype=np.int64)
    v = np.arange(D)[:, None]
    j = np.arange(P)[None, :]
    h = h[v + D * ((j - v) * pow(D, -1, P) % P)]
    exp = np.ones((P, highest + 1), dtype=np.int64)
    for n in range(1, highest + 1):
        exp[:, n] = exp[:, n - 1] * j[0] * pow(n, -1, P) % P
    return h @ exp % P


def logarithm_digit(histogram, a, roots, frob):
    phi = table(a, True)
    D = len(phi)
    exponent = 296 * a % (P - 1)
    roots = roots[:: BIG_D // D]
    units = [v for v in range(1, D) if gcd(v, D) == 1]
    gauss = phi[units] @ roots[units] % P
    assert np.any(gauss)
    assert np.array_equal(gauss * frob % P, gauss * pow(int(phi[P % D]), -1, P) % P)
    orbits = []
    seen = set()
    for v in units:
        if v in seen:
            continue
        orbit = []
        t = v
        while t not in seen:
            seen.add(t)
            orbit.append(t)
            t = t * P % D
        assert t == v
        orbits.append(orbit)

    moments = exponent_moments(histogram, D, exponent)
    residues = np.arange(D)
    rows = np.array([(roots[v[0] * residues % D].T @ moments % P).T for v in orbits])
    inv = power(rows[:, 0], Q - 2)
    assert np.all(mul(rows[:, 0], inv) == ONE)
    log_der = np.zeros_like(rows)
    # For J(X), form X J'(X)/J(X). Every n through 296 is a unit.
    for n in range(1, exponent + 1):
        conv = np.einsum(
            "vji,vjk->vik", rows[:, 1:n], log_der[:, n - 1 : 0 : -1], optimize=False
        )
        log_der[:, n] = mul((n * rows[:, n] - reduce_products(conv)) % P, inv)
    digit = np.zeros(DEGREE, dtype=np.int64)
    for t, orbit in zip(log_der[:, exponent], orbits):
        b = t * pow(exponent, -1, P) % P
        for v in orbit:
            digit = (digit + pow(int(phi[v]), -1, P) * b) % P
            b = b * frob % P
    result = mul(gauss, digit)
    assert not np.any(result[1:])
    return int(result[0])


def main():
    roots, frob = roots_of_unity()
    expected = {
        (12407809, 1): (102, 568),
        (12407809, 2): (449, 89),
        (19645697, 1): (180, 52),
        (19645697, 2): (379, 327),
    }
    for r in (12407809, 19645697):
        h = jj.log_histogram(BIG_D * P, r, primitive(r))
        for a in (1, 2):
            i = 296 * a % (P - 1)
            leading = logarithm_digit(h, a, roots, frob)
            D = 7 * len(char2(a))
            residues = np.arange(D * P // 2 + 1, D * P, 2)
            residues = residues[(residues % 7 != 0) & (residues % P != 0)]
            inverse = np.array([pow(int(v), -1, P) if v else 0 for v in table(a, True)])
            powers = np.array([pow(v, -296 * a, P) if v else 0 for v in range(P)])
            carry = int(inverse[residues % D] @ powers[residues % P]) % P
            symbol = i * DEGREE * local_digit(a) * leading % P
            frobenius = upper(a, r)
            # At the chosen finite place (Y_D * Z)^D = Z^D represents the
            # generator in the Frobenius table. Convert its exponent to Z.
            assert symbol == DEGREE * D * carry * frobenius % P
            assert (leading, symbol) == expected[r, a]
            print(
                r,
                "upper exponent",
                a,
                "Jacobi coefficient times Gauss sum",
                leading,
                "Hilbert exponent",
                symbol,
                "Frobenius",
                frobenius,
                "carry",
                carry,
            )


if __name__ == "__main__":
    main()
