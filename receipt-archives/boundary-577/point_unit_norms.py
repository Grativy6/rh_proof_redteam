"""Power-residue fingerprints of the two required units in the degree-577 field."""

from math import isqrt

import numpy as np

from affine_frobenius import mul as matrix_product
from artin_units import P
from bounds import char2
from fourier_witness import character, factors, histogram


class QuadraticField:
    def __init__(self, prime):
        self.r = prime
        assert all(prime % i for i in range(2, isqrt(prime) + 1))
        assert 2 * (prime - 1) ** 2 < 2**63
        self.d = next(
            a for a in range(2, prime) if pow(a, (prime - 1) // 2, prime) == prime - 1
        )
        self.order = prime**2 - 1
        divisors = set(factors(prime - 1)) | set(factors(prime + 1))
        self.g = next(
            (j, 1)
            for j in range(1, prime)
            if all(
                self.scalar_power((j, 1), self.order // prime_factor) != (1, 0)
                for prime_factor in divisors
            )
        )

    def mul(self, u, v):
        a, b = u
        c, d = v
        r = self.r
        return ((a * c % r + self.d * (b * d % r)) % r, (a * d + b * c) % r)

    def scalar_power(self, value, n):
        result = (1, 0)
        while n:
            if n % 2:
                result = self.mul(result, value)
            value = self.mul(value, value)
            n //= 2
        return result

    def root_table(self, order, exponent=1):
        step = self.scalar_power(self.g, (self.order // order) * exponent)
        z = (1, 0)
        rows = []
        for _ in range(order):
            rows.append(z)
            z = self.mul(z, step)
        assert z == (1, 0)
        a = np.array(rows, dtype=np.int64)
        return a[:, 0], a[:, 1]

    def product(self, value):
        a, b = value
        while a.shape[-1] > 1:
            if a.shape[-1] % 2:
                shape = (*a.shape[:-1], 1)
                a = np.concatenate((a, np.ones(shape, dtype=np.int64)), axis=-1)
                b = np.concatenate((b, np.zeros(shape, dtype=np.int64)), axis=-1)
            a, b = self.mul((a[..., ::2], b[..., ::2]), (a[..., 1::2], b[..., 1::2]))
        return a[..., 0], b[..., 0]

    def weighted_product(self, values, exponents):
        a, b = values
        u, v = np.ones_like(a), np.zeros_like(b)
        for bit in range(max(int(n) for n in exponents).bit_length()):
            choose = ((exponents >> bit) & 1) != 0
            u[choose], v[choose] = self.mul(
                (u[choose], v[choose]), (a[choose], b[choose])
            )
            a, b = self.mul((a, b), (a, b))
        return tuple(map(int, self.product((u, v))))


def point_roots(field, hist):
    """Reduce the absolute point generator on each marked affine place."""
    r = field.r
    size = 256
    tame = field.root_table(size, pow(P, -1, size))
    wild = field.root_table(P, pow(size, -1, P))
    tgrid = np.outer(np.arange(size), np.arange(size)) % size
    wgrid = np.outer(np.arange(P), np.arange(P)) % P
    left = tuple(matrix_product(u[tgrid], hist, r) for u in tame)
    fa, fb = (u[wgrid] for u in wild)
    real = (
        matrix_product(left[0], fa, r) + field.d * matrix_product(left[1], fb, r)
    ) % r
    imag = (matrix_product(left[0], fb, r) + matrix_product(left[1], fa, r)) % r
    labels = (
        np.array([character(i) for i in range(1, size, 2)])[:, None]
        * np.array([pow(i, 297, P) for i in range(1, P)])[None, :]
    ) % P
    factors_by_label = {}
    for j in np.unique(labels):
        keep = labels == j
        a, b = field.product((real[1::2, 1:][keep], imag[1::2, 1:][keep]))
        assert b == 0
        factors_by_label[int(j)] = int(a)
    roots_origin = {}
    for e in factors_by_label:
        rad = 1
        for j, factor in factors_by_label.items():
            rad = rad * pow(factor, e * pow(j, -1, P) % P, r) % r
        roots_origin[e] = pow(rad, pow(P, -1, r - 1), r)

    mu = field.root_table(P)
    t = np.arange(P)
    coords = [np.zeros(P, dtype=np.int64), np.zeros(P, dtype=np.int64)]
    for e, s in roots_origin.items():
        for i, x in enumerate(mu):
            coords[i] = (coords[i] + s * x[-511 * e * t % P]) % r
    rows = list(zip(map(int, coords[0]), map(int, coords[1])))
    assert len(set(rows)) == P and rows[0][1] == 0
    assert all(rows[-i] == (a, -b % r) for i, (a, b) in enumerate(rows))
    return rows


def point_prime(r, hist):
    D, m = 256, P**2
    assert r % m == m - 1 and r % D in (127, 129)
    field = QuadraticField(r)
    rorder = field.order
    ga, gb = field.root_table(P)
    logs = {(int(a), int(b)): j for j, (a, b) in enumerate(zip(ga, gb))}
    # CRT factors for a primitive (256*p^2)-th root and its p-th power.
    tame = field.root_table(D, pow(m, -1, D))
    wild = field.root_table(m, pow(D, -1, m))
    v = np.arange(1, D, 2)
    ta, tb = tame[0][v, None], tame[1][v, None]
    t = np.array([pow(j, P, m) for j in range(1, P)], dtype=np.int64)
    weights = (
        np.array(char2())[v, None]
        * np.array([pow(j, 296, P) for j in range(1, P)])[None, :]
        % P
    )
    order = np.argsort(weights.ravel())
    indices = np.arange(1, P, dtype=np.int64)
    assert np.all(weights.ravel()[order].reshape(P - 1, 128) == indices[:, None])

    def grouped(ta, tb, ix):
        ua, ub = field.mul((ta, tb), (wild[0][ix], wild[1][ix]))
        a = ((1 - ua) % r).ravel()[order].reshape(P - 1, 128)
        b = ((-ub) % r).ravel()[order].reshape(P - 1, 128)
        return field.product((a, b))

    # The tame coordinate at conductor 256*p is the p-th power of the
    # tame coordinate just used. The Teichmuller exponents are needed mod p^2.
    base_ta = tame[0][P * v % D, None]
    base_tb = tame[1][P * v % D, None]
    tame_weights = np.array([pow(int(j), P, m) for j in indices], dtype=np.int64)
    base_group = grouped(base_ta, base_tb, P * t % m)
    base = field.weighted_product(base_group, tame_weights)
    unit = logs[field.scalar_power(base, rorder // m)]
    samples = []
    norm_group = (np.ones_like(indices), np.zeros_like(indices))
    derivative = (1, 0)
    for j in range(P):
        group = grouped(ta, tb, t * (1 + P * j) % m)
        norm_group = field.mul(norm_group, group)
        value = field.weighted_product(group, indices)
        samples.append(logs[field.scalar_power(value, rorder // P)])
        derivative = field.mul(derivative, field.scalar_power(value, P - 1 - j))
    assert all(np.array_equal(x, y) for x, y in zip(norm_group, base_group))
    assert sum(samples) % P == 0
    rho = -sum((j + 1) * n for j, n in enumerate(samples)) % P
    conjugate = (derivative[0], -derivative[1] % r)
    torus = field.mul(conjugate, field.scalar_power(derivative, rorder - 1))
    assert logs[field.scalar_power(torus, (r + 1) // P)] == rho
    strict = (rho + 95 * unit) % P
    rows = point_roots(field, hist)
    print(r, "point roots at t=0,1:", rows[:2], flush=True)
    assert (
        len({t * rho % P for t in range(P)}) == P
        and len({t * strict % P for t in range(P)}) == P
    )
    print(
        r,
        "nonresidue, generator:",
        field.d,
        field.g,
        "root unit, R, R0:",
        unit,
        rho,
        strict,
        flush=True,
    )
    return (rho, strict), shift_matrix(field, rows)


def shift_matrix(field, rows):
    # Frobenius exchanges t and -t. The first 288 rows determine both
    # members of every quadratic pair. A rational nonzero factor reads zero.
    r = field.r
    t = np.arange(1, (P + 1) // 2)
    a = np.array([rows[i][0] for i in t])[:, None] - np.arange(P - 1)
    b = np.broadcast_to(np.array([rows[i][1] for i in t])[:, None], a.shape)
    ua, ub = field.scalar_power((a % r, b), field.order // P)
    ga, gb = field.root_table(P)
    keys = ga * r + gb
    order = np.argsort(keys)
    result = order[np.searchsorted(keys[order], ua * r + ub)]
    assert np.array_equal(keys[result], ua * r + ub)
    return result


def solve_square(square, rhs):
    work = np.column_stack((square, rhs)).copy() % P
    n = len(square)
    det = 1
    for i in range(n):
        hits = np.flatnonzero(work[i:, i])
        if not len(hits):
            raise ValueError(f"Singular shift matrix at column {i}")
        j = i + int(hits[0])
        if j != i:
            work[[i, j]] = work[[j, i]]
            det = -det
        pivot = int(work[i, i])
        det = det * pivot % P
        work[i, i:] = work[i, i:] * pow(pivot, -1, P) % P
        work[i + 1 :, i:] = (
            work[i + 1 :, i:] - work[i + 1 :, i, None] * work[i, i:]
        ) % P
    for i in reversed(range(n)):
        work[:i, n:] = (work[:i, n:] - work[:i, i, None] * work[i, n:]) % P
    ans = work[:, n:]
    assert np.array_equal(square @ ans % P, rhs % P)
    return ans, det


def check_small_shifts(places):
    t = np.arange(1, (P + 1) // 2)[:, None]
    first = np.vstack([m for _, m in places[:2]])
    rhs = np.vstack([t * np.array(row) % P for row, _ in places[:2]])
    coefficients, det = solve_square(first, rhs)
    predicted, control = places[2]
    defect = (control @ coefficients - t * np.array(predicted)) % P
    minor = int(defect[0, 0] * defect[1, 1] - defect[0, 1] * defect[1, 0]) % P
    assert (
        det == 234 and defect[:2].tolist() == [[323, 147], [379, 548]] and minor == 121
    )
    print(
        "Shift matrix determinant:",
        det,
        "held-out errors at t=1,2:",
        defect[:2].tolist(),
        "minor:",
        minor,
    )


def operator_identities():
    # Work modulo p^2, so the check includes the digit lost by reducing first.
    modulus = P**2
    a = np.empty(P, dtype=np.int64)
    b = np.empty_like(a)
    a[0] = b[0] = 0
    for j in range(1, P):
        a[j] = pow(j, P, modulus)
        b[-j] = pow(int(a[j]), -1, modulus)
    prod = np.convolve(a, b) % modulus
    prod[: P - 1] = (prod[: P - 1] + prod[P:]) % modulus
    assert prod[0] == P - 1 and np.all(prod[1:P] == modulus - 1)
    assert np.all((np.roll(a, 1) - a) % P == P - 1)
    assert sum(j * pow(j, -1, P) for j in range(1, P)) % P == P - 1
    assert 366 * pow(8, -1, P) % P == 190
    print("Two Gauss operators multiply to p minus the translation norm.")


if __name__ == "__main__":
    operator_identities()
    hist = histogram()
    places = [point_prime(r, hist) for r in (1406957953, 1492187777, 2088130687)]
    slopes = [row for row, _ in places]
    det = (slopes[0][0] * slopes[1][1] - slopes[0][1] * slopes[1][0]) % P
    assert slopes == [(528, 199), (301, 576), (11, 209)] and det == 158
    check_small_shifts(places)
    print("Determinant of the two slope rows:", det)
