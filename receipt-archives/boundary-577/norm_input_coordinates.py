"""Read the actual S-divisors and an integral relative coordinate of the 577 field."""

import argparse
from hashlib import sha256
from math import gcd

import numpy as np

from artin_units import P
from residual_directions import table
from fourier_witness import C, F, character, dft, histogram, primitive, roots


SUPPORT = 12407809


def product_mod(factors, modulus):
    factors = np.asarray(factors, dtype=np.int64).ravel()
    while len(factors) > 1:
        if len(factors) % 2:
            factors = np.append(factors, 1)
        factors = factors[::2] * factors[1::2] % modulus
    return int(factors[0])


def jacobi_radicals(hist, q, g):
    root = pow(g, (q - 1) // F, q)
    a = pow(root, P * pow(P, -1, C), q)
    b = pow(root, C * pow(C, -1, P), q)
    assert max(C, P) * (q - 1) ** 2 < 2**63
    values = ((dft(C, a, q) @ hist % q) @ dft(P, b, q) % q)[1::2, 1:]
    tame = np.array([character(i) for i in range(1, C, 2)])
    wild = np.array([pow(i, 297, P) for i in range(1, P)])
    labels = tame[:, None] * wild % P
    group = [int(v) for v in np.unique(labels)]
    assert len(group) == 64
    products = {v: product_mod(values[labels == v], q) for v in group}
    weights = {v: pow(v, -1, P) for v in group}

    def combine(exponents):
        result = 1
        for v in group:
            result = result * pow(products[v], exponents[v], q) % q
        return result

    beta = combine(weights)
    carries = {}
    for e in group:
        shifted = {v: e * weights[v] % P for v in group}
        carries[e] = combine({v: (shifted[v] - e * weights[v]) // P for v in group})
        assert pow(carries[e], P, q) * pow(beta, e, q) % q == combine(shifted)
    return beta, carries


def upper_radical(a, q, g):
    phi = table(a, True)
    conductor = len(phi) * P
    z = roots(pow(g, (q - 1) // conductor, q), conductor, q)
    i = np.arange(1, conductor, 2, dtype=np.int64)
    i = i[(i % 7 != 0) & (i % P != 0)]
    twist = np.array([pow(t, (296 * a - 1) % (P - 1), P) for t in range(P)])
    exponents = phi[i % len(phi)] * twist[i % P] % P
    base = (1 - z[i]) % q
    values = np.ones_like(base)
    for bit in range(P.bit_length()):
        mask = (exponents >> bit) & 1 == 1
        values[mask] = values[mask] * base[mask] % q
        base = base * base % q
    return product_mod(values, q)


def algebra_product(left, right, beta, q):
    terms = np.convolve(left, right) % q
    result = terms[:P].copy()
    result[:-1] = (result[:-1] + beta * terms[P:]) % q
    return result


def polynomial_at_support():
    q = SUPPORT
    g = primitive(q)
    xi = pow(g, (q - 1) // P, q)
    beta, carries = jacobi_radicals(histogram(), q, g)
    assert pow(beta, (q - 1) // P, q) == pow(xi, 82, q)
    assert beta == 10606075
    print("Lower radicand at the support prime:", beta)
    for a, expected in ((1, 61), (2, 139)):
        radical = upper_radical(a, q, g)
        assert pow(radical, (q - 1) // P, q) == pow(xi, expected, q)
        exponent = expected * pow(82, -1, P) % P
        m = (q - 1) // P
        assert gcd(m, P) == 1
        factor = pow(radical * pow(beta, -exponent, q) % q, pow(P, -1, m), q)
        assert pow(factor, P, q) * pow(beta, exponent, q) % q == radical
        print("Upper radical, exponent of S, root factor:", radical, exponent, factor)

    coeff = np.zeros(P, dtype=np.int64)
    for e, carry in carries.items():
        weight = 131 * pow(pow(xi, e, q) - 1, -1, q) % q
        coeff[0] = (coeff[0] - weight) % q
        coeff[e] = weight * carry % q
    assert coeff[0] == 131 * 32 and np.count_nonzero(coeff) == 65
    unit = np.zeros(P, dtype=np.int64)
    unit[0] = 1
    result, power, n = unit.copy(), coeff.copy(), q
    while n:
        if n % 2:
            result = algebra_product(result, power, beta, q)
        power = algebra_product(power, power, beta, q)
        n //= 2
    assert np.array_equal(result, coeff * roots(pow(xi, 82, q), P, q) % q)
    # S^p-beta is irreducible of prime degree. The nonconstant coordinate
    # therefore generates the same residue field. Recover its monic polynomial.
    indices = np.arange(P)
    matrix = (
        coeff[(indices[:, None] - indices) % P]
        * np.where(indices[:, None] < indices, beta, 1)
        % q
    )
    v = unit.copy()
    traces, monic = [0], [1]
    test = v.copy()
    for k in range(1, P + 1):
        v = matrix @ v % q
        traces.append(P * int(v[0]) % q)
        c = -sum(monic[k - j] * traces[j] for j in range(1, k + 1)) * pow(k, -1, q) % q
        monic.append(c)
        test = ((matrix @ test) + c * unit) % q
    assert not np.any(test)
    digest = sha256(b"".join(int(v).to_bytes(4, "little") for v in monic)).hexdigest()
    assert digest == "8d49b7b6f5a6b45881784495e727b3762b35fa3cc30dde7f46aca5aded5d48e1"
    print(
        "Relative defining polynomial modulo the support prime, descending coefficients:",
        digest,
    )
    print("Coefficient of degree 576 and constant term:", monic[1], monic[-1])
    return monic


def divisor_and_moments():
    frobenius = 82 * pow(511, -1, P) % P
    n0 = 2 * pow(frobenius, -1, P) % P
    mult = [pow(5, i, P) for i in range(P - 1)]
    vals = [n0 * a % P for a in mult]
    assert len(set(vals)) == P - 1
    assert sum(v * frobenius * pow(a, -1, P) for a, v in zip(mult, vals)) % P == P - 2
    assert [389 * 442 % P, 495 * 366 % P] == [4 * (-2) % P] * 2
    absolute = sum(min(v, P - v) for v in vals)
    assert (frobenius, n0, absolute) == (296, 308, 83232)
    print("Support valuations start at", n0, "and have least absolute sum", absolute)
    assert -131 * 64 * 511 % P == 1
    inertia = {pow(5, 8 * i, P) for i in range(72)}
    assert len(inertia) == 72
    # The norm and the first moment in the t coordinate; t=0 has zero diagonal.
    lower = [488] + [0] * (P - 1)
    diag = [0] + [190 * pow(t, -1, P) % P for t in range(1, P)]
    assert (
        8 * sum(lower) % P,
        sum(diag) % P,
        -8 * sum(t * v for t, v in enumerate(diag)) % P,
    ) == (442, 0, 366)
    assert all(diag[t * a % P] * a % P == diag[t] for t in range(P) for a in inertia)
    assert sum(t * v for t, v in enumerate(diag)) % P == 387
    assert 482 * 171 % P == 488
    print(
        "Lower total 488; diagonal total 0 and signed first moment 366 across eight places."
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--coefficients",
        action="store_true",
        help="print the full monic polynomial modulo 12407809",
    )
    args = parser.parse_args()
    divisor_and_moments()
    coefficients = polynomial_at_support()
    if args.coefficients:
        print(coefficients)
