"""Resolve the 27 low-conductor carry zeros by local Jacobi digits.

The two prime inputs give independent Jacobi elements. The degree-four
coefficient arithmetic and the original fixed-class control are shared
with fourier_witness.py. All arrays are integral.
"""

from math import gcd, lcm

import numpy as np

import fourier_witness as witness
from dyadic_conductors import P, low_candidates


def jacobi_histogram(prime):
    conductor = 256 * P
    assert (prime - 1) % conductor == 0 and witness.factors(prime) == [prime]
    generator = witness.primitive(prime)
    indices = np.empty(prime, dtype=np.int32)
    residue, exponent = 1, 0
    for _ in range(1, prime):
        indices[residue] = exponent
        residue = residue * generator % prime
        exponent = (exponent + 1) % conductor
    assert residue == 1 and exponent == 0
    x = np.arange(2, prime, dtype=np.int64)
    # chi^{-1}(x(1-x)); group the exponents by their two CRT residues.
    powers = -indices[(x * (1 - x)) % prime] % conductor
    counts = np.bincount(powers, minlength=conductor)
    positions = np.arange(conductor)
    result = np.zeros((256, P), dtype=np.int64)
    result[positions % 256, positions % P] = counts
    assert int(result.sum()) == prime - 2
    return result


def logarithmic_coefficients(histogram, degree):
    # Zeta_p=exp(X); Zeta_256=Y in F_p[Y]/(Y^4-20). The nonprimitive
    # dyadic exponents implement the same Jacobi construction at smaller C.
    dyadic = np.arange(256)
    p_part = np.arange(P)
    roots = witness.roots(20, 64, P)
    moments = np.ones((P, degree + 1), dtype=np.int64)
    for k in range(1, degree + 1):
        moments[:, k] = moments[:, k - 1] * p_part * pow(k, -1, P) % P

    series = np.empty((255, degree + 1, 4), dtype=np.int64)
    for u in range(1, 256):
        powers = dyadic * u % 256
        for i in range(4):
            mask = powers % 4 == i
            values = roots[powers[mask] // 4] @ histogram[mask] % P
            series[u - 1, :, i] = values @ moments % P

    inverse = witness.power(series[:, 0, :], P**4 - 2)
    assert np.all(witness.times(series[:, 0, :], inverse) == [1, 0, 0, 0])
    normalized = witness.times(
        series.reshape(-1, 4), np.repeat(inverse, degree + 1, axis=0)
    )
    series = normalized.reshape(series.shape)
    derivative = np.zeros_like(series)
    # X J'/J gives k times the coefficient of X^k in log(J/J(0)).
    for k in range(1, degree + 1):
        product = np.einsum(
            "vji,vjk->vik",
            series[:, 1:k, :],
            derivative[:, k - 1 : 0 : -1, :],
            optimize=False,
        )
        derivative[:, k, :] = (
            k * series[:, k, :] - witness.reduce_product(product)
        ) % P
    return derivative


def projected_digits(rows, derivative):
    digits = {}
    for s, candidates in rows.items():
        c = 2**s
        order = c // 4
        root = pow(5, (P - 1) // order, P)
        values = {}
        for i in range(order):
            unit = pow(5, i, c)
            values[unit] = values[c - unit] = pow(root, i, P)
        units = np.arange(1, c, 2)
        for b, j, _ in candidates:
            weights = np.array([pow(values[int(u)], -b, P) for u in units])
            terms = derivative[units * (256 // c) - 1, j + 1, :]
            result = (weights @ terms) * pow(j + 1, -1, P) % P
            digits[s, b, j] = tuple(int(v) for v in result)
    return digits


def check_class_number_factors(rows):
    # Each odd power labels a character of the specific cyclic field cut out
    # by lambda. Count its divisible factors; each has valuation exactly one.
    for s, candidates in rows.items():
        possible = {(b, j) for b, j, _ in candidates}
        dyadic_order = 2 ** (s - 2)
        for b, j, _ in candidates:
            degree = lcm(dyadic_order, (P - 1) // gcd(P - 1, j + 1))
            powers = {
                (b * i % dyadic_order, ((j + 1) * i - 1) % (P - 1))
                for i in range(1, degree, 2)
            }
            assert len(powers) == degree // 2 and (b, j) in powers
            assert all(
                digit != 0
                for label, twist, digit in candidates
                if (label, twist) in powers
            )
            yield s, b, j, len(powers & possible)


def main():
    rows = low_candidates()
    degree = max(j + 1 for candidates in rows.values() for _, j, _ in candidates)
    first = jacobi_histogram(witness.R)
    assert np.array_equal(first, witness.histogram())
    second = jacobi_histogram(witness.D)
    a = projected_digits(rows, logarithmic_coefficients(first, degree))
    b = projected_digits(rows, logarithmic_coefficients(second, degree))
    for values in (a, b):
        assert {key for key, digit in values.items() if not any(digit)} == {
            (8, 39, 296)
        }
    assert witness.detect(first) == (1497311, 333)
    assert pow(1497311, P, witness.D) == 1 and 1497311 != 1
    print("s b j v_p(h-minus of its cyclic field) local at r=1920257 / r=2363393")
    for s, label, j, length in check_class_number_factors(rows):
        key = s, label, j
        print(s, label, j, length, a[key], b[key])
    print("Only (s,b,j)=(8,39,296) has zero local digit in both constructions.")
    print("Its global power-residue symbol is 1497311 modulo 2363393.")


if __name__ == "__main__":
    main()
