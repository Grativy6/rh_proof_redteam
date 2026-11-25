"""Exact coefficient-prime checks at 2663 for the real dyadic tower. Requires NumPy."""

from math import gcd, isqrt

import numpy as np


P = 2663
M = (P - 1) // 2


def is_prime(n):
    return n > 1 and all(n % k for k in range(2, isqrt(n) + 1))


def field_product(x, y):
    a, b = x
    c, d = y
    return ((a * c - b * d) % P, (a * d + b * c) % P)


def field_power(x, n):
    value = (1, 0)
    while n:
        if n & 1:
            value = field_product(value, x)
        x = field_product(x, x)
        n //= 2
    return value


def root_rows(order):
    # i^2=-1. The four Frobenius orbits at order 16 have representatives 1,3,9,11.
    z = field_power((1, 2), (P * P - 1) // 16)
    assert z == (484, 1147) and field_power(z, 8) == (P - 1, 0)
    base = field_power(z, 16 // order)
    reps, covered = [], set()
    for b in range(1, order, 2):
        if b not in covered:
            reps.append(b)
            covered.update((b, P * b % order))
    table = np.array([[field_power(base, (b * k) % order) for k in range(order)]
                      for b in reps], dtype=np.int64)
    return reps, table[:, :, 0].copy(), table[:, :, 1].copy()


def interval_table():
    # Column j/2 gives x^(-j-1), with zero at x=0. Prefixes permit wraparound.
    values = np.zeros((P, M), dtype=np.int64)
    values[1:, 0] = [pow(x, -1, P) for x in range(1, P)]
    ratio = values[:, 0] ** 2 % P
    for col in range(1, M):
        values[:, col] = values[:, col - 1] * ratio % P
    prefix = np.zeros((2 * P + 1, M), dtype=np.int64)
    np.cumsum(np.concatenate((values, values)), axis=0, out=prefix[1:])
    start = np.arange(P)
    intervals = (prefix[start + P] - prefix[start + M + 1]) % P
    return values, intervals


def moments(residues, endpoint, values, intervals):
    return (intervals[residues] + endpoint[:, None] * values[(M + residues) % P]) % P


def raw_columns(s, a, order, values, intervals):
    c = 1 << s
    step = pow(5, c // (4 * order), c)
    labels = [a * pow(step, k, c) % c for k in range(order)]
    inv = pow(c, -1, P)
    starts = np.array([(x % P) * inv % P for x in labels])
    endpoint = np.array([2 * x > c for x in labels])
    plus = moments(starts, endpoint, values, intervals)
    minus = moments((1 - starts) % P, ~endpoint, values, intervals)
    assert np.array_equal(plus, minus)
    return plus


def quotient_rows():
    # The four monic quadratic divisors of X^8+1 over F_p are X^2-tX-1.
    traces = [t for t in range(P) if (t**4 + 4 * t*t + 2) % P == 0]
    assert traces == [369, 968, 1695, 2294]
    constants, linear = [], []
    for t in traces:
        a, b = 1, 0
        u, v = [], []
        for _ in range(16):
            u.append(a)
            v.append(b)
            a, b = b, (a + t * b) % P
        constants.append(u)
        linear.append(v)
    return np.array(traces)[:, None], np.array(constants), np.array(linear)


def product_mod(entries):
    items = np.asarray(entries, dtype=np.int64).ravel()
    while len(items) > 1:
        if len(items) % 2:
            items = np.append(items, np.int64(1))
        items = items[::2] * items[1::2] % P
    return int(items[0])


def literal_moment(s, k, j):
    # CRT test over the unscaled interval, without the prefix table.
    c = 1 << s
    label = pow(5, (c // 64) * k, c)
    result = 0
    for b in range(P):
        x = label + c * b
        if 2 * x > c * P and x % P:
            result += pow(x, -j - 1, P)
    return result * pow(c, j + 1, P) % P


def dyadic_cases():
    values, intervals = interval_table()
    for s in range(3, 9):
        order = min(16, 1 << (s - 2))
        reps, real, imag = root_rows(order)
        live = np.ones((len(reps), M), dtype=bool)
        for r in range((1 << (s - 2)) // order):
            rows = raw_columns(s, 5**r, order, values, intervals)
            live &= ((real @ rows) % P == 0) & ((imag @ rows) % P == 0)
        cases = [(reps[b], 2 * int(j)) for b, j in np.argwhere(live)]
        assert cases == ([(1, 1232)] if s == 3 else [])
        print(f"Conductor {1 << s}: remaining inverse-character and twist pairs {cases}")

    assert pow(5, 8, 512) == 481
    assert pow(2, M, P) == 1 and pow(2, M // 11, P) == 72
    _, real, imag = root_rows(16)
    traces, coeff0, coeff1 = quotient_rows()
    u = 15 * np.arange(16) % 16
    product = 1
    for s in range(9, 9 + M):
        starts = (pow(pow(2, s, P), -1, P) + u * pow(16, -1, P)) % P
        compact = moments(starts, u >= 8, values, intervals)
        rows = raw_columns(s, 1, 16, values, intervals)
        assert np.array_equal(compact, rows)
        x, y = real @ compact % P, imag @ compact % P
        norms = (x*x + y*y) % P
        # Recompute as polynomial remainders modulo the four quadratics.
        a, b = coeff0 @ rows % P, coeff1 @ rows % P
        norms2 = (a*a + traces * a * b - b*b) % P
        assert np.array_equal(np.sort(norms, axis=0), np.sort(norms2, axis=0))
        assert np.all(norms)
        product = product * product_mod(norms) % P
        if s in (9, 57, 336, 1339):
            for k, j in ((0, 0), (5, 1232), (12, 1244), (15, 2660)):
                assert int(rows[k, j // 2]) == literal_moment(s, k, j)
    print(f"All {4*M*M:,} high-conductor cases have nonzero norm. Product {product}")
    assert product == 95


def low_unit():
    conductor, q = 8 * P, 63913
    assert is_prime(q) and q - 1 == 24 * P
    assert all(pow(13, (q-1)//r, q) != 1 for r in (2, 3, P))
    root = pow(13, (q - 1) // conductor, q)
    unit = 1
    carry = 0
    for a in range(1, conductor, 2):
        if a % P == 0:
            continue
        chi = 1 if a % 8 in (1, 7) else -1
        weight = chi * pow(a, 1232, P) % P
        unit = unit * pow((1 - pow(root, a, q)) % q, weight, q) % q
        if 2 * a > conductor:
            carry += chi * pow(a, -1233, P)
    assert (carry % P, root, unit, pow(unit, 24, q)) == (0, 2197, 60430, 41215)
    print("Conductor 8, twist 1232: upper-half carry 0, unit residue 60430, 24th power 41215")


def irregular_and_real():
    # Invert the power series (exp(X)-1)/X through degree p-3.
    modulus = P**2
    fact = [1] * P
    for n in range(1, P):
        fact[n] = n * fact[n-1] % modulus
    ifact = [1] * P
    ifact[-1] = pow(fact[-1], -1, modulus)
    for n in range(P - 1, 0, -1):
        ifact[n-1] = n * ifact[n] % modulus
    scaled = [1, (modulus - 1) // 2]
    zeros = []
    for n in range(2, P - 1):
        v = 0 if n % 2 else -(ifact[n+1] + scaled[1] * ifact[n]
                              + sum(scaled[k] * ifact[n+1-k] for k in range(2, n, 2))) % modulus
        scaled.append(v)
        if n % 2 == 0 and v % P == 0:
            zeros.append(n)
    assert zeros == [1244]
    assert scaled[1244] * fact[1244] % modulus == P * 612
    q, z = 31957, 4096
    assert is_prime(q) and q - 1 == 12 * P and z != 1 and pow(z, P, q) == 1
    value = 1
    for c in range(1, M + 1):
        diff = (pow(z, c, q) - pow(z, -c, q)) % q
        value = value * pow(diff, pow(c, P - 1 - 1244, q - 1), q) % q
    assert (value, pow(value, 12, q)) == (29748, 19454)
    print("Irregular index 1244; real-class test at 31957 gives 19454")


def other_roles():
    assert is_prime(P) and P - 1 == 2 * 11**3 and P + 1 == 2**3 * 3**2 * 37
    assert (P - 1)**2 == 4 * 11**6
    assert P % 8 == 7 and P % 16 == 7
    assert [r for r in range(2, P+2) if (P+1) % r == 0 and is_prime(r) and r % 8 == 3] == [3]
    for d in (-23, -43):
        assert pow(d % P, (P-1)//2, P) == 1
    assert (pow((-23) % 11, 5, 11), pow((-43) % 11, 5, 11)) == (10, 1)

    forms = []
    for a in range(1, isqrt(P // 3) + 1):
        for b in range(-a, a + 1):
            c, rem = divmod(b*b + P, 4*a)
            if rem or c < a or (b < 0 and (abs(b) == a or c == a)):
                continue
            if gcd(a, gcd(abs(b), c)) == 1:
                forms.append((a, b, c))
    assert len(forms) == 43 and 5137947**2 + P * 57439**2 == 2**45
    print("Distinguished-prime rank 7,086,244. Class number of discriminant -2663 is 43")


if __name__ == "__main__":
    other_roles()
    irregular_and_real()
    low_unit()
    dyadic_cases()
