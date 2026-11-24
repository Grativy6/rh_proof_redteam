"""Exact integer checks for the 5-primary Selmer and modular-form examples."""
from math import gcd, isqrt

Q = 571
RADICAND = -5 * Q
BETA = (3657, -50)
ONE = (1, 0)
# Coefficients in ascending order for the monic quintic, excluding the leading one.
QUINTIC = (-7314, 4205, 0, -145, 0)
# Each prime is 8 * 3 * 7 * 571 * k * 5**b - 1.
# The boolean records whether its Frobenius detects the nonzero class.
PROBES = (
    (1, 1, True), (1, 7, False), (2, 3, True), (2, 13, False),
    (6, 37, True), (6, 49, False), (16, 9, True), (16, 341, False),
    (52, 11, True), (52, 1259, False), (100, 493, True), (100, 1609, False),
)


def norm(z):
    x, y = z
    return x*x - RADICAND*y*y


def mul(z, w, n):
    x, y = z
    u, v = w
    return ((x*u + RADICAND*y*v) % n, (x*v + y*u) % n)


def power(z, exponent, n, product, identity):
    value = identity
    while exponent:
        if exponent & 1:
            value = product(value, z, n)
        z = product(z, z, n)
        exponent //= 2
    return value


def trial_prime(n):
    return n >= 2 and all(n % i for i in range(2, isqrt(n) + 1))


def certify_prime(n, b):
    if 5**b - 1 <= isqrt(n):
        assert trial_prime(n)
        return
    assert gcd(n, 2*5*RADICAND) == 1
    assert (n + 1) % 5**b == 0 and (n + 1) % 5**(b+1) != 0
    # z = (a+s)/(a-s) has norm 1. At every prime divisor p of n it lies
    # in a group of order p-1 or p+1, according as s**2 = RADICAND splits or not.
    for a in range(1, 101):
        denominator = norm((a, 1))
        if gcd(denominator, n) != 1:
            continue
        z = mul(mul((a, 1), (a, 1), n), (pow(denominator, -1, n), 0), n)
        w = power(z, (n + 1)//5, n, mul, ONE)
        if power(w, 5, n, mul, ONE) == ONE and gcd(n, norm((w[0]-1, w[1]))) == 1:
            return
    raise AssertionError(f"Missing an n+1 primality certificate for {n}")


def quintic_mul(z, w, n):
    c = [0]*9
    for i, a in enumerate(z):
        for j, b in enumerate(w):
            c[i+j] += a*b
    for k in range(8, 4, -1):
        for j, a in enumerate(QUINTIC):
            c[k-5+j] -= c[k]*a
    return tuple(x % n for x in c[:5])


def check_probe(b, k, detected):
    d = 8*3*7*Q*k*5**b - 1
    certify_prime(d, b)
    assert d % 16 == 7 and all((d+1) % r == 0 for r in (3, 5, 7, Q))
    assert (d+1) % 5**(b+1) != 0 and pow(RADICAND, (d-1)//2, d) == d-1
    sign = power(BETA, (d*d-1)//5, d, mul, ONE)
    assert (sign != ONE) == detected and power(sign, 5, d, mul, ONE) == ONE

    # X**(d**5) = X implies the separable factors have degrees dividing 5.
    # A degree-five polynomial in this situation either splits or is irreducible.
    x, one = (0, 1, 0, 0, 0), (1, 0, 0, 0, 0)
    assert power(x, d**5, d, quintic_mul, one) == x
    assert (power(x, d, d, quintic_mul, one) != x) == detected
    for t, extra in ((1, 0), (5, 1), (25, 2), (125, 3)):
        first = b + extra + 1 if detected else 1
        for n in range(1, first + 2):
            modulus = 5**n
            frob = -pow(pow(d, t, modulus), -1, modulus) % modulus
            rhs = 5**(n-1) if detected else 0
            soluble = rhs % gcd(frob-1, modulus) == 0
            assert soluble == (n >= first)
    return d


def legendre(a, p):
    r = pow(a % p, (p-1)//2, p)
    return -1 if r == p-1 else r


def check_classical_forms():
    # q * product (1-q^n)^3 (1-q^(7n))^3, through the coefficient of q^36.
    terms = [0, 1] + [0]*35
    for spacing in (1, 7):
        for n in range(spacing, len(terms), spacing):
            for _ in range(3):
                for j in range(len(terms)-1, n-1, -1):
                    terms[j] -= terms[j-n]
    assert (terms[5], terms[11]) == (0, -6)
    assert (legendre(11, 7), legendre(11, Q), 11 % 5) == (1, 1, 1)
    assert (terms[11] - (11**2 + 1)) % 5 != 0
    D = 7*Q
    character = [legendre(a, 7)*legendre(a, Q) for a in range(1, D+1)]
    assert sum(character) == sum(a*v for a, v in enumerate(character, 1)) == 0
    moment = sum(a*a*v for a, v in enumerate(character, 1))
    assert moment == D*22416 and 22416 % 5 == 1
    traces = {(1 + z + pow(z, -1, 5)) % 5 for z in range(1, 5)}
    assert traces == {1, 3, 4}
    return terms[5], terms[11], moment//D


def main():
    assert trial_prime(Q) and Q % 8 == 3
    assert norm(BETA) == 29**5 and (2*BETA[0]) % 29 != 0
    assert (BETA[0] - 2**5) == 125*29
    assert BETA[1] % 25 == 0 and BETA[1] % 125 != 0 and RADICAND % 25 != 0
    for b, k, detected in PROBES:
        d = check_probe(b, k, detected)
        print(f"d={d}, v5(d+1)={b}, quintic={'irreducible' if detected else 'split'}, "
              f"first strict coefficient level={b+1 if detected else 1}")
    a5, a11, bernoulli = check_classical_forms()
    print(f"Level-seven a5={a5}, a11={a11}. B_2 for conductor 3997 equals {bernoulli}.")


if __name__ == "__main__":
    main()
