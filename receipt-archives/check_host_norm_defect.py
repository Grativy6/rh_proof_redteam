"""Exact norm, self-dual ideal, and rank-one genus checks for the zeta hosts."""

from fractions import Fraction
from itertools import product
from math import gcd, isqrt


def prime(n):
    return n >= 2 and all(n % k for k in range(2, isqrt(n) + 1))


def sign(a, p):
    value = pow(a % p, (p - 1) // 2, p)
    assert value in (1, p - 1)
    return 1 if value == 1 else -1


def local_exterior_rows(q, d):
    # Coordinates: real cyclotomic generator wedge q, generator wedge d, q wedge d.
    at_two = (1, 0, 0)
    at_q = (1, 0, int(sign(-d, q) < 0))
    at_d = (0, 0, int(sign(-q, d) < 0))
    assert at_q[2] + at_d[2] == 1
    span = {
        tuple(
            sum(e * v[j] for e, v in zip(mask, (at_two, at_q, at_d))) % 2
            for j in range(3)
        )
        for mask in product(range(2), repeat=3)
    }
    assert span == {(a, 0, c) for a, c in product(range(2), repeat=2)}
    return at_two, at_q, at_d


def quartic_product(left, right):
    # theta=2 cos(pi/8), theta^4=4 theta^2-2.
    coef = [0] * 7
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            coef[i + j] += a * b
    for k in range(6, 3, -1):
        coef[k - 2] += 4 * coef[k]
        coef[k - 4] -= 2 * coef[k]
    return coef[:4]


def quartic_norm(coef):
    conjugate = [a * (-1) ** i for i, a in enumerate(coef)]
    A, B, C, D = quartic_product(coef, conjugate)
    assert B == D == 0
    return (A + 2 * C) ** 2 - 2 * C * C


def small_witness():
    assert prime(31) and 31 % 16 == 15
    assert all(sign(31, p) == 1 for p in (3, 11, 23))
    assert 7**2 - 2 * 3**2 == 31
    assert 5**2 % 23 == 2 and [(7 + 3 * t) % 23 for t in (5, -5)] == [22, 15]
    assert sign(22, 23) == sign(15, 23) == -1
    assert 16**2 + 23 == 31 * 3**2 and 5**2 + 11 * 3**2 == 31 * 2**2
    # For q=3,d=23 use s^2-s-17=0 and beta=v+s*theta.
    v = [1, 3, 2, -1]
    theta = [0, 1, 0, 0]
    terms = (
        quartic_product(v, v),
        quartic_product(v, theta),
        quartic_product(theta, theta),
    )
    norm_to_quartic = [a + b - 17 * c for a, b, c in zip(*terms)]
    assert norm_to_quartic == [-1, 15, 1, -4] and quartic_norm(norm_to_quartic) == 31
    # For q=11,d=23 use beta=1+(s-8)*theta, s^2-s-63=0.
    assert quartic_norm([1, -15, -7, 0]) == 31**3
    assert Fraction(31**9, 31**8) == 31


def class_sum(q, t):
    # First primitive generalized Bernoulli value for chi_-q times rho^t.
    conductor = (1, 16, 8, 16)[t] * q
    rho = {sgn * pow(5, j, 16) % 16: j for j in range(4) for sgn in (-1, 1)}
    out = [0, 0]
    for a in range(1, conductor + 1):
        if gcd(a, conductor) != 1:
            continue
        j = t * rho[a % 16] % 4 if t else 0
        out[j % 2] += a * sign(a, q) * (1 if j < 2 else -1)
    return tuple(Fraction(c, conductor) for c in out)


def class_count(q, d, roots):
    result = Fraction(2 * roots)
    for prime_conductor in (q, d):
        z = [class_sum(prime_conductor, t) for t in range(4)]
        assert z[0][1] == z[2][1] == 0 and z[3] == (z[1][0], -z[1][1])
        result *= z[0][0] * z[2][0] * (z[1][0] ** 2 + z[1][1] ** 2) / 16
    assert result.denominator == 1
    return int(result)


def main():
    small_witness()
    qs = [q for q in range(3, 500) if prime(q) and q % 8 == 3]
    ds = [d for d in range(7, 500, 16) if prime(d)]
    for q, d in product(qs, ds):
        local_exterior_rows(q, d)
    assert class_count(3, 23, 6) == 60 and class_count(11, 23, 2) == 300
    # For d=23, (3+sqrt(-23))/2 has norm 8. Norm 2 is impossible.
    assert (3**2 + 23) // 4 == 8 and all(
        isqrt(8 - 23 * y * y) ** 2 != 8 - 23 * y * y for y in range(isqrt(8 // 23) + 1)
    )
    print(
        "31 passes every local norm test. The attempted shared quadratic preimage gives nonsquares 22 and 15 at 23."
    )
    print(
        "The complete exterior calculation leaves one bit for all",
        len(qs) * len(ds),
        "prime pairs tested.",
    )
    print(
        "Rank-one genus sizes 60 and 300; the respective mean numbers of vectors of norm one are 1/10 and 1/150."
    )


if __name__ == "__main__":
    main()
