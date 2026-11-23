"""Exact finite controls for cyclotomic traces, small sections and ramified levels."""

from fractions import Fraction
from itertools import combinations, product
from math import comb, factorial, gcd, isqrt


def polynomial_remainder(dividend, monic_divisor):
    """Polynomials are low coefficient first. Division by a monic stays integral."""
    assert monic_divisor[-1] == 1
    remainder = list(dividend)
    while len(remainder) >= len(monic_divisor):
        offset = len(remainder) - len(monic_divisor)
        lead = remainder[-1]
        for i, coefficient in enumerate(monic_divisor):
            remainder[offset + i] -= lead * coefficient
        while remainder and remainder[-1] == 0:
            remainder.pop()
    return remainder


def check_prime_power_fourier(prime, exponent):
    stride = prime ** (exponent - 1)
    order = prime * stride
    degree = order - stride
    cyclotomic = [int(i % stride == 0) for i in range(degree + 1)]

    # Compute traces of multiplication by powers in the power basis, without
    # using the character sum or the pair-difference identity being checked.
    traces = []
    for j in range(order):
        trace = 0
        for i in range(degree):
            power = (i + j) % order
            reduced = polynomial_remainder([0] * power + [1], cyclotomic)
            if i < len(reduced):
                trace += reduced[i]
        traces.append(trace)
    for seed in range(1, 6):
        coeffs = [((seed * i * i + 3 * i + 1) % 11) - 5 for i in range(order)]
        trace_square = sum(a * b * traces[(i - j) % order]
                           for i, a in enumerate(coeffs) for j, b in enumerate(coeffs))
        blocks = [coeffs[r::stride] for r in range(stride)]
        differences = sum((a - b) ** 2 for block in blocks for a, b in combinations(block, 2))
        assert trace_square == stride * differences
        costs = [min(sum((a - anchor) ** 2 for a in block) for anchor in block)
                 for block in blocks]
        assert prime * sum(costs) <= 2 * differences


def fifth_root_house_count(radius):
    # Inverse Fourier bounds the four power-basis coefficients by 8R/5.
    bound = 8 * radius // 5
    count = 0
    for coeffs in product(range(-bound, bound + 1), repeat=4):
        v = coeffs + (0,)
        c0, c1, c2 = [sum(v[i] * v[(i + t) % 5] for i in range(5)) for t in range(3)]
        # Require both conjugate squared moduli to be <= R^2.
        gap = 2 * radius ** 2 - 2 * c0 + c1 + c2
        if gap >= 0 and gap ** 2 >= 5 * (c1 - c2) ** 2:
            count += 1
    return count


def check_small_sections():
    gaussian = sum(sum(a * a for a in v) <= 4 for v in product(range(-2, 3), repeat=4))
    assert gaussian == 89
    counts = [fifth_root_house_count(radius) for radius in (1, 2, 3)]
    assert counts == [11, 61, 301]
    for prime, exponent in [(3, 1), (3, 2), (3, 3), (5, 1), (5, 2), (7, 1)]:
        check_prime_power_fourier(prime, exponent)
    print("Gaussian linear sections:", gaussian)
    print("House at most 1, 2, 3 in Q(zeta_5):", counts)
    print("Prime-power trace and anchor identities: six power bases, five test vectors each")


def check_gauss_periods(prime):
    # Work in Z[X]/Phi_p. Two vectors of length p give the same element
    # exactly when their difference is constant.
    residues = {a * a % prime for a in range(1, prime)}
    n = (prime - 1) // 2
    assert prime % 16 == 7 and len(residues) == n
    chi = [0] + [1 if a in residues else -1 for a in range(1, prime)]
    square = [sum(chi[j] * chi[(k - j) % prime] for j in range(prime))
              for k in range(prime)]
    square[0] += prime
    assert len(set(square)) == 1

    # (1-zeta)^n / tau = -(1-zeta)^n tau / p. Test divisibility by p
    # in the power basis. Its absolute norm is 1 since Norm(1-zeta)=p.
    binomial = [(-1) ** j * comb(n, j) for j in range(n + 1)]
    numer = [-sum(term * chi[(k - j) % prime] for j, term in enumerate(binomial))
             for k in range(prime)]
    assert all((val - numer[-1]) % prime == 0 for val in numer[:-1])

    # Store a period as a + b*tau, with tau^2 = -p.
    def period(k):
        k %= prime
        if k == 0:
            return Fraction(n), Fraction(0)
        return Fraction(-1, 2), Fraction(chi[k], 2)

    a, b = period(1)
    assert a * a + prime * b * b == (prime + 1) // 4
    assert gcd((prime + 1) // 4, n) == 1
    assert Fraction((prime + 1) // 4, n * n) < 1
    assert n ** (2 * n) > prime ** (n - 1)

    # Tr((zeta^u-zeta^v)zeta^k/tau) must lie in Z[(1+tau)/2]
    # on every power-basis vector, including the two exceptional exponents.
    u, v = 1, chi.index(-1)
    for k in range(prime):
        a1, b1 = period(k + u)
        a2, b2 = period(k + v)
        real, imag = b1 - b2, -(a1 - a2) / prime
        assert (real - imag).denominator == (2 * imag).denominator == 1
        if k == 0:
            assert (real, imag) == (1, 0)

        exponent_sum = [0] * prime
        for j in residues:
            exponent_sum[j * (k + u) % prime] += 1
            exponent_sum[j * (k + v) % prime] -= 1
        # Multiply (real + imag*tau) by tau and check in the cyclotomic ring.
        delta = [entry - real * symbol for entry, symbol in zip(exponent_sum, chi)]
        delta[0] += prime * imag
        assert len(set(delta)) == 1


def check_window_denominator():
    for prime in (7, 23, 71, 103, 167, 263):
        check_gauss_periods(prime)
    d = 5_368_439
    denominator = (d - 1) // 2
    for value in (d, denominator):
        assert all(value % divisor for divisor in range(2, isqrt(value) + 1))
    assert all((d + 1) % prime == 0 and denominator % prime for prime in (3, 5, 7, 11))
    assert gcd((d + 1) // 4, denominator) == 1
    print("Gauss periods and integral weighted retractions: six complete cyclotomic power bases")
    print("Earlier finite window example: d =", d, "and prime trace denominator =", denominator)


def multiplicative_order(a, modulus):
    assert gcd(a, modulus) == 1 and modulus > 1
    residue = a % modulus
    order = 1
    while residue != 1:
        residue = residue * a % modulus
        order += 1
    return order


def check_ramified_frames():
    phi20 = [1, 0, -1, 0, 1, 0, -1, 0, 1]
    alpha = [1, -1, 0, 1]
    r1 = polynomial_remainder(phi20, alpha)
    r2 = polynomial_remainder(alpha, r1)
    assert (r1, r2, polynomial_remainder(r1, r2)) == ([2, -2, 1], [-3, 1], [5])
    assert [(1 - i + i ** 3) % 5 for i in (2, 3)] == [2, 0]
    assert 4 ** 4 * 125 ** 2 == 4_000_000
    minkowski_upper = (Fraction(400, 314) ** 4 * Fraction(factorial(8), 8 ** 8) * 2000)
    assert minkowski_upper < 13
    assert [multiplicative_order(p, n) for p, n in [(2, 5), (3, 20), (7, 20), (11, 20)]] == [4, 4, 4, 2]

    # In F_5[t]/t^4, use t = zeta_5 - 1 and represent a unit by four coefficients.
    units = {v for v in product(range(5), repeat=4) if v[0]}
    roots = {tuple(a * comb(b, j) % 5 if j <= b else 0 for j in range(4))
             for a in range(1, 5) for b in range(5)}
    assert len(roots) == 20 and roots <= units and len(units) == 500
    assert len({v[0] for v in roots}) == 4 and sum(v[0] == 1 for v in roots) == 5
    assert len(units) // len(roots) == 25
    assert Fraction(4, 20) == Fraction(1, 5)

    # The two displayed type primes in the Gaussian example require separate roots.
    assert multiplicative_order(5, 156) == multiplicative_order(13, 60) == 4
    kernels = [{j for j in range(780) if j % size == 0} for size in (156, 60)]
    assert [len(s) for s in kernels] == [5, 13] and kernels[0] & kernels[1] == {0}
    assert (5 ** 4 - 1) * (13 ** 4 - 1) == 22_848 * 780
    print("Q(zeta_20) reduced frames: 1 orbit, stabilizer 5, mass 1/5")
    print("Q(zeta_20) modulo the extended ideal: 25 free frame orbits")
    print("Q(zeta_780) two reduced frames on the standard line: 22,848 free orbits")


if __name__ == "__main__":
    check_small_sections()
    check_ramified_frames()
    check_window_denominator()
