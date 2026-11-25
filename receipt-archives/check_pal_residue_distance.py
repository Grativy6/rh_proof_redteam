"""Replay a finite rational witness for the full weighted residue distance.

Only Python's standard library is required. The bounds use integers throughout.
"""
from fractions import Fraction
from math import isqrt

# The entries are indexed by increasing squarefree d from 2 through 101.
# Divide by 100 to obtain the coefficient of (k mod d)/d.
HUNDREDTHS = (
    98, 96, 88, -74, 81, -64, 67, 66, -62, -59, 59, 53, -53, -49, 51,
    -47, 42, 43, 49, -50, -35, -44, 50, -33, -54, 32, 42, 38, -31,
    29, -35, 35, -24, -20, -28, 19, 24, -36, -26, 44, 12, -24, 38,
    12, 17, -33, -21, 43, 17, -24, 30, -28, -25, -16, 24, -20, -32,
    -21, -19, 37, 51,
)
CUTOFF = 4_000_000
SCALE = 1 << 64


def squarefree(n):
    return all(n % (i * i) for i in range(2, isqrt(n) + 1))


def finite_witness():
    moduli = [d for d in range(2, 102) if squarefree(d)]
    coefficients = dict(zip(moduli, HUNDREDTHS, strict=True))
    # For F(k) = sum a_d b_d(k), F(k)-F(k-1) = slope - sum_{d|k} a_d.
    # Store each jump as an integer number of hundredths.
    slope = sum(Fraction(c, 100 * d) for d, c in coefficients.items())
    denominator = 100 * slope.denominator
    step = 100 * slope.numerator
    residual = denominator
    resets = [0] * (CUTOFF + 1)
    for d, c in coefficients.items():
        for k in range(d, CUTOFF + 1, d):
            resets[k] += c

    squared_denominator = denominator**2
    rounded_sum = 0
    for k in range(1, CUTOFF + 1):
        residual += slope.denominator * resets[k] - step
        if k <= 202:
            direct = 1 - sum(Fraction(c * (k % d), 100 * d)
                             for d, c in coefficients.items())
            assert Fraction(residual, denominator) == direct
        term_denominator = squared_denominator * k * (k + 1)
        term_numerator = SCALE * residual**2
        rounded_sum += (term_numerator + term_denominator - 1) // term_denominator

    head = Fraction(rounded_sum, SCALE)
    envelope = 1 + Fraction(sum(map(abs, HUNDREDTHS)), 100)
    tail = envelope**2 / (CUTOFF + 1)
    assert head + tail < Fraction(1, 92)
    return head, tail


def four_readings(d):
    return Fraction(-2 * (1 % d) + (3 % d) + (5 % d) - (6 % d), d)


def check_prefix_identity():
    """Test the closed-form next-block calculation against direct rational readings."""
    def mobius(n):
        if not squarefree(n):
            return 0
        primes = (p for p in range(2, n + 1)
                  if n % p == 0 and all(p % i for i in range(2, isqrt(p) + 1)))
        return (-1) ** sum(1 for _ in primes)

    mu = [0] + [mobius(n) for n in range(1, 64)]
    for n in range(2, 33):
        pivot = n * sum(Fraction(mu[d], d) for d in range(1, n))
        coefficients = {d: -mu[d] for d in range(2, n)}
        coefficients[n] = pivot
        for k in range(1, 2 * n):
            fitted = sum(a * Fraction(k % d, d) for d, a in coefficients.items())
            expected = 0 if k < n else pivot + sum(mu[n:k + 1])
            assert 1 - fitted == expected


if __name__ == "__main__":
    check_prefix_identity()
    # For d > 6 all four remainders equal their numerators.
    assert [four_readings(d) for d in range(2, 8)] == [0, 0, 0, 0, 1, 0]
    norm_squared = sum(c * c * k * (k + 1) for k, c in [(1, -2), (3, 1), (5, 1), (6, -1)])
    assert norm_squared == 92
    head, tail = finite_witness()
    print(f"Head upper bound: {head}")
    print(f"Tail upper bound: {tail}")
    print(f"Full squared error < 1/92: {head + tail < Fraction(1, 92)}")
