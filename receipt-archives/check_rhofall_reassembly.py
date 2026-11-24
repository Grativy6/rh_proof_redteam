"""Reassemble the four real character ramps on the modulus-one branch.

Standard Python, with the two existing large-prime certificates in this folder.
The identities over all scales and the functional equation are proved in the
accompanying receipt. This program checks finite coefficients and controls.
"""

from fractions import Fraction

from check_prime_window_readouts import (
    certify_window_primes,
    legendre,
    log_interval,
    prime_powers,
)


def character_row(n, q, d):
    a, b = legendre(n, q), legendre(n, d)
    return 1, a, b, a * b


def projected_coefficient(p, exponent, q, d):
    if p == d:
        return 2 if exponent % 2 == 0 else 0
    if p == q or exponent % 2 == 0:
        return 0
    return 4 if (legendre(p, q), legendre(p, d)) == (1, -1) else 0


def check_prime(p, q, d, exponents):
    _, a, b, both = character_row(p, q, d)
    # Evaluate the Euler factor as a rational number, away from poles.
    t = Fraction(1, p + 1)
    ratio = (1 - b * t) * (1 - both * t) / ((1 - t) * (1 - a * t))
    if p == d:
        expected_factor = 1 / (1 - t * t)
    elif a == 1 and b == -1:
        expected_factor = ((1 + t) / (1 - t)) ** 2
    else:
        expected_factor = 1
    assert ratio == expected_factor

    for j in exponents:
        principal, first, second, product = character_row(p**j, q, d)
        observed = projected_coefficient(p, j, q, d)
        assert principal + first - second - product == observed
        assert observed - first + second + product == principal


def check_raw_ramps(q, d, x):
    # Preserve each formal log(p) separately. Fraction also allows noninteger x.
    full = {}
    selected = {}
    for n, p in prime_powers(int(x)):
        exponent, power = 1, p
        while power < n:
            power *= p
            exponent += 1
        weight = x / n - 1
        values = full.setdefault(p, [Fraction(0) for _ in range(4)])
        for i, coefficient in enumerate(character_row(n, q, d)):
            values[i] += coefficient * weight
        selected[p] = (
            selected.get(p, Fraction(0))
            + projected_coefficient(p, exponent, q, d) * weight
        )
    for p, (principal, first, second, product) in full.items():
        assert selected[p] - first + second + product == principal


def quadratic_l_at_minus_two(q, d=None):
    # L(-2, chi) = -f^2/3 sum chi(a) B_3(a/f).
    conductor = q if d is None else q * d
    total = Fraction(0)
    for a in range(1, conductor + 1):
        x = Fraction(a, conductor)
        bernoulli = x**3 - Fraction(3, 2) * x * x + x / 2
        value = legendre(a, q)
        if d is not None:
            value *= legendre(a, d)
        total += value * bernoulli
    return -Fraction(conductor**2, 3) * total


def check_dyadic_and_pages():
    y = 2**40
    terms = sum((Fraction(y, 2**j) - 1 for j in range(1, 41)), Fraction(0))
    assert terms == y - 41
    assert [projected_coefficient(2, j, 3, 23) for j in range(1, 41)] == [0] * 40

    exponent = Fraction(2) + 8 * Fraction(1, 55)
    assert 55 * exponent == 118
    assert [e for e in range(121) if 2**118 <= 2**e <= 2 * 2**118] == [118, 119]
    for e in (5, 6, 118, 119):
        conductor_exponent = sum((k + 2) * 2 ** (k - 1) for k in range(1, e + 1))
        assert conductor_exponent == (e + 1) * 2**e - 1
    assert pow(577, 2**112, 2**119) == 1 + 2**118
    assert pow(577, 2**113, 2**119) == 1
    assert pow(5, 32, 256) == 129
    assert pow(5, 9 * 39, 577) == 510 and pow(510, 32, 577) == 576
    print("At 2^40 the omitted raw principal weight is (2^40 - 41) log 2.")
    print(
        "At x=2^55 both pages 118 and 119 fit. The earlier 5-to-6 character sign is -1 modulo 577."
    )


def check_joint_budget():
    # x = z^55. Compare B(x) / x^401 without rounding x, B, or the cutoff.
    z = Fraction(117162393, 200)
    log2_low, log2_high = log_interval(2, terms=32)
    rem_low, rem_high = log_interval(z / 2**19, terms=32)
    logz_low = 19 * log2_low + rem_low
    logz_high = 19 * log2_high + rem_high
    assert 1053 * log2_high < 55 * logz_low < 55 * logz_high < 1054 * log2_low

    log_ratio_low = z / 2 - 22055 * logz_high
    log_ratio_high = z / 2 - 22055 * logz_low
    lower_reciprocal, _ = log_interval(Fraction(1000, 349), terms=32)
    _, upper_reciprocal = log_interval(Fraction(20, 7), terms=32)
    assert -lower_reciprocal < log_ratio_low <= log_ratio_high < -upper_reciprocal

    rem_low, rem_high = log_interval(Fraction(577, 512), terms=32)
    log577_low = 9 * log2_low + rem_low
    log577_high = 9 * log2_high + rem_high
    assert 6 < log577_low < log577_high < 7
    assert log2_high / 2 < Fraction(347, 1000)
    assert log577_high * (Fraction(1, 576) + Fraction(1, 2**40)) < Fraction(13, 1000)
    assert log2_low / 2 + log577_low / 576 > Fraction(71, 200)
    assert 2 * (log2_high + log577_high) < 16
    assert 2**40 > 16 * 200
    for t in range(1, 1601):
        assert (t + 279) // 576 == len(range(296, t, 576))
    print(
        "At X=(117162393/200)^55 each known prime contribution fits; together they exceed the budget."
    )
    print("Rational log bounds put B(X)/X^401 strictly between 0.349 and 0.350.")


def main():
    large_ds = certify_window_primes()
    q = 3
    for p in sorted({p for _, p in prime_powers(251)}):
        check_prime(p, q, 23, range(1, 7))
    for x in (Fraction(529), Fraction(1071, 2)):
        check_raw_ramps(q, 23, x)
    assert (
        quadratic_l_at_minus_two(q),
        quadratic_l_at_minus_two(23),
        quadratic_l_at_minus_two(q, 23),
    ) == (Fraction(-2, 9), -48, 0)

    m = 2**40 + 15
    for d in large_ds:
        for p in (2, q, 5, 7, 11, 13, 17, 19, m, d):
            check_prime(p, q, d, (1, 2, 3, 4))
    assert [projected_coefficient(m, 1, q, d) for d in large_ds] == [4, 0]
    print(
        "Primitive coefficients reassemble prime by prime, including the ramified primes."
    )
    print(f"At prime {m} the two certified pairs give projected weights 4 and 0.")
    print("For q=3, d=23 the three quadratic L-values at -2 are -2/9, -48 and 0.")
    check_dyadic_and_pages()
    check_joint_budget()


if __name__ == "__main__":
    main()
