"""Exact local checks for the CM curve y^2 = x^3 - 35x - 98, at 5."""

from dataclasses import dataclass
from fractions import Fraction
from math import comb, factorial


A, B = -35, -98
DEGREE = 25


def product_coefficient(poly, power, degree):
    """Coefficient of T^degree in poly(T)^power, truncated at degree."""
    result = [Fraction(1)] + [Fraction(0)] * degree
    for _ in range(power):
        updated = [Fraction(0)] * (degree + 1)
        for i, c in enumerate(result):
            if c:
                for j, a in enumerate(poly[: degree - i + 1]):
                    if a:
                        updated[i + j] += c * a
        result = updated
    return result[degree]


def log_coeff(n):
    """[t^n] l(t) from the residue of t^(-n) dx/(2y)."""
    if not n % 2:
        return Fraction(0)
    m = (n - 1) // 2
    total = 0
    for b in range(m // 3 + 1):
        if (m - 3 * b) % 2 == 0:
            a = (m - 3 * b) // 2
            total += comb(m, a) * comb(m - a, b) * A**a * B**b
    return Fraction(total, n)


def from_log():
    """Triangularly solve l(h(T)) = T + T^25/5 through degree 25."""
    result = [Fraction(0)] * (DEGREE + 1)
    result[1] = 1
    for n in range(2, DEGREE + 1):
        rhs = Fraction(1, 5) if n == 25 else Fraction(0)
        for m in range(2, n + 1):
            c = log_coeff(m)
            if c:
                rhs -= c * product_coefficient(result, m, n)
        result[n] = rhs
    return result


def weierstrass_coeffs(order):
    """wp = z^(-2) + sum c[j] z^(2j-2), independently from wp''."""
    c = [Fraction(0)] * (order + 1)
    c[2], c[3] = Fraction(-4 * A, 20), Fraction(-4 * B, 28)
    for j in range(4, order + 1):
        c[j] = Fraction(3, (2 * j + 1) * (j - 3)) * sum(
            c[i] * c[j - i] for i in range(2, j - 1)
        )
    return c


def from_wp(degree=DEGREE, sign=1):
    """Form -2wp/wp' in the signed height-two log input through first correction."""
    if not 1 <= degree < 5**4 or sign not in (-1, 1):
        raise ValueError("Choose degree below 625 and a sign of 1 or -1.")
    c = weierstrass_coeffs(max(3, degree // 2))
    numerator = [Fraction(0)] * (degree + 1)
    denominator = [Fraction(0)] * (degree + 1)
    numerator[1] = denominator[0] = 1
    for j in range(2, len(c)):
        if 2 * j + 1 <= degree:
            numerator[2 * j + 1] = c[j]
        if 2 * j <= degree:
            denominator[2 * j] = -(j - 1) * c[j]
    parameter = [Fraction(0)] * (degree + 1)
    for n in range(1, degree + 1):
        parameter[n] = numerator[n] - sum(
            denominator[j] * parameter[n - j] for j in range(1, n + 1)
        )

    # (T + sign*T^25/5)^m has total degree m+24*k after k replacements.
    coefficients = parameter.copy()
    for n in range(1, degree + 1):
        for k in range(1, n // 25 + 1):
            m = n - 24 * k
            coefficients[n] += parameter[m] * comb(m, k) * Fraction(sign, 5)**k
    return coefficients


def v5(x):
    x = Fraction(x)
    if not x:
        raise ValueError("zero has no finite valuation")
    a, b, v = abs(x.numerator), x.denominator, 0
    while a % 5 == 0:
        a //= 5
        v += 1
    while b % 5 == 0:
        b //= 5
        v -= 1
    return v


def residue(x):
    x = Fraction(x)
    return (x.numerator * pow(x.denominator, -1, 5)) % 5


@dataclass(frozen=True)
class Quad:
    """a + b*w, with w^2 = w - 2.  The basis is integral and unramified at 5."""
    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)

    def __add__(self, other):
        return Quad(self.a + other.a, self.b + other.b)

    def __mul__(self, other):
        return Quad(
            self.a * other.a - 2 * self.b * other.b,
            self.a * other.b + self.b * other.a + self.b * other.b,
        )

    def scale(self, scalar):
        return Quad(scalar * self.a, scalar * self.b)

    def power(self, n):
        result = Quad(1)
        for _ in range(n):
            result = result * self
        return result

    def residues(self):
        return (residue(self.a), residue(self.b))


def norm_defect_through_ten(s2):
    """Exp(phi([w]T)-2phi(T)), after removing the unit epsilon^n in each degree."""
    limit = 10
    c = weierstrass_coeffs(5)
    w = Quad(0, 1)
    phi = [Fraction(0)] * (limit + 1)
    phi[2] = Fraction(s2, 2)
    for j in range(2, 6):
        phi[2 * j] = c[j] / ((2 * j - 1) * (2 * j))
    delta = [(w.power(n) + Quad(-2)).scale(a) for n, a in enumerate(phi)]
    coefficients = [Quad(1)] + [Quad()] * limit
    for n in range(1, limit + 1):
        total = Quad()
        for j in range(1, n + 1):
            total += (delta[j] * coefficients[n - j]).scale(j)
        coefficients[n] = total.scale(Fraction(1, n))
    return coefficients


def main():
    h = from_log()
    assert h == from_wp()
    assert all(v5(c) >= 0 for c in h[1:25] if c)
    assert v5(h[25]) == -1 and residue(5 * h[25]) == 2
    for a in range(5):
        for b in range(5):
            if (a, b) != (0, 0):
                u = Quad(a, b)
                assert (u + u.power(25)).residues() == u.scale(2).residues()
                assert u.scale(2).residues() != (0, 0)

    # The signed logarithm removes the same denominator at every degree here.
    corrected = from_wp(149, sign=-1)
    assert all(v5(a) >= 0 for a in corrected if a)
    for prime in (5, 17, 19, 31, 41):
        assert all(log_coeff(n).denominator % prime for n in range(prime, prime**2, prime))
        first = prime * log_coeff(prime**2)
        assert first.numerator * pow(first.denominator, -1, prime) % prime == prime - 1

    for s2 in range(5):
        series = norm_defect_through_ten(s2)
        assert all(v5(c) >= 0 for z in series[:10] for c in (z.a, z.b) if c)
        fifth = series[10].scale(5)
        factor = (Quad(0, 1).power(10) + Quad(-2)).scale(
            Fraction(49, 33) - Fraction(s2, 2)**5
        )
        assert fifth.residues() == factor.residues()
        assert (fifth.residues() == (0, 0)) == (s2 == 1)

    assert factorial(4) % 5 == 4
    print("The two formal-parameter computations agree through degree 25.")
    print("At all 24 residual units the degree-25 coefficient has valuation -1.")
    print("The corrected coordinate is 5-integral through degree 149; five inert primes match the Frobenius sign.")
    print("Exactly the quadratic correction s2 = 1 modulo 5 passes degree 10.")


if __name__ == "__main__":
    main()
