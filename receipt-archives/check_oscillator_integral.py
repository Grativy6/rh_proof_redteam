"""Compare two exact formulas for the rank-one oscillator coefficient."""

from fractions import Fraction
from math import comb, factorial


def beta_monomial(power, exponent):
    """Integral of x**power * (1-x)**exponent from zero to one."""
    return Fraction(factorial(power) * factorial(exponent),
                    factorial(power + exponent + 1))


def from_oscillator(weight, depth):
    """Polynomial after removing sech(t)**weight, in x = tanh(t)**2."""
    coeffs = [0] * (depth + 1)
    for h in range(depth + 1):
        factor = (-1) ** h * comb(depth, h) * comb(weight + depth - 1, h)
        for power in range(depth - h + 1):
            coeffs[h + power] += factor * (-1) ** power * comb(depth - h, power)
    return coeffs


def from_disk(weight, depth):
    """Coefficient of z**depth in (z+u)**depth/(1+uz)**(weight+depth)."""
    return [
        (-1) ** h * comb(depth, h) * comb(weight + depth + h - 1, h)
        for h in range(depth + 1)
    ]


def check():
    total = 0
    for modes in range(2, 13):
        for degree in range(13):
            for depth in range(degree // 2 + 1):
                weight = modes + degree - 2 * depth
                polynomial = from_oscillator(weight, depth)
                if polynomial != from_disk(weight, depth):
                    raise ValueError(f"Coefficient mismatch at {(modes, degree, depth)}")
                exponent = weight + depth - 2
                integral = sum(coef * beta_monomial(h, exponent)
                               for h, coef in enumerate(polynomial))
                expected = 0 if depth else Fraction(1, modes + degree - 1)
                if integral != expected:
                    raise ValueError(f"Integral mismatch at {(modes, degree, depth)}")
                total += 1
    print(f"Two polynomial formulas and their exact integrals agree in {total} cases.")
    print("For two modes in degree two, the trace has integral 0 and the harmonic part has factor 1/3.")


if __name__ == "__main__":
    check()
