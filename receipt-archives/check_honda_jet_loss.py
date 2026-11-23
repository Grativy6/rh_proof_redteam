"""Check the Honda jet valuation by invariant differentiation and series inversion."""

from fractions import Fraction
from math import factorial


def weight_parts(p, excess):
    """Enumerate multiplicities in sum m_j*(p^(2j)-1) = excess."""
    weights = []
    q = p * p
    power = q
    while power - 1 <= excess:
        weights.append(power - 1)
        power *= q

    def visit(j, remaining):
        if j < 0:
            if remaining == 0:
                yield ()
            return
        for count in range(remaining // weights[j] + 1):
            for lower in visit(j - 1, remaining - count * weights[j]):
                yield lower + (count,)

    yield from visit(len(weights) - 1, excess)


def inversion_jet(p, n, k):
    """n! [X^n] g(X)^k from Lagrange inversion."""
    result = Fraction(0)
    for counts in weight_parts(p, n - k):
        count = sum(counts)
        denominator = p**sum(j * m for j, m in enumerate(counts, 1))
        for m in counts:
            denominator *= factorial(m)
        result += Fraction(k * (-1)**count * factorial(n + count - 1), denominator)
    return result


def inv_derivative_rows(p, limit):
    """Row n is (D^n T^k)(0), where D = (1/L'(T))*d/dT."""
    q = p * p
    step = q - 1
    nonconstant = []
    j, power = 1, q
    while power - 1 <= limit:
        nonconstant.append((power - 1, p**j))
        j += 1
        power *= q

    reciprocal = [0] * (limit + 1)
    reciprocal[0] = 1
    for degree in range(step, limit + 1, step):
        reciprocal[degree] = -sum(
            factor * reciprocal[degree - shift]
            for shift, factor in nonconstant if shift <= degree
        )
    previous = [1]
    for n in range(1, limit + 1):
        row = [0] * (n + 1)
        for k in range(n, 0, -step):
            row[k] = k * sum(
                reciprocal[j] * previous[k - 1 + j] for j in range(0, n - k + 1, step)
            )
        yield n, row
        previous = row


def valuation(p, a):
    a = abs(a)
    if a == 0:
        raise ValueError("zero has no finite valuation")
    exponent = 0
    while a % p == 0:
        a //= p
        exponent += 1
    return exponent


def main():
    comparisons = 0
    for p, limit in ((3, 128), (5, 650), (7, 150)):
        q = p * p
        for n, row in inv_derivative_rows(p, limit):
            for k in range(n, 0, -(q - 1)):
                value = row[k]
                if value:
                    assert (q - 1) * (valuation(p, value) + 1) >= p * n
                if n <= 110 or n in (600, 625, 650):
                    assert inversion_jet(p, n, k) == value, (p, n, k)
                    comparisons += 1
            if n == q - 1 or n == q * (q - 1):
                assert valuation(p, row[q - 1]) == p * n // (q - 1) - 1
    assert valuation(5, factorial(24)) == 4
    assert valuation(5, abs(inversion_jet(5, 600, 24).numerator)) == 124
    for p in (3, 5, 7):
        assert all((a**p * b - a * b**p) % p == 0 for a in range(p) for b in range(p))
        assert valuation(p, p - p**p) == 1
    print(f"{comparisons} exact derivative and inverse-series computations agree.")
    print("The lower bound passed throughout. At p=5 the extremal valuations are 4 and 124.")


if __name__ == "__main__":
    main()
