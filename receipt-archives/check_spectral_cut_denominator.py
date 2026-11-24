"""Finite checks for the bad-type rank and Fourier denominator calculation."""

from fractions import Fraction
from math import gcd, isqrt


def is_prime(n):
    return n > 1 and all(n % i for i in range(2, isqrt(n) + 1))


def square_class_weight():
    # Enumerate monic quadratics through their coefficients, counting each
    # split squarefree polynomial once. Its Whittaker weight is 1/(g-1)^2.
    g = 257
    squares = {i * i % g for i in range(1, g)}
    roots = {i * i % g: i for i in range(1, g)}
    inv_two = pow(2, -1, g)
    count = 0
    for linear in range(g):
        for constant in range(g):
            if constant == 0:
                continue
            disc = (linear * linear - 4 * constant) % g
            if disc not in roots:
                continue
            root = roots[disc]
            r1 = (-linear + root) * inv_two % g
            r2 = (-linear - root) * inv_two % g
            if r1 in squares or r2 in squares:
                count += 1
    assert count == 24_512
    weight = Fraction(count, (g - 1) ** 2)
    assert weight == Fraction(383, 1024)
    lower = Fraction(3, 8) - Fraction(3, 8 * g * g) - Fraction(1, g) - Fraction(1, g - 1)
    assert weight >= lower >= Fraction(23, 64)
    print("Squarefree quadratic weight at 257:", weight)


def trim(coeffs):
    result = list(coeffs)
    while result and result[-1] == 0:
        result.pop()
    return result


def remainder_mod(dividend, divisor, p):
    result = trim(c % p for c in dividend)
    divisor = trim(c % p for c in divisor)
    assert divisor
    inv = pow(divisor[-1], -1, p)
    while len(result) >= len(divisor):
        offset = len(result) - len(divisor)
        lead = result[-1] * inv % p
        for j, c in enumerate(divisor):
            result[offset + j] = (result[offset + j] - lead * c) % p
        result = trim(result)
    return result


def coprime_mod(f, h, p):
    a, b = f, h
    while b:
        a, b = b, remainder_mod(a, b, p)
    return len(trim(a)) == 1 and a[0] % p != 0


def check_fourier_mask():
    g = 1013
    h = (g - 1) // 2
    assert is_prime(g) and h == 2 * 11 * 23
    prim = next(a for a in range(2, g) if all(pow(a, (g - 1) // p, g) != 1 for p in (2, 11, 23)))
    roots = [1] + [pow(prim, 253 - 2 * j, g) for j in range(1, 6)]
    assert len(set(roots)) == 6
    bad = set()
    for j in range(h):
        twist = pow(prim, 2 * j, g)
        # Orders with a single prime factor, including the identity.
        if any(any(pow(x * twist % g, k, g) == 1 for k in (4, 11, 23)) for x in roots):
            bad.add(j)
    axes = {j for j in range(h) if any(j * k % h == 0 for k in (2, 11, 23))}
    assert len(axes) == 34
    assert bad == axes | {r + s for r in range(1, 6) for s in (0, 253)}
    good = set(range(h)) - bad
    assert 22 in bad and 68 in good
    change = pow(prim, 2 * (68 - 22), g)
    assert change != 1 and pow(change, 11, g) == 1
    for root in roots:
        before = root * pow(prim, 2 * 22, g) % g
        after = root * pow(prim, 2 * 68, g) % g
        assert pow(before, 11, g) == pow(after, 11, g)
    diagonal = Fraction(len(good), h)
    assert len(bad) == 44 and diagonal == Fraction(21, 23)

    # On an order-23 character, use the exact power basis of Q(zeta_23).
    powers = [sum(j % 23 == i for j in good) for i in range(23)]
    reduced = [x - powers[-1] for x in powers[:-1]]
    assert reduced == [-11] + [-2] * 5 + [0] * 16
    assert coprime_mod([1] * 23, reduced, 11)
    for p in (11, 23):
        prime_to_p = h // p
        counts = [sum((r + j * prime_to_p) in good for j in range(p)) for r in range(prime_to_p)]
        assert any(value % p for value in counts)
    assert Fraction(21, 23) ** 3 == Fraction(9261, 12167)
    assert gcd(11 ** 3, diagonal.denominator) == 1
    print("At 1013 the diagonal coefficient is 21/23.")
    print("An off-diagonal coefficient needs 11 at every place over 11.")
    print("Three independent copies require both 11^3 and 23^3.")


if __name__ == "__main__":
    square_class_weight()
    check_fourier_mask()
