"""Exact checks for the determinant plane pairing. Uses only the Python standard library."""

from collections import Counter
from itertools import permutations
from math import comb, factorial, prod


def first_weight(p, depth, digit, modulus):
    """Compute binom(p^depth + digit, digit) modulo modulus (a power of p)."""
    power = p**depth
    assert 0 <= digit < power
    # Terms divisible by p reproduce the preceding block. The rest have a
    # unit denominator, so the whole computation uses exact modular integers.
    if not digit:
        return 1
    result = first_weight(p, depth - 1, digit // p, modulus)
    numer, denom = 1, 1
    for j in range(1, digit + 1):
        if j % p:
            numer = numer * (power + j) % modulus
            denom = denom * j % modulus
    return result * numer * pow(denom, -1, modulus) % modulus


def digits_for_sum(p, precision):
    digits = [0] * p
    for h in range(1, precision):
        modulus = p**(h+1)
        current = [first_weight(p, h-1, a, modulus) for a in digits]
        assert sum(current) % (p**h) == 0
        ones = -(sum(current) // p**h) % p
        digits = [p*a + int(i < ones) for i, a in enumerate(digits)]
        after = [first_weight(p, h, a, modulus) for a in digits]
        assert all((new-old) % modulus == (int(i < ones)*p**h) % modulus
                   for i, (new, old) in enumerate(zip(after, current)))
        assert sum(after) % modulus == 0
    return digits


def check_digits(p, precision):
    digits = digits_for_sum(p, precision)
    degree = p**(precision-1)
    modulus = p**precision
    weights = [first_weight(p, precision-1, a, modulus) for a in digits]
    assert all(u % p == 1 for u in weights)
    assert factorial(p-1) * sum(weights) % modulus == 0
    assert factorial(p-1) * weights[0] % p != 0
    if degree < 10000:
        assert weights == [comb(degree+a, a) % modulus for a in digits]
    print(f'p={p}, depth={precision-1}, digits={digits}, sum=0 modulo {modulus}; '
          f'cofactor pairing is a unit.')


def check_small_norm(r, exponent):
    entries = []
    for perm in permutations(range(r)):
        sign = (-1)**sum(i > j for a, i in enumerate(perm) for j in perm[a+1:])
        entries.append((tuple(i*r + value for i, value in enumerate(perm)), sign))
    polynomial = {(): 1}
    for _ in range(exponent):
        out = Counter()
        for word, coefficient in polynomial.items():
            for term, sign in entries:
                out[tuple(sorted(word + term))] += coefficient * sign
        polynomial = {word: c for word, c in out.items() if c}
    norm = sum(c*c * prod(factorial(n) for n in Counter(word).values())
               for word, c in polynomial.items())
    expected = prod(factorial(exponent+j)//factorial(j) for j in range(r))
    assert norm == expected
    return norm


def main():
    check_digits(5, 7)
    check_digits(17, 4)
    for r, b in [(2, 4), (3, 3), (5, 1)]:
        print(f'Fock norm square r={r}, b={b}: {check_small_norm(r, b)}')
    p, h = 17, 8
    b = p**h
    budget_bound = p*p*((p+1)*(h+3) + 3*(h+7))
    c = 4*budget_bound + 1
    assert budget_bound == 70227 and c == 280909
    assert b + 1 - 60*c > 0
    assert all(comb(b+j, j) % p for j in range(p))
    print(f'Positive link cutoff at p={p}, b={b}: {b+1-60*c}; '
          f'additional valuation budget at most {budget_bound}.')


if __name__ == '__main__':
    main()
