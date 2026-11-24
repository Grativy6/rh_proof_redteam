"""Exact local elementary divisors in cyclic good/bad Fourier blocks."""

from itertools import combinations, permutations, product
from math import comb


class CyclotomicRing:
    """Integer power basis of a prime-power cyclotomic ring."""

    def __init__(self, p, a):
        self.p = p
        self.order = p ** a
        self.stride = self.order // p
        self.degree = self.order - self.stride
        self.zero = (0,) * self.degree
        self.one = (1,) + self.zero[1:]

    def reduce(self, coefficients):
        cycle = [0] * self.order
        for j, coefficient in enumerate(coefficients):
            cycle[j % self.order] += coefficient
        # One cyclotomic relation for each residue modulo the stride.
        return tuple(cycle[j] - cycle[self.degree + j % self.stride]
                     for j in range(self.degree))

    def root(self, power):
        return self.reduce([0] * (power % self.order) + [1])

    def mul(self, x, y):
        raw = [0] * (2 * self.degree - 1)
        for i, a in enumerate(x):
            if a:
                for j, b in enumerate(y):
                    raw[i + j] += a * b
        return self.reduce(raw)

    def valuation(self, x):
        # Substitute zeta = 1 + pi. The valuation of the i-th nonzero
        # term is i mod degree, so the minimum cannot cancel.
        vals = []
        for i in range(self.degree):
            c = sum(comb(j, i) * x[j] for j in range(i, self.degree))
            if c:
                vals.append(i + self.degree * valuation_int(c, self.p))
        return min(vals) if vals else None


def add(x, y):
    return tuple(a + b for a, b in zip(x, y))


def neg(x):
    return tuple(-a for a in x)


def valuation_int(n, p):
    assert n != 0
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def root_product(ring, indices):
    coefficients = [ring.one]
    for j in indices:
        minus_root = neg(ring.root(j))
        new = [ring.zero] * (len(coefficients) + 1)
        for i, a in enumerate(coefficients):
            new[i] = add(new[i], ring.mul(a, minus_root))
            new[i + 1] = add(new[i + 1], a)
        coefficients = new
    return coefficients


def remainder(ring, polynomial, monic):
    raw = list(polynomial)
    assert monic[-1] == ring.one
    while len(raw) >= len(monic):
        offset, lead = len(raw) - len(monic), raw[-1]
        for i, a in enumerate(monic):
            raw[offset + i] = add(raw[offset + i], neg(ring.mul(lead, a)))
        assert raw.pop() == ring.zero
    return raw


def determinant(ring, matrix):
    result = ring.zero
    for perm in permutations(range(len(matrix))):
        inversions = sum(a > b for a, b in combinations(perm, 2))
        term = ring.one
        for row, col in enumerate(perm):
            term = ring.mul(term, matrix[row][col])
        result = add(result, neg(term) if inversions % 2 else term)
    return result


def elementary_divisors(p, a, bad):
    ring = CyclotomicRing(p, a)
    good = sorted(set(range(ring.order)) - set(bad))
    fg, fb = root_product(ring, good), root_product(ring, bad)
    b = len(bad)
    columns = [remainder(ring, [ring.zero] * j + fg, fb) for j in range(b)]
    matrix = list(zip(*columns))
    minor_vals = [0]
    for size in range(1, b + 1):
        vals = []
        for rows in combinations(range(b), size):
            for cols in combinations(range(b), size):
                minor = [[matrix[i][j] for j in cols] for i in rows]
                val = ring.valuation(determinant(ring, minor))
                if val is not None:
                    vals.append(val)
        minor_vals.append(min(vals))
    exps = [y - x for x, y in zip(minor_vals, minor_vals[1:])]
    assert exps == sorted(exps) and exps[-1] == a * ring.degree
    assert sum(exps) == sum(p ** valuation_int(j - i, p) for i in bad for j in good)
    return exps


def tensor_control():
    indices = list(product(range(5), repeat=2))
    in_good = {pair for pair in indices if min(pair) >= 2}
    in_bad = {pair for pair in indices if max(pair) >= 3}
    assert (len(in_good), len(in_bad), len(in_good & in_bad)) == (9, 16, 8)
    one = [0, *elementary_divisors(5, 1, (0, 1))]
    two = sorted(a + b for a, b in product(one, repeat=2))
    assert two == [0, 2, 2, 4, 4, 4, 6, 6, 8]
    assert sum(x > 0 for x in two) == len(in_good & in_bad) and sum(two) == 36
    print("Two order-5 coordinates: intersection dimension 8, total uniformizer length 36.")


if __name__ == "__main__":
    cases = [
        (5, 1, (0, 1), [2, 4]),
        (7, 1, (0, 1, 2), [2, 4, 6]),
        (7, 1, (0, 1, 3), [3, 3, 6]),
        (5, 2, (0, 5, 10), [20, 30, 40]),
    ]
    for p, a, bad, expected in cases:
        actual = elementary_divisors(p, a, bad)
        assert actual == expected, (p, a, bad, actual)
        print(f"Order {p ** a}, bad exponents {bad}: {actual}")
    tensor_control()
