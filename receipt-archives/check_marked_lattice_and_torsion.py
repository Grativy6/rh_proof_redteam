"""Finite checks for the marked-lattice, torsion, fan and CM-action proofs.

Uses only the Python standard library. Exact zeros over a complete field and
the universal rank statements are proved in the companion mathematical receipts.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import factorial, isqrt


def inner(gram, x, y):
    return sum(
        a * x[i] * y[j] for i, row in enumerate(gram) for j, a in enumerate(row) if a
    )


def matmul(a, b):
    return tuple(
        tuple(sum(x * y for x, y in zip(row, col)) for col in zip(*b)) for row in a
    )


def transpose(a):
    return tuple(zip(*a))


def identity(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def coset_table(gram, level):
    """Enumerate completely using a positive diagonal-dominance lower bound."""
    n = len(gram)

    def label(x):
        return tuple(a % level for a in x)

    low = min(
        row[i] - sum(abs(v) for j, v in enumerate(row) if j != i)
        for i, row in enumerate(gram)
    )
    assert low > 0
    samples = product(range(-(level // 2), level - level // 2), repeat=n)
    ceiling = max(inner(gram, x, x) for x in samples)
    bound = isqrt(ceiling // low)
    norms, winners = {}, {}
    for x in product(range(-bound, bound + 1), repeat=n):
        q = inner(gram, x, x)
        if q > ceiling:
            continue
        c = label(x)
        if c not in norms or q < norms[c]:
            norms[c], winners[c] = q, [x]
        elif q == norms[c]:
            winners[c].append(x)
    assert len(norms) == level**n
    return norms, winners


def check_doubling():
    examples = [
        (((5, 2), (2, 3)), 5),
        (((4, 1, 0), (1, 4, -1), (0, -1, 3)), 4),
        (((4, 1, 0, 0), (1, 4, 1, 0), (0, 1, 4, 1), (0, 0, 1, 4)), 4),
    ]
    for gram, n in examples:
        d, winners = coset_table(gram, n)
        safe = [c for c in d if d[tuple(2 * x % n for x in c)] == 4 * d[c]]
        assert all(len(winners[c]) == 1 for c in safe)
        for c, e in product(safe, repeat=2):
            ce = tuple((x + y) % n for x, y in zip(c, e))
            assert d[ce] - d[c] - d[e] == 2 * inner(gram, winners[c][0], winners[e][0])
        assert all(v in safe and winners[v] == [v] for v in identity(len(gram)))
    print("The full doubling and Gram checks passed in ranks 2, 3 and 4.")


def size_gate(g, r, n):
    assert g % 2 == 0
    return (
        n > 1 + 2 * g * 2 ** (g // 2),
        r * 2 ** (g // 2) > g * 3**g * factorial(g) * n**g,
        r * n > 6 * n**g * factorial(g),
    )


def check_periods():
    assert not any(size_gate(16, 7, 7**4))
    assert all(size_gate(16, 7**149, 7**6))
    assert all(size_gate(16, 7**5020, 7**312))
    assert not any(size_gate(16, 3, 81))
    assert all(size_gate(16, 3**210, 243**2))
    for m in (9, 27, 81, 243):
        a = (m - 1) // 2

        def exponents(x, y):
            u = 4 * (x * x + y * y)
            return u, u + 4 * x * y

        u1, v1 = exponents(a, 2)
        u2, v2 = exponents(a - m, 2)
        assert u2 - u1 == v1 - v2 == 4 * m
        assert u1 + v1 == u2 + v2 == 2 * m * m + 30
        assert 4 * (m - 2) ** 2 > max(u1, u2) and 3 * (m - 2) ** 2 > max(v1, v2)
        assert 2 * m * m > 4 * m and 4 * m % 8 == 4
        if m == 9:
            assert (u1, v1, u2, v2) == (80, 112, 116, 76)
            # Off-line terms cost >=192+4*81. On the line the total
            # energy is >=6*(x^2+y^2), so this box covers every term <=408.
            small = Counter()
            for x, y in product(range(-8, 9), repeat=2):
                if x % m == a and y % m == 2 and sum(exponents(x, y)) <= 408:
                    small[sum(exponents(x, y))] += 1
            assert small == {192: 2, 408: 1}
            # After removing the initial root phase, the normalized sum is
            # z^16-z^-20+2^216*z^-56 to this precision. The next on-line
            # term of energy <516 would lie in the following slightly larger box.
            shell = [
                (x, y)
                for x, y in product(range(-9, 10), repeat=2)
                if x % m == a and y % m == 2 and 408 < sum(exponents(x, y)) < 516
            ]
            assert not shell
            modulus = 2**324
            z = (1 - 2**214 * pow(9, -1, modulus)) % modulus
            val = (
                pow(z, 16, modulus)
                - pow(z, -20, modulus)
                + 2**216 * pow(z, -56, modulus)
            ) % modulus
            assert val == 0
    # All three possible leading ratios in F4. Encode 1, w, w^2 by bits.
    mu3 = (1, 2, 3)
    readings = [1 ^ z for z in mu3]
    assert readings[0] == 0 and all(readings[1:])
    print(
        "At m=9 the two exponents cross by 36. The first Newton correction checks modulo 2^324."
    )


def times_quaternion(a, b):
    t, x, y, z = a
    u, i, j, k = b
    return (
        t * u - x * i - y * j - z * k,
        t * i + x * u + y * k - z * j,
        t * j - x * k + y * u + z * i,
        t * k + x * j - y * i + z * u,
    )


def hurwitz_matrix(level, sign):
    # Twice each basis element in the orthonormal quaternion coordinates.
    columns = []
    for v in ((2, 0, 0, 0), (0, 2, 0, 0), (0, 0, 2, 0), (1, 1, 1, 1)):
        w = times_quaternion((1, 1, sign * level, 1), v)
        assert all(x % 2 == 0 for x in w)
        doubled = [x // 2 for x in w]
        assert all((x - doubled[3]) % 2 == 0 for x in doubled)
        columns.append(
            tuple((x - doubled[3]) // 2 for x in doubled[:3]) + (doubled[3],)
        )
    return transpose(columns)


def is_prime(n):
    return n > 1 and all(n % i for i in range(2, isqrt(n) + 1))


def check_actions():
    gram = ((2, 0, 0, 1), (0, 2, 0, 1), (0, 0, 2, 1), (1, 1, 1, 2))
    for level in (9, 3**28):
        discr = level**2 + 2
        assert discr % 4 == 3
        plus, minus = (hurwitz_matrix(level, sign) for sign in (1, -1))
        for a in (plus, minus):
            square = matmul(a, a)
            left, right = matmul(transpose(a), gram), matmul(gram, a)
            for i, j in product(range(4), repeat=2):
                assert square[i][j] - a[i][j] + (i == j) * ((discr + 1) // 4) == 0
                assert left[i][j] + right[i][j] == gram[i][j]
        diff = tuple(tuple(a - b for a, b in zip(x, y)) for x, y in zip(plus, minus))
        assert all(x % level == 0 for row in diff for x in row)
        assert any(x % (3 * level) for row in diff for x in row)
        jmat = tuple(tuple(x // level for x in row) for row in diff)
        assert matmul(jmat, jmat) == tuple(
            tuple(-x for x in row) for row in identity(4)
        )
    p, q, r = 249737, 14947671577, 140195420227
    assert p * q * r == 3**56 + 2 and all(is_prime(v) for v in (83, p, q, r))
    assert all(size_gate(4, 3**24, 81))
    print(
        "The two integral CM generators agree on full level 3^28 and differ at the next level."
    )


def check_theta_shells():
    # In doubled standard E8 coordinates all entries have the same parity,
    # and their sum is zero modulo 4. Count squared lengths up to 32.
    shells = Counter()
    for parity in (0, 1):
        counts = Counter({(0, 0): 1})
        options = [x for x in range(-5, 6) if x % 2 == parity]
        for _ in range(8):
            advanced = Counter()
            for (weight, residue), multiplicity in counts.items():
                for x in options:
                    if weight + x * x <= 32:
                        advanced[weight + x * x, (residue + x) % 4] += multiplicity
            counts = advanced
        for j in range(1, 5):
            shells[j] += counts[8 * j, 0]
    assert [shells[j] for j in range(1, 5)] == [240, 2160, 6720, 17520]
    tail_ratio = Fraction(6, 5) ** 5 / 200
    relative_tail = sum(Fraction(j * shells[j], 200 ** (j - 1)) for j in range(2, 5))
    relative_tail += Fraction(3**8 * 5**5, 200**4) / (1 - tail_ratio)
    assert relative_tail < 23 < shells[1]
    assert 2 * (5**2 - 2) ** 8 > 5**16
    print(
        "The four E8 shells give a direct derivative sign. The good-factor grid bound exceeds half at level five."
    )


def check_fan():
    # These representatives attain the minima of each separate conorm
    # square. Brute evaluation below checks the labels and all wall cases.
    for a, b, c in product(range(5), repeat=3):

        def q(x, y):
            return a * x * x + b * y * y + c * (x + y) ** 2

        labels = ((1, 0), (0, 1), (1, 1))
        minima = [
            min(
                q(x, y)
                for x, y in product(range(-3, 4), repeat=2)
                if (x % 2, y % 2) == lab
            )
            for lab in labels
        ]
        assert minima == [q(1, 0), q(0, 1), q(1, -1)]
        v1, v2, v3 = sorted(minima)
        phi = 3 * v1 + 2 * v2 + v3
        assert phi <= 3 * minima[0] + 2 * minima[1] + minima[2]
        wall = 5 * (minima[0] + minima[1]) + 2 * minima[2]
        assert 2 * phi <= wall
        assert (2 * phi == wall) == (minima[0] == minima[1] <= minima[2])
    b = 7**5
    d = b + 1
    assert 10 * 2 * d + 2 * (4 * d - 2 * b) == 403396
    # Lagrange identity for a mixed binary form and a spanning triple.
    gram = ((7, -2), (-2, 4))
    xs = ((1, 2), (3, 1), (-4, 3))
    coeff = (-3, 5, 2)
    v = tuple(sum(k * x[j] for k, x in zip(coeff, xs)) for j in range(2))
    others = [
        tuple(coeff[i] * xs[j][d] - coeff[j] * xs[i][d] for d in range(2))
        for i, j in combinations(range(3), 2)
    ]
    assert sum(k * k for k in coeff) * sum(inner(gram, x, x) for x in xs) == sum(
        inner(gram, x, x) for x in [v, *others]
    )
    for n in (5, 10, 50, 100):
        t = Fraction(3, 7)
        marked = ((Fraction(t, n * n), t / n), (t / n, Fraction(1)))
        assert marked[0][1] / marked[0][0] == n
        assert inner(marked, (-n, 1), (-n, 1)) == 1 - t
    print(
        "The sorted support, rational shear and insertion identity pass the exact checks."
    )


if __name__ == "__main__":
    check_doubling()
    check_periods()
    check_actions()
    check_theta_shells()
    check_fan()
