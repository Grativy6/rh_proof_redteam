"""Exact finite checks for the distinguished-prime projector and inert parameter map."""

from collections import Counter
from itertools import combinations, product
from math import comb, prod


def field_tables(q):
    # The extension field uses the basis 1, x with x^2 = x + 1.
    if q == 4:
        def multiply(a, b):
            raw = (a if b & 1 else 0) ^ ((a << 1) if b & 2 else 0)
            return raw ^ 7 if raw & 4 else raw

        return [[a ^ b for b in range(q)] for a in range(q)], [
            [multiply(a, b) for b in range(q)] for a in range(q)
        ]
    assert q in (2, 3, 5, 7)
    return [[(a + b) % q for b in range(q)] for a in range(q)], [
        [a * b % q for b in range(q)] for a in range(q)
    ]


def smith_diagonal(matrix):
    """Use integral row and column operations. Return positive invariant factors."""
    a = [row[:] for row in matrix]
    rows, cols = len(a), len(a[0])
    factors = []
    for k in range(min(rows, cols)):
        candidates = ((abs(a[i][j]), i, j)
                      for i in range(k, rows) for j in range(k, cols) if a[i][j])
        pivot = min(candidates, default=None)
        if pivot is None:
            break
        _, i, j = pivot
        a[i], a[k] = a[k], a[i]
        for row in a:
            row[j], row[k] = row[k], row[j]
        while True:
            i = next((i for i in range(k + 1, rows) if a[i][k]), None)
            if i is not None:
                quotient = a[i][k] // a[k][k]
                a[i] = [v - quotient * w for v, w in zip(a[i], a[k])]
                if a[i][k]:
                    a[k], a[i] = a[i], a[k]
                continue
            j = next((j for j in range(k + 1, cols) if a[k][j]), None)
            if j is not None:
                quotient = a[k][j] // a[k][k]
                for row in a:
                    row[j] -= quotient * row[k]
                if a[k][j]:
                    for row in a:
                        row[j], row[k] = row[k], row[j]
                continue
            i = next((i for i in range(k + 1, rows)
                      if any(x % a[k][k] for x in a[i][k + 1:])), None)
            if i is None:
                break
            a[k] = [v + w for v, w in zip(a[k], a[i])]
        factors.append(abs(a[k][k]))
    assert all(b % a == 0 for a, b in zip(factors, factors[1:]))
    return factors


def check_group(n, q):
    add, mul = field_tables(q)
    positions = list(combinations(range(n), 2))
    index = {pair: k for k, pair in enumerate(positions)}
    middle = [[(index[i, k], index[k, j]) for k in range(i + 1, j)]
              for i, j in positions]
    simple = [index[i, i + 1] for i in range(n - 1)]
    elements = list(product(range(q), repeat=len(positions)))
    indices = {g: i for i, g in enumerate(elements)}
    coeff = [prod(q - 1 if g[i] == 0 else -1 for i in simple) for g in elements]
    size = len(elements)
    square = [0] * size
    columns = []
    for right, b in enumerate(elements):
        column = [0] * size
        for left, a in enumerate(elements):
            ab = [add[x][y] for x, y in zip(a, b)]
            for k, terms in enumerate(middle):
                for i, j in terms:
                    ab[k] = add[ab[k]][mul[a[i]][b[j]]]
            target = indices[tuple(ab)]
            column[target] = coeff[left]
            square[target] += coeff[left] * coeff[right]
        columns.append(tuple(column))
    assert square == [size * c for c in coeff]
    # Subtracting a duplicate column or row is an integral change of basis.
    columns = list(dict.fromkeys(columns))
    rows = list(dict.fromkeys(zip(*columns)))
    observed = Counter(smith_diagonal([list(row) for row in rows]))
    d = n - 1
    expected = Counter({q**s: comb(d, s) * (q - 2)**s for s in range(d + 1)})
    assert observed == +expected
    assert sum(observed.values()) == (q - 1)**d
    print(f"UT({n},{q}): size {size}, Smith factors {dict(sorted(observed.items()))}")


def flag_trace(q):
    """Count fixed points, lines and incident flags of each actual 3-by-3 matrix."""
    points = [p for p in product(range(q), repeat=3) if next((x for x in p if x), 0) == 1]
    incidence = {(p, line) for p in points for line in points
                 if sum(x * y for x, y in zip(p, line)) % q == 0}
    weighted = [0] * 4
    for a, b, c in product(range(q), repeat=3):
        # Upper rows are (1,a,c), (0,1,b), (0,0,1). Every eigenvalue is 1.
        pts = [p for p in points if (a * p[1] + c * p[2]) % q == 0 and b * p[2] % q == 0]
        lns = [line for line in points
               if line[0] * a % q == 0 and (line[0] * c + line[1] * b) % q == 0]
        flags = sum((p, line) in incidence for p in pts for line in lns)
        weight = (q - 1 if a == 0 else -1) * (q - 1 if b == 0 else -1)
        for i, count in enumerate((flags, len(pts), len(lns), 1)):
            weighted[i] += weight * count
    ranks = [divmod(x, q**3) for x in weighted]
    assert ranks == [((q - 1)**2, 0), (0, 0), (0, 0), (0, 0)]
    st_dim = len(incidence) - 2 * len(points) + 1
    assert st_dim == q**3
    print(f"GL(3,{q}): flags {len(incidence)}, Steinberg {st_dim}, each retains {ranks[0][0]}")


def polynomial_product(a, b, modulus):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % modulus
    return out


def check_reconstruction():
    trials = 0
    # Lists here are in descending degree. The same t may occur many times.
    for modulus in (2, 3, 4, 8, 9):
        for m in range(5):
            for t in product(range(modulus), repeat=m):
                paired, elementary = [1], [1]
                for x in t:
                    paired = polynomial_product(paired, [1, -x, 1], modulus)
                    elementary = polynomial_product(elementary, [1, x], modulus)
                for odd in (False, True):
                    full = polynomial_product(paired, [1, -1], modulus) if odd else paired
                    if odd:
                        quotient = [full[0]]
                        for coefficient in full[1:-1]:
                            quotient.append((coefficient + quotient[-1]) % modulus)
                        assert (full[-1] + quotient[-1]) % modulus == 0
                    else:
                        quotient = full
                    recovered = [1]
                    for j in range(1, m + 1):
                        earlier = sum(comb(m - j + 2 * a, a) * recovered[j - 2 * a]
                                      for a in range(1, j // 2 + 1))
                        recovered.append(((-1)**j * quotient[j] - earlier) % modulus)
                    assert recovered == elementary
                    trials += 1
    for p in (2, 3, 5, 7):
        z = 1 + p
        assert z != 1 and (z + pow(z, -1, p*p)) % (p*p) == 2 % (p*p)
    print(f"Reciprocal parameter: {trials} coefficient-ring cases, four marked collisions")


if __name__ == "__main__":
    for rank, q in ((1, 7), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 7), (4, 2)):
        check_group(rank, q)
    for prime in (2, 3, 5, 7):
        flag_trace(prime)
    check_reconstruction()
