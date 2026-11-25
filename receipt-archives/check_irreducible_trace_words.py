"""Rank-three word traces at an absolutely irreducible point, over prime fields."""

from itertools import product


def identity():
    return [[int(i == j) for j in range(3)] for i in range(3)]


def multiply(a, b, p):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) % p for j in range(3)]
            for i in range(3)]


def rank(rows, p):
    pivots = {}
    for row in rows:
        v = row[:]
        for i, pivot in sorted(pivots.items()):
            c = v[i]
            v = [(x - c * y) % p for x, y in zip(v, pivot)]
        i = next((i for i, x in enumerate(v) if x % p), None)
        if i is not None:
            factor = pow(v[i], -1, p)
            pivots[i] = [x * factor % p for x in v]
    return len(pivots)


def evaluate(word, matrices, p):
    value = identity()
    for letter in word:
        value = multiply(value, matrices[letter], p)
    return value


def trace_row(word, matrices, p):
    # For a perturbation D at one letter, cyclicity gives tr(prefix D suffix)
    # = tr(suffix prefix D). Its coefficient on D_ij is (suffix prefix)_ji.
    row = [0] * (9 * len(matrices))
    for position, letter in enumerate(word):
        cyclic = word[position + 1:] + word[:position]
        value = evaluate(cyclic, matrices, p)
        for i, j in product(range(3), repeat=2):
            where = 9 * letter + 3 * i + j
            row[where] = (row[where] + value[j][i]) % p
    return row


def check(p):
    matrices = [identity(), [[1, 0, 0], [0, 2, 0], [0, 0, 4]],
                [[0, 1, 0], [0, 0, 1], [1, 0, 0]]]
    basis = [(1,) * i + (2,) * j for i, j in product(range(3), repeat=2)]
    assert rank([sum(evaluate(b, matrices, p), []) for b in basis], p) == 9
    words = {s + a + b for s in ((), (0,), (1,), (2,)) for a in basis for b in basis}
    rows = [trace_row(word, matrices, p) for word in sorted(words)]
    assert rank(rows, p) == 19

    inner = []
    for i, j in product(range(3), repeat=2):
        unit = [[int((a, b) == (i, j)) for b in range(3)] for a in range(3)]
        direction = []
        for matrix in matrices:
            left, right = multiply(unit, matrix, p), multiply(matrix, unit, p)
            direction.extend((left[a][b] - right[a][b]) % p for a, b in product(range(3), repeat=2))
        inner.append(direction)
        assert all(sum(x * y for x, y in zip(direction, row)) % p == 0 for row in rows)
    assert rank(inner, p) == 8
    for word, change in [((0,), 0), ((0, 0, 0), 0), ((0, 1), -1)]:
        row = trace_row(word, matrices, p)
        assert (row[0] - row[4] - change) % p == 0
    print(f"F_{p}: {len(words)} distinct words, maximum length {max(map(len, words))}, "
          "27 generator directions, trace rank 19, conjugacy kernel 8")


if __name__ == "__main__":
    for prime in (5, 7, 11):
        check(prime)
