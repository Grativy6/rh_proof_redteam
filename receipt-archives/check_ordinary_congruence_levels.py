"""Direct coset actions for the actual positive ordinary Hecke operators."""

from collections import Counter
from itertools import combinations, permutations, product


def multiply(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def depth(c, d, p, m):
    while c % p == d % p == 0:
        c, d = c // p, d // p
    if not c:
        return m
    s = 0
    while s < m and c % p == 0:
        c //= p
        s += 1
    return s


def rank_two(p, m):
    size = p**m
    # Primitive rows modulo p^m, up to unit scaling.
    reps = [(c, 1) for c in range(size)] + [(1, d) for d in range(0, size, p)]
    action = [None] * (m + 1)
    for c, d in reps:
        s = depth(c, d, p, m)
        counts = Counter(depth(p*c, r*c + d, p, m) for r in range(p))
        row = [counts[j] for j in range(m + 1)]
        if action[s] is not None:
            assert action[s] == row
        action[s] = row
    expected = [[0] * (m+1) for _ in range(m+1)]
    expected[0][:2] = [1, p-1]
    for s in range(1, m+1):
        expected[s][min(s+1, m)] = p
    assert action == expected

    differences = [[int(j == i) - int(j == i+1) for j in range(m+1)] for i in range(m)]
    reading = [sum(p**i * differences[i][j] for i in range(m)) for j in range(m+1)]
    change = [reading, *differences[1:], [0]*m + [1]]
    blocks = [[0] * (m+1) for _ in range(m+1)]
    blocks[0][0], blocks[m][m] = 1, p
    for i in range(1, m-1):
        blocks[i][i+1] = p
    assert multiply(change, action) == multiply(blocks, change)

    ordinary = [[int(i == j == 0) for j in range(m+1)] for i in range(m+1)]
    power = identity(m+1)
    for k in range(m+4):
        for r in range(1, m+4):
            matches = all((power[i][j]-ordinary[i][j]) % (p**r) == 0
                          for i in range(m+1) for j in range(m+1))
            assert matches == (k >= r)
            quotient_matches = all((power[i][j]-ordinary[i][j]) % (p**r) == 0
                                   for i in range(m) for j in range(m))
            assert quotient_matches == (k >= min(r, m-1))
        power = multiply(power, blocks)
    return len(reps)


ORDERS = list(permutations(range(3)))
PAIRS = list(combinations(range(3), 2))


def primitive_reduction(vector, p):
    assert any(vector)
    while all(x % p == 0 for x in vector):
        vector = [x // p for x in vector]
    return [x % p for x in vector]


def flag_cell(bottom, middle, p):
    line = primitive_reduction(bottom, p)
    wedge = primitive_reduction([bottom[i]*middle[j] - bottom[j]*middle[i] for i, j in PAIRS], p)
    a = next(i for i, value in enumerate(line) if value)
    plane = next(pair for pair, value in zip(PAIRS, wedge) if value)
    assert a in plane
    b = next(i for i in plane if i != a)
    return (a, b, 3-a-b)


def flag_operator(j, p):
    rows = []
    for order in ORDERS:
        row = [0] * 6
        for r, s in product(range(p), repeat=2):
            if j == 1:
                g = [[p, r, s], [0, 1, 0], [0, 0, 1]]
            else:
                g = [[p, 0, r], [0, p, s], [0, 0, 1]]
            cell = flag_cell(g[order[0]], g[order[1]], p)
            row[ORDERS.index(cell)] += 1
        rows.append(row)
    return rows


def rank_three(p):
    u, v = flag_operator(1, p), flag_operator(2, p)
    assert multiply(u, v) == multiply(v, u)
    assert all(op[i][j] == 0 for op in (u, v) for i in range(6) for j in range(i))
    observed = [(u[i][i], v[i][i]) for i in range(6)]
    assert observed == [(1, 1), (1, p), (p, 1), (p*p, p), (p, p*p), (p*p, p*p)]
    # In the Steinberg quotient, the sign row kills each partial-flag pullback.
    sign = [(-1)**sum(order[i] > order[j] for i, j in PAIRS) for order in ORDERS]
    assert multiply([sign], u) == multiply([sign], v) == [sign]
    for op in (u, v):
        assert [row[0] for row in op] == [1, 0, 0, 0, 0, 0]
    print(f"GL3 over residue size {p}: {observed}. Ordinary and Steinberg both read (1,1).")


def inversion_test():
    for n in range(2, 8):
        slopes = [i*i+i for i in range(n)]
        for order in permutations(range(n)):
            delta = sum(sum(slopes[order[i]]-slopes[i] for i in range(j)) for j in range(1, n))
            inv = sum(slopes[order[i]]-slopes[order[j]] for i, j in combinations(range(n), 2)
                      if order[i] > order[j])
            assert delta == inv
            assert bool(delta) == (tuple(range(n)) != order)


def rank_three_kummer():
    # R(s,c) is Sym^2 of the Kummer extension, twisted by s^-1.
    def representation(s, c, modulus):
        inv = pow(s, -1, modulus)
        return [[s % modulus, c % modulus, c*c*inv % modulus],
                [0, 1, 2*c*inv % modulus], [0, 0, inv]]

    for a in range(1, 9):
        size = 11**(a+2)
        for s, t in ((1, 2), (2, 3), (12, 13)):
            for c, d in ((11**a, 3*11**a), (-2*11**a, 11**a)):
                left = multiply(representation(s, c, size), representation(t, d, size))
                assert [[x % size for x in row] for row in left] == representation(s*t, c+s*d, size)
                assert representation(s, c, 11**a) == representation(s, 0, 11**a)
    n = [[0, 1, 0], [0, 0, 2], [0, 0, 0]]
    frob = [[1, 0, 0], [0, 11, 0], [0, 0, 121]]
    assert multiply(n, n) == [[0, 0, 2], [0, 0, 0], [0, 0, 0]]
    assert multiply(n, frob) == [[11*x for x in row] for row in multiply(frob, n)]
    print("Rank-three Kummer matrices: multiplication and reduction, plus the nonzero monodromy square.")


if __name__ == "__main__":
    reps = sum(rank_two(p, m) for p, cap in ((2, 7), (3, 5), (5, 4), (11, 3))
               for m in range(1, cap+1))
    print(f"GL2: checked {reps} primitive row representatives, 19 levels, integral blocks and cutoffs.")
    for prime in (2, 3, 5, 7, 11):
        rank_three(prime)
    inversion_test()
    rank_three_kummer()
    print("Compared prefix sums and weighted inversions for every permutation through rank seven.")
