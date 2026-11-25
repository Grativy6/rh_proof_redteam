"""Finite arithmetic for the two component tests and the paired trace calculation."""

from itertools import product


def check_components(p):
    count = 0
    for a, d, b, c in product(range(p), repeat=4):
        g1, g2 = b*b*c % p, (d*b+a*c) % p
        left = a == b == 0
        middle = b == c == 0
        right = c == d == 0
        assert (g1 == g2 == 0) == (left or middle or right)
        # Two choices of a matrix multiplying the column (b,c).
        det1, det2 = a*b*c, -d*b*b
        assert (det1-det2-b*g2) % p == 0
        if left or middle or right:
            assert det1 % p == det2 % p == 0
            count += 1
    assert count == 3*p*p-2*p

    # Both possible ranks of the missing linear constraint on two-by-two matrices.
    for label in ("triangular", "trace zero"):
        total, moving = 0, 0
        for u, v, w in product(range(p), repeat=3):
            a, b, c, d = (u, v, 0, w) if label == "triangular" else (u, v, w, -u)
            if (a*d-b*c) % p:
                continue
            for x, y in product(range(p), repeat=2):
                if (a*x+b*y) % p == (c*x+d*y) % p == 0:
                    total += 1
                    moving += int(x != 0 or y != 0)
        expected = (2*p**3-p, 2*p*p*(p-1)) if label == "triangular" else (p**3+p*p-p, p*(p*p-1))
        assert (total, moving) == expected
    print(f"F_{p}: {count} points in the three-plane union; both matrix hyperplanes checked.")


def jet_product(x, y, p):
    return [sum(x[i]*y[n-i] for i in range(n+1)) % p for n in range(len(x))]


def check_jets():
    for order in (2, 3, 4):
        original = sharp = 0
        for tail in product(range(5), repeat=order-2):
            b = [0, 1, *tail]
            square = jet_product(b, b, 5)
            cube = jet_product(square, b, 5)
            original += int(not any(cube))
            sharp += int(not any(square))
        assert original == (5**(order-2) if order <= 3 else 0)
        assert sharp == (1 if order == 2 else 0)
    print("Same tangent lifts to order two on the uncut ring, only order one on the determinant cut.")


def rank(rows, p):
    pivots = {}
    for raw in rows:
        row = {j: x % p for j, x in raw.items() if x % p}
        while row:
            j = min(row)
            c = row[j]
            if j not in pivots:
                inv = pow(c, -1, p)
                pivots[j] = {k: x * inv % p for k, x in row.items()}
                break
            for k, x in pivots[j].items():
                y = (row.get(k, 0)-c*x) % p
                if y:
                    row[k] = y
                else:
                    row.pop(k, None)
    return len(pivots)


def add(row, index, coefficient):
    row[index] = row.get(index, 0) + coefficient


def trace_kernel(g, p):
    # Basis for (M_2 x F) plus g copies of both off-diagonal blocks, with square-zero radical.
    basis = [(i, j, label) for i, j in product(range(3), repeat=2)
             for label in ((-1,) if (i < 2) == (j < 2) else range(g))]
    index = {x: i for i, x in enumerate(basis)}
    d = len(basis)
    def multiply(i, j):
        a, b, m = basis[i]
        c, e, n = basis[j]
        if b != c or min(m, n) >= 0:
            return None
        return index[a, e, max(m, n)]

    table = [[multiply(i, j) for j in range(d)] for i in range(d)]
    eq = []
    for i, j, k in product(range(d), repeat=3):
        row = {}
        # beta(xy,z) = beta(y,zx) + beta(x,yz).
        for a, b, sign in ((table[i][j], k, 1), (j, table[k][i], -1), (i, table[j][k], -1)):
            if a is not None and b is not None:
                add(row, d*a+b, sign)
        if row:
            eq.append(row)
    unit = [index[i, i, -1] for i in range(3)]
    eq.extend({d*i+j: 1 for j in unit} for i in range(d))
    invisible = d*d-rank(eq, p)

    inner = [{} for _ in range(d)]
    modes = [{} for _ in range(g*g)]
    for i, j in product(range(d), repeat=2):
        if table[j][i] is not None:
            add(inner[table[j][i]], d*i+j, 1)
        if table[i][j] is not None:
            add(inner[table[i][j]], d*i+j, -1)
        a, b, m = basis[i]
        c, h, n = basis[j]
        if a == h and b == c and min(m, n) >= 0:
            if a < 2:
                modes[g*m+n][d*i+j] = 1
            else:
                modes[g*n+m][d*i+j] = -1
    for v in inner+modes:
        assert all(sum(x*v.get(j, 0) for j, x in row.items()) % p == 0 for row in eq)
    base = rank(inner, p)
    assert base == d-2 and rank(inner+modes, p) == invisible == base+g*g
    print(f"F_{p}, g={g}: trace-zero derivations {invisible}, inner {base}, extra {g*g}.")


if __name__ == "__main__":
    for prime in (2, 3, 5, 7, 11):
        check_components(prime)
    check_jets()
    for prime in (3, 11):
        for size in range(4):
            trace_kernel(size, prime)
