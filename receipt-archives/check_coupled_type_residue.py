"""Exact controls for the paired type-prime selector and its Fourier return."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import factorial


def sym_index(k, half, i):
    if i < k:
        return i + half
    if i < k + half:
        return i - k
    return i


def det_mod(rows, p):
    mat = [row.copy() for row in rows]
    result = 1
    for j in range(len(mat)):
        pivot = next((i for i in range(j, len(mat)) if mat[i][j] % p), None)
        if pivot is None:
            return 0
        if pivot != j:
            mat[j], mat[pivot] = mat[pivot], mat[j]
            result = -result
        d = mat[j][j] % p
        result = result * d % p
        inverse = pow(d, -1, p)
        for i in range(j + 1, len(mat)):
            scale = mat[i][j] * inverse % p
            if scale:
                for l in range(j, len(mat)):
                    mat[i][l] = (mat[i][l] - scale * mat[j][l]) % p
    return result % p


def sharp_value(rows, k, m, t, p):
    """Return the additive exponent on these test inputs, or None for zero.

    Coordinates are already integral in the scaled flag bases. The chosen
    accepted matrices have all determinant character arguments equal to one.
    """
    r = k + m - 1
    half = m // 2 - 1
    a = r + (m - 2) * t
    assert len(rows) >= a and all(len(row) == a for row in rows)
    if any(any(v % p for v in row) for row in rows[a:]):
        return None
    for j in range(r):
        if rows[j][j] % p != 1:
            return None
        for i in range(a):
            forbidden = (i >= r or sym_index(k, half, j) < sym_index(k, half, i)
                         or (j == k + half and i < k))
            if i != j and forbidden and rows[i][j] % p:
                return None
    for j in range(r, a):
        if any(rows[i][j] % p for i in range(r, a)
               if (j - r) // t < (i - r) // t):
            return None
    det = det_mod(rows[:a], p)
    if det == 0:
        return None
    assert det == 1
    for start in range(r, a, t):
        assert det_mod([row[start:start+t] for row in rows[start:start+t]], p) == 1
    exponent = sum(rows[i][i+1] for i in range(k-1))
    exponent += sum(rows[i][i+1] for i in range(k, r-1))
    return exponent % p


def varied_column(k, m, t, j, u):
    r = k + m - 1
    a = r + (m - 2) * t
    n = a + t
    assert len(u) == n
    return [[u[i] if col == j else int(i == col) for col in range(a)] for i in range(n)]


def test_charts(k, m, t, p):
    r = k + m - 1
    half = m // 2 - 1
    a = r + (m - 2) * t
    n = a + t
    j = k - 1
    free = [i for i in range(r) if sym_index(k, half, i) < sym_index(k, half, j)]
    assert len(free) == k - 1 + half and k - 2 in free
    identity = []
    moved = []
    for small in product(range(p), repeat=r):
        u = list(small) + [0] * (n - r)
        fi = sharp_value(varied_column(k, m, t, k, u), k, m, t, p)
        fm = sharp_value(varied_column(k, m, t, j, u), k, m, t, p)
        if fi is not None:
            identity.append(u)
        allowed = all(u[i] == int(i == j) for i in range(n) if i not in free)
        assert (fm is not None) == allowed
        if fm is not None:
            assert fm == u[k - 2]
            moved.append((u, fm))
    assert identity == [[int(i == k) for i in range(n)]]
    assert len(moved) == p ** len(free)
    # Fixed destination row of the second selector. Character product is
    # zeta^(fm-eta(u)). Check every covector restricted to the free space.
    eta_at_j = 2 % p
    for on_free in product(range(p), repeat=len(free)):
        counts = Counter((phase - eta_at_j*u[j] -
                          sum(h*u[i] for h, i in zip(on_free, free))) % p
                         for u, phase in moved)
        matched = tuple(on_free) == tuple(int(i == k-2) for i in free)
        if matched:
            assert counts == {(-eta_at_j) % p: len(moved)}
        else:
            assert counts == dict.fromkeys(range(p), len(moved) // p)
    # The tail divisibility test sees a coordinate outside the leading minor.
    bad = identity[0].copy()
    bad[a] = 1
    assert sharp_value(varied_column(k, m, t, k, bad), k, m, t, p) is None
    print(f"q={p}, k={k}, m={m}: identity fiber 1, swapped fiber {len(moved)}, only the matching frequency survives.")


def large_rank_control():
    k, m, t, p = 8, 4, 17, 11
    a = k + m - 1 + (m - 2) * t
    n = a + t
    assert a == k + (m-2) * (t+1) + 1 and n == k + (m-1) * (t+1)
    for j in (k, k-1):
        u = [int(i == j) for i in range(n)]
        assert sharp_value(varied_column(k, m, t, j, u), k, m, t, p) == 0
        u[k-2] = 1
        expected = None if j == k else 1
        assert sharp_value(varied_column(k, m, t, j, u), k, m, t, p) == expected
    # D swap D^-1 in ordinary coordinates has a denominator, but its
    # columns form a basis of Z_p plus p*Z_p in normalized coordinates.
    raw_swap = ((0, Fraction(1, p)), (p, 0))
    assert raw_swap[0][1] * p == 1 and raw_swap[1][0] / Fraction(p) == 1
    assert -raw_swap[0][1] * raw_swap[1][0] == -1
    print(f"Penultimate ranks {a-1} -> {n}: tested {a} flag columns and a raw 1/{p} entry.")


def fourier_lattice():
    for p in (5, 7, 11, 17):
        # Nontrivial characters form a Vandermonde on zeta,...,zeta^(p-1).
        # Reduce its jth Newton column after division by (zeta-1)^j.
        for j in range(p-1):
            column = []
            for i in range(p-1):
                v = 1
                for k in range(j):
                    v = v * (i-k) % p
                column.append(v)
            assert all(x == 0 for x in column[:j])
            assert column[j] == factorial(j) % p != 0
        assert sum(range(p-1)) == (p-1)*(p-2)//2
    print("Augmentation lattice: exact Newton pivots have orders 0 through q-2 at all four test primes.")


if __name__ == "__main__":
    test_charts(3, 2, 3, 5)
    test_charts(3, 4, 3, 3)
    large_rank_control()
    fourier_lattice()
