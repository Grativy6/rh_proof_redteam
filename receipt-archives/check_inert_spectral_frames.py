"""Enumerate normalized self-dual lattices for three split norm-one eigenlines.
Run with Python 3.10+ and the standard library. See the companion paper for the
finite reduction, the Hermite basis, and the link to the two orbital integrals.
"""
from fractions import Fraction
from functools import lru_cache
from itertools import product


def valuation(x, p):
    if not x:
        raise ValueError("distinct slopes are required")
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


@lru_cache(maxsize=None)
def residues(modulus):
    return tuple(product(range(modulus), repeat=2))


# Each completion has degree two over Q_p. The basis element has trace tr and norm n.
def norm(x, tr, n):
    a, b = x
    return a * a + tr * a * b + n * b * b


def is_unit(x, p):
    return x[0] % p != 0 or x[1] % p != 0


def binary_count(p, tr, n, z):
    # Columns (p^r,0), (a,1). Self-duality forces equal gaps on the two axes.
    k = valuation(z[1] - z[0], p)
    counts = []
    for r in range(k + 1):
        mod = p**r
        count = sum(
            (r == 0 or is_unit(a, p))
            and (norm(a, tr, n) + 1) % mod == 0
            and all((z[0] - z[1]) * x % mod == 0 for x in a)
            for a in residues(mod)
        )
        counts.append(count)
    return counts


def triple_count(p, tr, n, z):
    # e_i = product(j!=i)(Z-z_j)/(z_i-z_j) bounds each projected-to-cut gap.
    bounds = [sum(valuation(x - y, p) for j, y in enumerate(z) if i != j)
              for i, x in enumerate(z)]
    counts = {}
    for gaps in product(*(range(b + 1) for b in bounds)):
        r0, r1, r2 = gaps
        if sum(gaps) % 2:
            continue
        # First pure coordinate has ideal p^r0; full third projection has ideal O.
        # The middle diagonal then follows from the determinant of a self-dual basis.
        b1 = sum(gaps) // 2 - r0
        if b1 < 0 or b1 > r1:
            continue
        d0, d1 = p**r0, p**b1
        mod = p**max(gaps)
        w0, w1, w2 = [mod // p**r for r in gaps]
        count = 0
        # Upper triangular columns (d0,0,0), (a,d1,0), (b,c,1).
        # The first column already pairs integrally with every column.
        for a in residues(d0):
            if (w0 * norm(a, tr, n) + w1 * d1**2) % mod:
                continue
            if any((z[0] - z[1]) * x % d0 for x in a):
                continue
            for c in residues(d1):
                if b1 and not is_unit(c, p):
                    continue
                sc = [(z[1] - z[2]) * x for x in c]
                if any(x % d1 for x in sc):
                    continue
                x, y = [part // d1 for part in sc]
                # a times the second coefficient needed to eliminate the middle row.
                ax = a[0]*x - n*a[1]*y
                ay = a[0]*y + a[1]*x + tr*a[1]*y
                last_norm = w1 * norm(c, tr, n) + w2
                for b in residues(d0):
                    if r0 and not (is_unit(a, p) or is_unit(b, p)):
                        continue
                    if ((z[0]-z[2])*b[0] - ax) % d0 or ((z[0]-z[2])*b[1] - ay) % d0:
                        continue
                    if (w0 * norm(b, tr, n) + last_norm) % mod:
                        continue
                    # Both coefficients of the Hermitian pairing of columns two and three.
                    real = (a[0] + tr*a[1])*b[0] + n*a[1]*b[1]
                    imag = a[0]*b[1] - a[1]*b[0]
                    if (w0*real + w1*d1*c[0]) % mod or (w0*imag + w1*d1*c[1]) % mod:
                        continue
                    count += 1
        if count:
            counts[gaps] = count
    return counts


def test_transfer(p, tr, n, z, expected_signed, equal_cluster=False):
    # Irreducible reduction gives the integers of the unramified quadratic field.
    assert all((x*x - tr*x + n) % p for x in range(p))
    grids = triple_count(p, tr, n, z)
    if equal_cluster:
        assert grids == {(0, 0, 0): 1, (0, 1, 1): p+1, (1, 0, 1): p+1,
                         (1, 1, 0): p+1, (2, 2, 2): p*(p+1)**2}
    print(f"p={p}, slopes={z}, unsigned triple count={sum(grids.values())}")
    for i in range(3):
        others = tuple(x for j, x in enumerate(z) if j != i)
        signed = sum((-1)**gaps[i] * count for gaps, count in grids.items())
        inside = sum(binary_count(p, tr, n, others))
        cross = sum(valuation(z[i] - x, p) for x in others)
        # At depth h=1 the resultant has two more powers of p than the slope resultant.
        left = Fraction(inside, (-p)**2)
        right = Fraction(signed, (-p)**(2 + cross))
        assert signed == expected_signed[i] and left == right
        print(f"  singleton={i+1}, signed={signed}, within pair={inside}, transfer={left}")


def test_frame():
    # Choose two lifts of any root of 1+t^2 mod 5^m, with distinct exact valuations.
    root = 2
    for m in range(1, 17):
        scale = 5**m
        lifts = [root + scale*k for k in range(5)]
        deeper, = [t for t in lifts if (1 + t*t) % (5*scale) == 0]
        first = next(t for t in lifts if (1 + t*t) % (5*scale) != 0)
        second = next(deeper + 5*scale*k for k in range(5)
                      if (1 + (deeper + 5*scale*k)**2) % (25*scale) != 0)
        assert first % scale == second % scale
        assert valuation(1 + first*first, 5) == m
        assert valuation(1 + second*second, 5) == m + 1
        root = deeper
    print("Equal frame observations and unequal denominators at 16 consecutive depths.")


def test_precision():
    # The cross resultant keeps valuation 2h. The isolated line has positive parity.
    p = 3
    counts = []
    for k in range(1, 5):
        grids = triple_count(p, 0, 1, (0, 1, 1 + p**k))
        expected = 1 + (p + 1) * (p**k - 1) // (p - 1)
        assert all(gaps[0] == 0 for gaps in grids)
        count = sum(grids.values())
        assert count == expected
        counts.append(count)
    print("Isolated singleton with increasing internal gap:", counts)


if __name__ == "__main__":
    test_frame()
    test_precision()
    test_transfer(3, 0, 1, (0, 3, 6), (45, 45, 45), equal_cluster=True)
    test_transfer(5, 0, 3, (0, 5, 10), (175, 175, 175), equal_cluster=True)
    test_transfer(3, 0, 1, (0, 3, 12), (153, -135, -135))
    test_transfer(2, -1, 1, (0, 2, 4), (-32, 40, -32))
