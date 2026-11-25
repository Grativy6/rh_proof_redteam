"""Finite character readings for the PAL audit. Run with Python 3.10 or later.

The power-series images are computed from binomial coefficients. The plane
classification is checked a second way, by enumerating the directions of pairs.
"""

from itertools import combinations, product
from math import comb


def directions(points, p):
    result = set()
    for (x, y), (u, v) in combinations(points, 2):
        dx, dy = (u - x) % p, (v - y) % p
        result.add((dy * pow(dx, -1, p)) % p if dx else p)
    return result


def centroids(points, p):
    total = tuple(sum(values) % p for values in zip(*points))
    return [v for v in points if all(4 * vi % p == ti for vi, ti in zip(v, total))]


def count_plane():
    p = 5
    plane = tuple(product(range(p), repeat=2))
    count = 0
    for points in combinations(plane, 4):
        covers = len(directions(points, p)) == p + 1
        center = centroids(points, p)
        noncollinear = len(directions(points, p)) > 1
        assert covers == (noncollinear and len(center) == 1)
        count += covers
    assert count == 2000
    print(f"F5 plane: {count} obstructed four-sets among {comb(len(plane), 4)}.")


def binomial_table(p, r, precision, largest):
    # Coefficients at degrees 0,r,2r,... of (1+t^r)^e mod t^precision.
    length = (precision - 1) // r + 1
    return [tuple(comb(e, j) % p if j <= e else 0 for j in range(length))
            for e in range(largest + 1)]


def observers(points, p, r, precision):
    modulus = p**2
    cutoff = max((a + b) * (modulus - 1) for a, b in points)
    values = binomial_table(p, r, precision, cutoff)
    pair_visible = [False] * comb(len(points), 2)
    common = 0
    for u, v in product(range(modulus), repeat=2):
        read = [values[a*u + b*v] for a, b in points]
        for j, (x, y) in enumerate(combinations(read, 2)):
            pair_visible[j] |= x != y
        common += len(set(read)) == len(points)
    return all(pair_visible), common


def check_precision(p, points, expected):
    for r in (1, 2, 3):
        readings = [observers(points, p, r, m) for m in range(1, p*r + 2)]
        assert next(m for m, (pair, _) in enumerate(readings, 1) if pair) == r + 1
        assert [m for m, (_, count) in enumerate(readings, 1) if count] == [p*r + 1]
        assert readings[-1][1] == expected
    print(f"At {p}: r=1,2,3 all reach first common precision p*r+1.")


def check_three(p):
    plane = tuple(product(range(p), repeat=2))
    for points in combinations(plane, 3):
        assert any(len({(a*u+b*v) % p for a, b in points}) == 3 for u, v in plane)
    print(f"At {p}: every three-set in the first-digit plane separates.")


def main():
    count_plane()
    check_three(3)
    check_three(5)
    check_precision(3, ((0, 0), (1, 0), (0, 1), (1, 1)), 48)
    check_precision(5, ((0, 0), (1, 0), (0, 1), (2, 2)), 480)


if __name__ == "__main__":
    main()
