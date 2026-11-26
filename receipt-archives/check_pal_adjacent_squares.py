"""Compute the full two-square bill from two polynomial sums and the divisors of 2b+1."""

from fractions import Fraction as Q
from math import comb, isqrt
import json

from check_pal_square_holes import marks, sixth_prefix
from check_pal_doubled_ruler import extra


def common(b):
    gap = 2 * b + 1
    for r in range(3, isqrt(gap) + 1, 2):
        v, rem = divmod(gap, r)
        if rem == 0 and r < v:
            t, u = (v - r) // 2, (v + r) // 2
            d = b * b - t * t
            assert d == (b + 1) ** 2 - u * u and 8 * b * b < 9 * d <= 9 * b * b
            yield r, v, t, u, d


def section(n, d):
    """Polynomial extension of the second quotient cell, including its endpoint."""
    N = 2 * n
    return (N - d) ** 5 * (7 * d - N) + (N - 2 * d) ** 5 * (14 * d - N) - N**5 * (n - d)


def series_sum(fn, first, last):
    if first > last:
        return 0
    differences = [fn(t) for t in range(13)]
    total = 0
    for j in range(13):
        total += differences[0] * (comb(last + 1, j + 1) - comb(first, j + 1))
        differences = [y - x for x, y in zip(differences, differences[1:])]
    return total


def fast(b):
    assert b >= 4
    n = b * b
    T = isqrt((n - 1) // 3)
    U = isqrt((n + 6 * b + 2) // 3)
    low = isqrt(2 * b)
    old = series_sum(lambda t: section(n, b * b - t * t), 1, T)
    new = series_sum(lambda t: section(n, (b + 1) ** 2 - t * t), low + 1, U)
    hits = list(common(b))
    refund = old + new - sum(section(n, d) for _, _, _, _, d in hits)
    union = T + U - low - len(hits)
    bill = max(0, sixth_prefix(2 * n) - 16 * n**7 - refund)
    return union, refund, bill, hits


def brief(b):
    size, credit, bill, hits = fast(b)
    return {
        "center": b,
        "center_gap": 2 * b + 1,
        "distinct_composites": size,
        "overlaps": len(hits),
        "refund_numerator": str(credit),
        "bill_numerator": str(bill),
    }


def audit():
    for b in range(4, 321):
        n = b * b
        one, two = marks(n, b), marks(n, b + 1)
        size, refund, bill, hits = fast(b)
        assert one & two == {x[4] for x in hits}
        assert size == len(one | two)
        direct = sum(extra(n, d) for d in one | two)
        assert refund == direct and bill == max(
            0, sixth_prefix(2 * n) - 16 * n**7 - direct
        )
        if b in (4, 64, 320):
            assert all(section(n, d) == extra(n, d) for d in one | two)
    assert list(common(64)) == [(3, 43, 20, 23, 3696)]
    for k in range(4, 161):
        if k % 3:
            b = k * k
            assert any(r == 3 and t == (b - 4) // 3 for r, _, t, _, _ in common(b))
    return {
        "direct_centers_inclusive": [4, 320],
        "example": {
            "lower_square": 64**2,
            "upper_square": 65**2,
            "factor_pairs_of_gap": [[1, 129], [3, 43]],
            "genuine_intersection": [3696],
        },
        "exact_large_examples": [brief(b) for b in (64, 10000, 10**8, 10**12)],
        "second_term_sqrt2_factor": str(Q(5, 32)),
        "scope": "These integer bills preserve the full signed-polynomial return on the union. The separate retained-prime product is not evaluated at the large examples.",
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
