"""Exclude S5 by a simple integral root of the six-pentagon resolvent."""

from fractions import Fraction
from itertools import combinations, permutations
from math import ceil, floor, prod


def polynomial(coeff, x):
    y = 1
    for a in coeff:
        y = y * x + a
    return y


def real_intervals(coeff):
    # The Hunter search bounds the sum of squares of all roots by 170.
    denominator = 8
    intervals = []
    while len(intervals) != 5:
        intervals = []
        left = Fraction(-15)
        fl = polynomial(coeff, left)
        for j in range(-15 * denominator + 1, 15 * denominator + 1):
            right = Fraction(j, denominator)
            fr = polynomial(coeff, right)
            if fr == 0:
                intervals.append((right, right))
            elif fl * fr < 0:
                intervals.append((left, right))
            left, fl = right, fr
        denominator *= 2
    refined = []
    for left, right in intervals:
        fl = polynomial(coeff, left)
        for _ in range(160):
            if left == right:
                break
            mid = (left + right) / 2
            fm = polynomial(coeff, mid)
            if fm == 0:
                left = right = mid
            elif fl * fm < 0:
                right = mid
            else:
                left, fl = mid, fm
        refined.append((left, right))
    return refined


def square_interval(a, b):
    return (0 if a <= 0 <= b else min(a * a, b * b), max(a * a, b * b))


def resolvent_values(roots):
    edges = list(combinations(range(5), 2))
    terms = []
    for i, j in edges:
        ps = [a * b for a in roots[i] for b in roots[j]]
        terms.append((min(ps), max(ps)))
    classes = set()
    for tail in permutations((1, 2, 3, 4)):
        cyc = (0,) + tail
        perimeter = {tuple(sorted((cyc[i], cyc[(i + 1) % 5]))) for i in range(5)}
        mask = sum(1 << i for i, e in enumerate(edges) if e in perimeter)
        classes.add(min(mask, 1023 - mask))
    assert len(classes) == 6
    for mask in sorted(classes):
        lo = hi = 0
        for i, (a, b) in enumerate(terms):
            if mask >> i & 1:
                lo += a
                hi += b
            else:
                lo -= b
                hi -= a
        yield square_interval(lo, hi)


def simple_integral_root(coeff):
    intervals = list(resolvent_values(real_intervals(coeff)))
    for lo, hi in intervals:
        n = ceil(lo)
        if n != floor(hi):
            continue
        if sum(a <= n <= b for a, b in intervals) != 1:
            continue
        bound = prod(max(abs(n - a), abs(n - b)) for a, b in intervals)
        if bound < 1:
            return n
    raise AssertionError(f"No certified simple rational resolvent root for {coeff}")
