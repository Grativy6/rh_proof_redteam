"""Compute elementary divisors of the two-row product families in both slot conventions."""

from collections import Counter
from itertools import permutations
from math import comb

from check_correlated_places import P, smith_exponents


def add_multiple(result, term, coefficient):
    for monomial, value in term.items():
        total = result.get(monomial, 0) + coefficient * value
        if total:
            result[monomial] = total
        else:
            result.pop(monomial, None)


def multiply(left, right):
    result = Counter()
    for m, a in left.items():
        for n, b in right.items():
            result[tuple(sorted(m + n))] += a * b
    return {monomial: value for monomial, value in result.items() if value}


def determinant(rows, width, sign=1):
    """Minor in the first len(rows) columns of a generic matrix."""
    result = {}
    for ordered in permutations(rows):
        parity = sum(a > b for i, a in enumerate(ordered) for b in ordered[i + 1:])
        monomial = tuple(sorted(row * width + column for column, row in enumerate(ordered)))
        result[monomial] = sign * (-1)**parity
    return result


def slot(cofactor, k):
    rows = tuple(range(k))
    if cofactor:
        flat = [determinant(tuple(j for j in rows if j != i), k, (-1)**(i+k-1)) for i in rows]
        minors = {(i, j): determinant(tuple(a for a in rows if a not in (i, j)), k, (-1)**(i+j))
                  for i in rows for j in rows if i < j}
    else:
        flat = [determinant((i,), k) for i in rows]
        minors = {(i, j): determinant((i, j), k) for i in rows for j in rows if i < j}
    return flat, minors


def flat_monomials(flat, degree, minimum=0):
    if degree == 0:
        yield {(): 1}
        return
    for i in range(minimum, len(flat)):
        for rest in flat_monomials(flat, degree - 1, i):
            yield multiply(flat[i], rest)


def valuations(polynomials, precision):
    # The transpose has the same nonzero elementary divisors and keeps the
    # short matrix dimension equal to the number of proposed generators.
    monomials = set().union(*(poly.keys() for poly in polynomials))
    columns = [[poly.get(m, 0) for poly in polynomials] for m in sorted(monomials)]
    return Counter(smith_exponents(columns, len(polynomials), precision))


def check(k, degree, cofactor, exponent):
    flat, minors = slot(cofactor, k)
    polynomials = list(flat_monomials(flat, degree))
    outputs = len(polynomials) * (k - 1)
    failures = comb(degree + k - 2, k - 1)
    precision = exponent + 1
    star = [minors[0, j] for j in range(1, k)]
    triangle = star[:-1] + [minors[1, 2]]
    changed = dict(minors[1, 2])
    add_multiple(changed, star[-1], P**exponent)
    tilted = star[:-1] + [changed]
    for label, family, expected in [
        ('selected', star, {0: outputs}),
        ('triangle', triangle, {0: outputs - failures, precision: failures}),
        ('tilted', tilted, {0: outputs - failures, exponent: failures}),
    ]:
        # An exponent equal to precision is zero in the truncated coefficient ring.
        result = valuations([multiply(f, b) for f in polynomials for b in family], precision)
        assert result == expected, (k, degree, cofactor, label, result, expected)
        print(f'k={k} d={degree} {"cofactor" if cofactor else "vector"} {label}: '
              f'{dict(sorted(result.items()))}')


if __name__ == '__main__':
    for odd in [False, True]:
        check(k=4, degree=2, cofactor=odd, exponent=3)
    check(k=5, degree=3, cofactor=False, exponent=4)
