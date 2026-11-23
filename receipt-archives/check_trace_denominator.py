"""Exact checks of the trace and lattice exponents; all exponents count powers of p."""

from fractions import Fraction
from itertools import combinations
from math import comb, prod


def val(p, a):
    assert a > 0
    value = 0
    while a % p == 0:
        a //= p
        value += 1
    return value


def compositions(d, n):
    if n == 1:
        yield (d,)
    else:
        for first in range(d + 1):
            for tail in compositions(d - first, n - 1):
                yield (first, *tail)


def multinomial(parts):
    remaining = sum(parts)
    value = 1
    for part in parts:
        value *= comb(remaining, part)
        remaining -= part
    return value


def trace_cost_formula(p, n, d):
    total = d + n - 1
    power = p
    cost = 0
    while power <= total:
        cost += min(n - 1, total // power) - (n - 1) // power
        power *= p
    return cost


def maximizing_parts(p, n, d):
    total = d + n - 1
    bars = sorted(sorted(range(1, total + 1), key=lambda x: val(p, x), reverse=True)[:n-1])
    ends = [0, *bars, total + 1]
    return tuple(b - a - 1 for a, b in zip(ends, ends[1:]))


def exact_cost(p, n, d):
    dim = comb(d + n - 1, n - 1)
    return val(p, dim) + max(val(p, multinomial(parts)) for parts in compositions(d, n))


def main():
    for p in (5, 7, 17):
        for n in range(2, 6):
            for d in range(15):
                expected = trace_cost_formula(p, n, d)
                attained = val(p, comb(d + n - 1, n - 1) * multinomial(maximizing_parts(p, n, d)))
                assert expected == attained == exact_cost(p, n, d)
    for d in (24, 25, 29):
        trace = val(5, d + 1)
        cost = exact_cost(5, 2, d)
        assert cost == trace_cost_formula(5, 2, d) == 2
        print(f'p=5, GL(2), degree {d}: trace {trace}, lattice {cost-trace}, combined {cost}')
    assert 100 * trace_cost_formula(17, 2, 16) == 100
    assert 17**3 <= 4*16*100 + 1 < 17**4
    assert 10 * (5 + 25*2 + 70*3) == 2650
    for p, n, h in [(5, 4, 2), (17, 5, 1), (7, 7, 2)]:
        lam = [(p**h - 1) * (n - 1 - i) for i in range(n)]
        dim = prod(Fraction(lam[i] - lam[j] + j - i, j - i) for i, j in combinations(range(n), 2))
        positive_roots = n*(n-1)//2
        assert dim == p**(h * positive_roots)
        assert p**h <= lam[0] + n - 1 < p**(h+1)
        print(f'p={p}, GL({n}), Steinberg parameter {h}: trace cost {val(p, int(dim))}')


if __name__ == '__main__':
    main()
