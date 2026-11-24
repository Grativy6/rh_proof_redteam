"""Finite controls for detecting a determinant class by a fixed theta string."""

from collections import Counter
from math import prod

from check_good_bad_congruence_block import CyclotomicRing, add, neg
from check_fixed_level_theta_congruences import scale


def monic_polynomial(ring, roots):
    coefficients = [ring.one]
    for root in roots:
        new = [ring.zero] + coefficients
        for i, coefficient in enumerate(coefficients):
            new[i] = add(new[i], neg(ring.mul(root, coefficient)))
        coefficients = new
    return coefficients


def reduce_mod(x, modulus):
    return tuple(a % modulus for a in x)


def evaluate(ring, coefficients, x, modulus):
    value = ring.zero
    for coefficient in reversed(coefficients):
        value = reduce_mod(add(ring.mul(value, x), coefficient), modulus)
    return value


def check_shared_root():
    p, precision = 11, 3
    modulus = p ** precision
    ring = CyclotomicRing(p, 1)
    selected = (1, 2, 4, 8, 16)
    first = selected + (2, 4)
    second = selected + (2 + p * p, 4 - p * p)
    outside = (1, 2, 4, 8 + p, 16, 2, 4)
    # The residual derivative at 8 is the same for all three orbits.
    derivative = prod(8 - root for root in first if root != 8)
    step = pow(derivative, -1, p)
    inverse_eight = pow(8, -1, modulus)
    for orbit, roots in enumerate((first, second, outside)):
        for j in range(p):
            twist = ring.root(j)
            polynomial = monic_polynomial(ring, [scale(root, twist) for root in roots])
            x = scale(8, ring.one)
            for _ in range(precision * (p - 1)):
                correction = scale(step, evaluate(ring, polynomial, x, modulus))
                x = reduce_mod(add(x, neg(correction)), modulus)
            actual = reduce_mod(scale(inverse_eight, x), modulus)
            if orbit < 2:
                assert actual == reduce_mod(twist, modulus)
                value = evaluate(ring, [ring.one] * p, actual, modulus)
                assert value == (scale(p, ring.one) if j == 0 else ring.zero)
            else:
                assert x == reduce_mod(scale(8 + p, twist), modulus)
                if j == 0:
                    assert evaluate(ring, [ring.one] * p, actual, modulus) != ring.zero
    print("One common iteration identifies all 22 selected twists mod 11^3.")
    print("On the outside orbit the selector needs the support condition.")


def multiply_polynomials(ring, left, right):
    result = [ring.zero] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i+j] = add(result[i+j], ring.mul(a, b))
    return result


def inverse_mod_prime(matrix, prime):
    n = len(matrix)
    rows = [row[:] + [int(i == j) for j in range(n)] for i, row in enumerate(matrix)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if rows[i][j] % prime)
        rows[j], rows[pivot] = rows[pivot], rows[j]
        inverse = pow(rows[j][j], -1, prime)
        rows[j] = [(v * inverse) % prime for v in rows[j]]
        for i in range(n):
            if i != j:
                multiplier = rows[i][j]
                rows[i] = [(a - multiplier * b) % prime for a, b in zip(rows[i], rows[j])]
    return [row[n:] for row in rows]


def check_cluster():
    p, precision = 7, 2
    ring = CyclotomicRing(p, 1)
    modulus = p ** precision
    roots = [2**i for i in range(8)] + [1]
    counts = Counter(root % p for root in roots[:-1])
    assert sorted(counts.values()) == [2, 3, 3]
    bucket = [x for x in roots if x % p == 2]
    rest = [x for x in roots if x % p != 2]
    assert len(bucket) == 3
    base_g = monic_polynomial(ring, [scale(x, ring.one) for x in bucket])
    base_h = monic_polynomial(ring, [scale(x, ring.one) for x in rest])
    # Linearize (g,h) -> gh once at the common residue polynomial.
    c, n = len(bucket), len(roots)
    columns = []
    for factor, shifts in ((base_h, c), (base_g, n-c)):
        for j in range(shifts):
            column = [0] * j + [sum(value) % p for value in factor]
            columns.append(column + [0] * (n-len(column)))
    inverse = inverse_mod_prime([list(row) for row in zip(*columns)], p)
    for j in range(p):
        polynomial = monic_polynomial(ring, [scale(x, ring.root(j)) for x in roots])
        g, h = base_g.copy(), base_h.copy()
        for _ in range(precision * (p - 1)):
            trial = multiply_polynomials(ring, g, h)
            error = [add(x, neg(y)) for x, y in zip(polynomial[:-1], trial[:-1])]
            corrections = []
            for row in inverse:
                delta = ring.zero
                for scalar, entry in zip(row, error):
                    delta = add(delta, scale(scalar, entry))
                corrections.append(delta)
            g[:-1] = [reduce_mod(add(x, y), modulus) for x, y in zip(g[:-1], corrections[:c])]
            h[:-1] = [reduce_mod(add(x, y), modulus) for x, y in zip(h[:-1], corrections[c:])]
        check = multiply_polynomials(ring, g, h)
        assert [reduce_mod(x, modulus) for x in check] == [reduce_mod(x, modulus) for x in polynomial]
        constant = reduce_mod(scale(pow(base_g[0][0], -1, modulus), g[0]), modulus)
        recovered = ring.one
        for _ in range(pow(c, -1, p)):
            recovered = reduce_mod(ring.mul(recovered, constant), modulus)
        assert recovered == reduce_mod(ring.root(j), modulus)
    print("The same factor lift recovers all seven twists without a simple fixed root.")


def check_resultant(p, a, q, length, twist_power):
    ring = CyclotomicRing(p, a)
    delta = ring.root(twist_power)
    roots = [q**i for i in range(length)]
    resultant = ring.one
    for x in roots:
        for y in roots:
            difference = add(scale(x, ring.one), neg(scale(y, delta)))
            resultant = ring.mul(resultant, difference)
    counts = Counter(root % p for root in roots)
    collision_pairs = sum(n*n for n in counts.values())
    twist_depth = ring.valuation(add(ring.one, neg(delta)))
    actual = ring.valuation(resultant)
    assert actual == collision_pairs * twist_depth
    print(f"p={p}, root order={p**a}, twist power={twist_power}, q={q}, t={length}, "
          f"resultant valuation {actual} in uniformizer units.")


if __name__ == "__main__":
    check_shared_root()
    check_cluster()
    for case in [(3, 1, 7, 5, 1), (3, 2, 7, 5, 1), (3, 2, 2, 5, 3),
                 (5, 1, 2, 6, 1), (7, 1, 2, 8, 1)]:
        check_resultant(*case)
