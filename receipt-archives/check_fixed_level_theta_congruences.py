"""Exact controls for finite markings, determinant classes and the split theta polynomial."""

from fractions import Fraction
from itertools import product

from check_good_bad_congruence_block import CyclotomicRing, add, neg


def scale(scalar, x):
    return tuple(scalar * a for a in x)


def polynomial(ring, roots):
    """Coefficients of the product of (1 - root * X), in ascending degree."""
    coefficients = [ring.one]
    for root in roots:
        new = coefficients + [ring.zero]
        for i, coefficient in enumerate(coefficients):
            new[i + 1] = add(new[i + 1], neg(ring.mul(root, coefficient)))
        coefficients = new
    return coefficients


def divide_constant_one(ring, dividend, divisor):
    assert divisor[0] == ring.one
    residual = dividend.copy()
    quotient = []
    for i in range(len(dividend) - len(divisor) + 1):
        coefficient = residual[i]
        quotient.append(coefficient)
        for j, factor in enumerate(divisor):
            residual[i + j] = add(residual[i + j], neg(ring.mul(coefficient, factor)))
    assert all(x == ring.zero for x in residual)
    return quotient


def check_theta_polynomial():
    ring = CyclotomicRing(3, 1)
    norm = Fraction(7)
    string = [scale(norm ** k, ring.one) for k in (2, 1, 0, -1, -2)]
    # Every fixed and moving root is 1 in F_3 after zeta_3 is reduced to 1.
    fixed = polynomial(ring, string)
    for k in range(ring.order):
        row_roots = [ring.root(k), ring.root(k)]
        lifted = polynomial(ring, row_roots + string)
        assert divide_constant_one(ring, lifted, fixed) == polynomial(ring, row_roots)
        for root in row_roots + string:
            residue = sum(root, Fraction(0))
            assert residue.denominator % 3 and (residue.numerator - residue.denominator) % 3 == 0
    rotated = [ring.mul(ring.root(1), root) for root in [ring.one, ring.one] + string]
    assert string[0] not in rotated
    print("Seven roots coincide after reduction mod 3. Fixed-block division is exact.")


def check_projection():
    ring = CyclotomicRing(3, 1)
    u = add(ring.one, neg(ring.root(1)))
    values = [ring.zero, ring.one, add(ring.one, ring.root(1))]
    for i, value in enumerate(values):
        assert ring.mul(u, value) == add(ring.one, neg(ring.root(i)))

    # Input is supported on one of five class fibres. The two marking factors
    # (1 - zeta^i)/(1 - zeta) have integral coordinates at all nine markings.
    source = {(c, i, j): ring.mul(values[i], values[j]) if c == 0 else ring.zero
              for c, i, j in product(range(5), range(3), range(3))}
    projected = {}
    for a, b in product(range(3), repeat=2):
        coefficient = ring.zero
        for (_, i, j), value in source.items():
            coefficient = add(coefficient, ring.mul(ring.root(-a*i-b*j), value))
        # The effective projector keeps the trivial class character and
        # only the good marks. It may discard additional good labels.
        if 1 not in (a, b) and (a, b) != (2, 2):
            projected[a, b] = scale(Fraction(1, len(source)), coefficient)

    expected_denominator = scale(5, ring.mul(u, u))
    assert ring.mul(expected_denominator, projected[0, 0]) == ring.one
    assert all(v == ring.zero for k, v in projected.items() if k != (0, 0))
    assert ring.valuation(ring.mul(u, u)) == 2
    print("The extra kernel cut leaves 1 / (5 * (1-zeta_3)^2) on the retained vector.")


def check_representatives():
    ring = CyclotomicRing(3, 1)
    u = add(ring.one, neg(ring.root(1)))
    powers = [ring.one, u, ring.mul(u, u)]
    for n, value_after_three in enumerate(powers):
        # Coefficients in the two orbit coordinates must agree mod u^3.
        # The zeroth Fourier coefficient forces their scalars to agree mod u^3.
        diffs = [add(value_after_three, neg(ring.mul(value_after_three, ring.root(-k))))
                 for k in range(3)]
        assert all(x == ring.zero or ring.valuation(x) >= 3 for x in diffs) == (n >= 2)
    assert ring.valuation(scale(3, powers[2])) == ring.valuation(scale(9, ring.one))
    print("Two congruent three-point orbits give evaluated ideal (9) in the control.")


def check_split_two():
    # For d=23, norm(a+b*(1+sqrt(-23))/2) = a^2 + a*b + 6*b^2.
    # Four times the norm is (2*a+b)^2 + 23*b^2, bounding this exact search.
    small = {(a, b): a*a + a*b + 6*b*b
             for a in range(-4, 5) for b in range(-1, 2)}
    assert 2 not in small.values()
    assert all(b == 0 for (a, b), norm in small.items() if norm == 4)
    assert small[1, 1] == 8
    # The element 1+omega is nonzero at only one of the two residue roots.
    assert [(1+x) % 2 for x in (0, 1)] == [1, 0]
    print("For discriminant -23 the prime ideal over 2 has exact class order 3.")


if __name__ == "__main__":
    check_theta_polynomial()
    check_projection()
    check_representatives()
    check_split_two()
