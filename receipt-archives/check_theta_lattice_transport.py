"""Checks for the finite theta projector and the CM cusp calculation.

Run with Python 3.8+ and its standard library. The finite group tests are
exact. The two class-mean evaluations use separate floating-point formulas.
"""

import cmath
import math
from collections import Counter
from itertools import product


def check_period_characters():
    # O_K for K=Q(sqrt(-7)), with omega=(1+sqrt(-7))/2. Reduced modulo
    # 2 the coordinates below are the two F_2 components, not power-basis
    # coefficients. The allowed shift has doubled class (1,1).
    points = list(product(range(2), repeat=2))

    def twist(t, x):
        pairing = (t[0] * x[1] + t[1] * x[0]) % 2
        odd_section = 1 if x == (0, 0) else -1
        return odd_section * (-1) ** pairing

    expected = [(-1) ** (a * b) for a, b in points]
    matching = [t for t in points if [twist(t, x) for x in points] == expected]
    assert matching == [(1, 1)]

    # Apply (1/5) [[3,-4],[4,3]] in two coordinates of a fourfold
    # product, with identity on the other two. The active period
    # coordinates have basis 1,omega in each copy. Both quotients
    # by the intersection have 25 classes, parametrized by F_5^2.
    quotient = list(product(range(5), repeat=2))
    assert 3 * 3 + 4 * 4 == 25
    characters = [tuple(3 * (v * a - u * b) % 5 for u, v in quotient)
                  for a, b in quotient]
    assert len(set(characters)) == 25
    for i, first in enumerate(characters):
        for j, second in enumerate(characters):
            counts = Counter((a - b) % 5 for a, b in zip(first, second))
            assert counts == ({0: 25} if i == j else dict.fromkeys(range(5), 5))
    # 1+zeta+...+zeta^4=0. Square norm after averaging is 25*(1/5)^2.
    print("25 distinct period characters; 600 off-diagonal inner products vanish.")


def check_divided_torsion():
    # Columns of 5g on E[25] describe (S/5)/P. Represent torsion
    # in the numerator modulo 25, first real then omega coefficients.
    column_image = {((3 * a - 4 * b) % 25, (4 * a + 3 * b) % 25)
                    for a, b in product(range(25), repeat=2)}
    subgroup = {u + v for u in column_image for v in column_image}
    assert len(column_image) == 25 and len(subgroup) == 625

    # Multiplication by omega has matrix [[0,-2],[1,1]]. This is an
    # invertible O_K-linear torsion control. Its determinant changes
    # the Weil-pairing exponent by 2 modulo 25.
    moved = {(-2 * v % 25, -2 * w % 25, (a + v) % 25, (b + w) % 25)
             for a, b, v, w in subgroup}
    assert moved == subgroup
    original = (3, 4, 0, 0)
    wrong_lift = (8, 4, 0, 0)
    assert all((a - b) % 5 == 0 for a, b in zip(original, wrong_lift))
    assert original in subgroup and wrong_lift not in subgroup
    print("625 divided torsion classes; the wrong lift passes level 5 and fails level 25.")


def check_analytic_average():
    # The other two coordinates of the fourfold product stay at zero.
    omega = complex(0.5, math.sqrt(7) / 2)
    area = omega.imag
    reps = list(product(range(-2, 3), repeat=2))

    def theta_two(z):
        center = round(-z.imag / area - 0.5)
        return sum(cmath.exp(1j * math.pi * ((n + 0.5) ** 2 * omega
                                              + 2 * (n + 0.5) * z))
                   for n in range(center - 9, center + 10))

    constant = theta_two(0)

    def base(z):
        factors = [cmath.exp(math.pi * w * w / (2 * area)) * theta_two(w) / constant
                   for w in z]
        return factors[0] * factors[1]

    def translated(fn, v, z):
        pairing = sum(w * a.conjugate() for w, a in zip(z, v))
        squared = sum(abs(a) ** 2 for a in v)
        return fn(tuple(w + a for w, a in zip(z, v))) * cmath.exp(
            -math.pi * (pairing + squared / 2) / area)

    def average(fn, direction, z):
        total = 0j
        for a, b in reps:
            norm = a * a + a * b + 2 * b * b
            v = tuple((a + b * omega) * u for u in direction)
            total += (-1) ** norm * translated(fn, v, z)
        return total / 5

    def projected(z):
        return average(base, (3 / 5, 4 / 5), z)

    errors = []
    for z in [(0j, 0j), (0.14 + 0.09j, -0.25 + 0.37j), (0.22j, 0.35 - 0.1j)]:
        errors.append(abs(average(projected, (1, 0), z) - base(z)))
    assert max(errors) < 2e-11
    print(f"Three direct Jacobi evaluations; largest inverse-average error {max(errors):.2e}.")


    # Move one target coordinate by u=tau/conj(tau), a two-coset rotation.
    # On the fourfold product the other three slots can be held at zero.
    rotation = omega / omega.conjugate()
    phase = omega.conjugate() / math.sqrt(2)
    assert abs(phase * phase - rotation.conjugate()) < 2e-15
    phase_errors = []
    for w in (0j, 0.13 + 0.24j, -0.28j):
        z = (rotation * w, 0j)
        raw = (base(z) - translated(base, (rotation, 0), z)) / math.sqrt(2)
        phase_errors.append(abs(raw - phase * base((w, 0j))))
    assert max(phase_errors) < 2e-12
    # Two source columns and two elliptic factors with diagonal K action.
    raw_row_scalar = phase ** 4
    target_correction = rotation ** 2
    assert abs(raw_row_scalar * target_correction - 1) < 2e-14
    assert abs(raw_row_scalar / target_correction - 1) > 0.1
    print(f"Two-coset phase and target-row sign; largest phase error {max(phase_errors):.2e}.")


def reduced_forms(d):
    """Primitive reduced positive forms of fundamental discriminant -d."""
    for a in range(1, math.isqrt(d // 3) + 1):
        for b in range(-a, a + 1):
            c, rem = divmod(b * b + d, 4 * a)
            if rem or a > c or ((a == abs(b) or a == c) and b < 0):
                continue
            if math.gcd(math.gcd(a, b), c) == 1:
                yield a, b, c


def evaluate_form(d, form):
    a, b, c = form
    x, y = -b / (2 * a), math.sqrt(d) / (2 * a)
    alpha, beta = (a % 2) / 2, (c % 2) / 2
    assert not (alpha and beta)
    terms = []
    for n in range(-10, 11):
        u = n + alpha
        exponent = -math.pi * y * (u * u - alpha * alpha)
        phase = math.pi * (x * u * u + 2 * u * beta)
        terms.append(cmath.rect(math.exp(exponent), phase))
    log_theta = math.log(abs(sum(terms))) - math.pi * y * alpha * alpha
    log_norm = -0.5 * math.log(2 * y) - 2 * log_theta
    nome = cmath.exp(2j * math.pi * complex(x, y))
    eta_remainder = math.fsum(math.log(abs(1 - nome ** k)) for k in range(1, 17))
    shape = math.pi * y / 6 - 0.5 * math.log(y) - 2 * eta_remainder
    return log_norm, shape


def mean_shape_via_character(d):
    # L(0,chi) and L'(0,chi) from the Hurwitz values at 0, then the
    # odd primitive quadratic functional equation. Euler's constant
    # cancels in the resulting class-mean expression.
    chi = [1 if pow(a, (d - 1) // 2, d) == 1 else -1 for a in range(1, d)]
    numerator = -sum(a * v for a, v in enumerate(chi, 1))
    value_zero, remainder = divmod(numerator, d)
    assert remainder == 0 and value_zero > 0
    gamma_sum = math.fsum(v * math.lgamma(a / d) for a, v in enumerate(chi, 1))
    return 0.25 * math.log(d) + 0.5 * (math.log(4 * math.pi) - gamma_sum / value_zero)


def check_cusp():
    print(" d      classes   log norm, principal   mean log+ norm   mean B")
    for d in (7, 23, 71, 103, 199, 1031, 10007):
        assert d % 16 == 7 and all(d % p for p in range(2, math.isqrt(d) + 1))
        forms = list(reduced_forms(d))
        values = [evaluate_form(d, f) for f in forms]
        mean_shape = math.fsum(b for _, b in values) / len(forms)
        assert abs(mean_shape - mean_shape_via_character(d)) < 2e-10
        principal = next(v[0] for f, v in zip(forms, values) if f[0] == 1)
        mean_log_plus = math.fsum(max(0, v) for v, _ in values) / len(forms)
        print(f"{d:5d} {len(forms):9d} {principal:21.8f} "
              f"{mean_log_plus:16.8f} {mean_shape:10.8f}")


if __name__ == "__main__":
    check_period_characters()
    check_divided_torsion()
    check_analytic_average()
    check_cusp()
