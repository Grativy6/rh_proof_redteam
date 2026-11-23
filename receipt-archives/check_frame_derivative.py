"""Exact integer checks for the frame derivative. Python 3, standard library."""

from math import comb
from fractions import Fraction


def valuation(n, p):
    if not n:
        raise ValueError("use a finite valuation only on a nonzero integer")
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def factorial_valuation(n, p):
    value = 0
    while n:
        n //= p
        value += n
    return value


def multiply_truncated(f, g, degree):
    result = [0] * (degree + 1)
    for i, a in enumerate(f[:degree + 1]):
        for j, b in enumerate(g[:degree - i + 1]):
            result[i + j] += a * b
    return result


def shift_coefficients(power, rho, order, degree):
    """Return [T^v] (1+T)^rho ((1+T)^power-1)^order for all v <= degree."""
    factor = [0] + [comb(power, i) for i in range(1, min(power, degree) + 1)]
    values = [comb(rho, i) for i in range(min(rho, degree) + 1)]
    for _ in range(order):
        values = multiply_truncated(values, factor, degree)
    return values + [0] * (degree + 1 - len(values))


def finite_difference(power, rho, order, degree):
    return sum((-1) ** (order - k) * comb(order, k) * comb(rho + power * k, degree)
               for k in range(order + 1))


def check_coefficients():
    checked = 0
    for p, power in [(5, 5), (5, 25), (7, 49), (17, 17), (79, 79)]:
        for order in range(1, 7):
            sharp_degree = order * power // p
            for rho in sorted({0, 1, power // 2, power - 1}):
                degree = sharp_degree + 6
                values = shift_coefficients(power, rho, order, degree)
                for v, coefficient in enumerate(values):
                    assert coefficient == finite_difference(power, rho, order, v)
                    if coefficient:
                        exponent = valuation(coefficient, p)
                        # order <= v/power + (1-1/p) * exponent
                        assert p * power * order <= p * v + (p - 1) * power * exponent
                    checked += 1
                assert values[sharp_degree] % (p ** (order + 1)) == p ** order
                assert all(a % (p ** (order + 1)) == 0 for a in values[:sharp_degree])
    return checked


def evaluate_digit_slice(power, N, M, z1, z2, w1, w2):
    """Evaluate the derivative on the x1^M slice, omitting the [z,z'] factor."""
    q, remainder = divmod(M, power)
    assert remainder == 0
    direct = sum((-1) ** k * comb(N, k) * comb(power * k, M)
                 * z1 ** (N-k) * z2 ** k * w1 ** (k-q) * w2 ** (N-k+q)
                 for k in range(q, N + 1))
    determinant = z1*w2 - z2*w1
    retained = 0
    for h in range(q, N):
        shift = shift_coefficients(power, 0, h, M)[M]
        retained += ((-1) ** h * comb(N, h) * shift * z2 ** h
                     * w1 ** (h-q) * w2 ** q * determinant ** (N-h))
    last = ((-1) ** N * shift_coefficients(power, 0, N, M)[M]
            * z2 ** N * w1 ** (N-q) * w2 ** q)
    assert direct == retained + last
    return direct, retained, last


def check_small_determinants():
    for p, power, N in [(5, 5, 5), (5, 25, 5), (7, 7, 14)]:
        M = N * power // p
        for point in [(1, 1, 1, 1), (-1, 2, 0, 3), (2, 1, 1, -1), (3, 1, 2, 2)]:
            direct, retained, error = evaluate_digit_slice(power, N, M, *point)
            assert error % p**N == 0
            if point == (1, 1, 1, 1):
                assert retained == 0 and valuation(direct, p) == N
    assert finite_difference(5, 0, 5, 5) == 3125


def check_full_parameters():
    p, rank, c, q = 79, 2, 2000, 1400
    power = p**3
    N, M = p*q, power*q
    frame_degree = M + power*N + 1
    degrees = [M, N+1, 1, frame_degree, 0, 0, 0]
    slack = N - 1
    assert N+1 - slack == 2 and M-60*c > 0
    for ordinary_degree in [M, N+2]:
        assert rank*Fraction(ordinary_degree, power) + 26*rank*c <= slack
    assert 2*sum(degrees) + rank < p**6
    log_bounds = [5, 3, 1, 6, 1, 1, 1]
    assert all(d + rank < p**b for d, b in zip(degrees, log_bounds))
    e_bound = rank**2 * 7
    kappa_bound = rank * sum(b + 1 for b in log_bounds)
    assert (e_bound, kappa_bound) == (28, 50)
    assert 4 * (4*e_bound + 3*kappa_bound) < c
    assert 1 + 120*c < power and M > 120*c and N > c
    assert sum(factorial_valuation(d, p) for d in degrees) == 716804268
    # The sharp coefficient has a unique least-valuation product.
    assert M == N * (power // p)
    equality = []
    for i in range(1, power + 1):
        cost = 3 - valuation(i, p)
        margin = p*i + (p-1)*power*cost - p*power
        assert margin >= 0
        if margin == 0:
            equality.append((i, cost))
    assert equality == [(power // p, 1), (power, 0)]
    # Lucas gives the unit in C(P,P/p)/p = C(P-1,P/p-1).
    n, k, unit = power - 1, power // p - 1, 1
    while n:
        unit = unit * comb(n % p, k % p) % p
        n, k = n // p, k // p
    assert unit == 1
    return p, power, N, M, frame_degree, slack


if __name__ == "__main__":
    print("Newton coefficients compared by two exact methods:", check_coefficients())
    check_small_determinants()
    print("Three determinant slices agree with their retained terms plus exact error.")
    p, P, N, M, d, slack = check_full_parameters()
    print(f"p={p}, P={P}, N={N}, M={M}, frame degree={d}, slack={slack}")
    print(f"Exact chain cutoff 2, observed weight 1, obstruction valuation {N}.")
