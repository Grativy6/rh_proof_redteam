"""Verify the conductor-64 obstruction and the two short Fourier rows at 17.

Only the Python standard library is required. Weighted Bernoulli sums are
formed over the integers, including when the conductor is divisible by 17.
"""

from math import gcd


PRIMITIVE = tuple(g for g in range(1, 17) if pow(g, 8, 17) == 16)


def character(f, a):
    if f == 1:
        return 1
    assert f == 17
    return {0: 0, 1: 1, 16: -1}[pow(a, 8, 17)]


def signed_coefficients(f, n):
    level = 2**n
    result = []
    for j in range(level // 8):
        a = pow(5, j, level)
        total = 0
        for i in range(f):
            value = a + i * level
            total += (1 if 2*value > f*level else -1) * character(f, value)
        result.append(total)
    return result


def original_coefficients(f, n):
    level = 2**n
    degree = level // 8
    table = {}
    for j in range(2 * degree):
        a = pow(5, j, level)
        sign = 1 if j < degree else -1
        table[a] = (j % degree, sign)
        table[-a % level] = (j % degree, -sign)
    result = [0] * degree
    for value in range(1, f*level, 2):
        j, sign = table[value % level]
        result[j] += value * character(f, value) * sign
    quotients = []
    for entry in result:
        q, r = divmod(entry, f * level)
        assert r == 0
        quotients.append(q)
    return quotients


def evaluate(coefficients, root):
    value = 0
    for c in reversed(coefficients):
        value = (root * value + c) % 17
    return value


def norm_step(coefficients):
    """Compute P(z)P(-z) in the power basis of z^2."""
    degree = len(coefficients) // 2
    result = [0] * degree
    for i, x in enumerate(coefficients):
        for j, y in enumerate(coefficients):
            if (i + j) % 2:
                continue
            power = (i + j) // 2
            sign = (-1 if j % 2 else 1) * (-1 if power >= degree else 1)
            result[power % degree] += sign * x * y
    return result


def short_sum(a, h, gamma):
    return sum(pow(a+h*b, 8, 17)*pow(gamma, b, 17) for b in range(17)) % 17


def shift_basis(values, exponent):
    """Multiply by X^exponent in Z[X]/(X^d+1), d = len(values)."""
    degree = len(values)
    shifted = [0] * degree
    for j, value in enumerate(values):
        wrap, slot = divmod(j + exponent, degree)
        shifted[slot] += (-value if wrap % 2 else value)
    return shifted


def check_pure_rows():
    for e in range(2, 10):
        size = 2**e
        for n in (2*e - 1, 2*e, 2*e + 1):
            if (e, n) == (2, 3):
                assert signed_coefficients(1, 3) == [-1]
                continue
            level = 2**n
            h, stride = level // size, level // (4*size)
            step = (pow(5, stride, level) - 1) // h
            inverse = pow(step, -1, size)
            row = [1 if 2*pow(5, i*stride, level) > level else -1
                   for i in range(size // 2)]
            one = [1] + [0] * (len(row) - 1)
            if n == 2*e - 1:
                power = (1 + size//4) * inverse
                shifted = shift_basis(row, 2*power)
                correction = shift_basis(one, size//4 + power)
                expected = [2*(v-u) for u, v in zip(one, correction)]
            else:
                shifted = shift_basis(row, inverse)
                expected = [-2*v for v in one]
            assert [u-v for u, v in zip(row, shifted)] == expected


def main():
    check_pure_rows()
    for n in range(3, 12):
        for f in (1, 17):
            assert signed_coefficients(f, n) == original_coefficients(f, n)

    first = signed_coefficients(1, 6)
    assert first == [-1, -1, -1, 1, 1, 1, -1, 1]
    assert [g for g in PRIMITIVE if not evaluate(first, g)] == [11]
    assert pow(11, -1, 17) == 14
    assert all(evaluate(signed_coefficients(17, 6), g) for g in PRIMITIVE)
    for expected in ([-2, 6, 2, 2], [24, -40], [2176]):
        first = norm_step(first)
        assert first == expected

    for f in (1, 17):
        at_128 = signed_coefficients(f, 7)
        assert all(any(evaluate(at_128[j::2], g) for j in range(2)) for g in PRIMITIVE)

    failures = {}
    for exponent in range(8):
        h = pow(2, exponent, 17)
        for gamma in PRIMITIVE:
            if not short_sum(1, h, gamma):
                second = short_sum(5, h, pow(gamma, 13, 17))
                failures[h, gamma] = second
                assert second
    assert failures == {(2, 5):1, (2, 7):11, (16, 3):7, (16, 5):11,
                        (9, 6):4, (9, 7):3}

    for n in range(8, 15):
        level = 2**n
        h, stride = level // 16, level // 64
        c = (pow(5, stride, level)-1) // h
        assert gcd(c, 16) == 1
        coeff = signed_coefficients(17, n)
        for beta in PRIMITIVE:
            for j, a in enumerate((1, 5)):
                gamma = pow(beta, pow(a*c, -1, 16), 17)
                scale = -2 * pow((1-pow(gamma, 17, 17)) % 17, -1, 17)
                assert evaluate(coeff[j::stride], beta) == scale * short_sum(a,h,gamma) % 17
    print("Conductor 64: norm 2176, unique zero label 11 mod 17; inverse label 14.")
    print("Conductor 128: all primitive Bernoulli values are units at 17 for f=1 and f=17.")
    print("Pure signed-row identities for e=2 through 9 passed.")
    print("64 short-row cases: six first-row zeros, all six second rows nonzero.")
    print("Direct comparison of the short rows at n=8 through 14 passed.")


if __name__ == "__main__":
    main()
