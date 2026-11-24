"""Exact finite arithmetic for the disappearing tail and the degree-seven CM example."""
from fractions import Fraction


def unit_mul(x, y):
    # u^2 = 3u - 1, with coordinates in the basis (1,u).
    a, b = x
    c, d = y
    return a*c - b*d, a*d + b*c + 3*b*d


def tail_checks():
    u, conjugate = (0, 1), (3, -1)
    assert unit_mul(u, conjugate) == (1, 0)
    polynomial = lambda x: x*x - 3*x + 1
    assert polynomial(0) > 0 > polynomial(Fraction(1, 2))
    for cutoff in (0, 3, 12):
        n = cutoff + 1
        a, b = (1, 0), (1, 0)
        for _ in range(n*n):
            a = unit_mul(a, u)
            b = unit_mul(b, conjugate)
        assert (a[0] + 3*a[1], -a[1]) == b
        assert unit_mul(a, b) == (1, 0)
        assert Fraction(5, 2)**(n*n) * Fraction(1, 2)**n > 1
    print("Cutoffs 0, 3, 12 give the exact inverse coefficients. The limit proof is on paper.")


# Q[X]/(X^3+7X^2-21X-91). The cubic is monic and has no rational root.
ONE, X = (1, 0, 0), (0, 1, 0)


def add(*xs):
    return tuple(map(sum, zip(*xs)))


def scale(n, x):
    return tuple(n*t for t in x)


def mul(*xs):
    value = ONE
    for x in xs:
        raw = [0]*5
        for i, a in enumerate(value):
            for j, b in enumerate(x):
                raw[i+j] += a*b
        for k in (4, 3):
            raw[k-1] -= 7*raw[k]
            raw[k-2] += 21*raw[k]
            raw[k-3] += 91*raw[k]
        value = tuple(raw[:3])
    return value


def poly(coeffs):
    v = (0, 0, 0)
    for a in reversed(coeffs):
        v = add(mul(v, X), scale(a, ONE))
    return v


def kernel_seven():
    A, B = -35, -98
    for divisor in (1, 7, 13, 91, -1, -7, -13, -91):
        assert divisor**3 + 7*divisor**2 - 21*divisor - 91
    f = poly([B, A, 0, 1])
    h = poly([-A*A, 12*B, 6*A, 0, 3])
    k = poly([-8*B*B-A**3, -4*A*B, -5*A*A, 20*B, 5*A, 0, 1])
    psi5 = add(scale(32, mul(f, f, k)), scale(-1, mul(h, h, h)))
    psi7 = add(mul(psi5, h, h, h), scale(-128, mul(f, f, k, k, k)))
    assert f != (0, 0, 0) and psi7 == (0, 0, 0)
    num, den = poly([A*A, -8*B, -2*A, 0, 1]), scale(4, f)
    # Test the doubling x-coordinate after clearing its denominator.
    assert add(mul(num, num, num), scale(7, mul(num, num, den)),
               scale(-21, mul(num, den, den)), scale(-91, mul(den, den, den))) == (0, 0, 0)

    # Newton sums of the three x-coordinates. Both signs of each point occur.
    x1 = -7
    x2 = x1*x1 + 42
    x3 = -7*x2 + 21*x1 + 3*91
    velu_a = A - 5*(6*x2 + 6*A)
    velu_b = B - 7*(10*x3 + 6*A*x1 + 12*B)
    assert (velu_a, velu_b) == (49*A, -343*B)
    assert Fraction(2*x1, 4*7) == -Fraction(1, 2)
    print("The six order-seven kernel points give sum x = -14 and cubic coefficient -1/2.")


def four_slot_test():
    def trial(a, b, c, d):
        return 1 + a*b*c*d

    anchor, sample = 0, (1, 1, 1, 1)
    lhs = trial(*sample) * trial(anchor, anchor, anchor, anchor)**3
    rhs = 1
    for z in sample:
        rhs *= trial(z, anchor, anchor, anchor)
    assert (lhs, rhs) == (2, 1)
    print("A symmetric four-variable control fails the slice identity by 2 versus 1.")


if __name__ == "__main__":
    tail_checks()
    kernel_seven()
    four_slot_test()
