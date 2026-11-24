"""Exact controls for the tower cokernel and the bad-window budget. Standard library only."""
from fractions import Fraction
from math import gcd


def mmul(a, b, mod):
    return tuple(tuple(sum(a[i][t]*b[t][j] for t in range(2)) % mod
                       for j in range(2)) for i in range(2))


def mpow(matrix, exp, mod):
    result = ((1, 0), (0, 1))
    while exp:
        if exp & 1:
            result = mmul(result, matrix, mod)
        matrix = mmul(matrix, matrix, mod)
        exp //= 2
    return result


def cokernel_length(h, twist, m, offdiag):
    # The finite group is (Z/2^h)^2. For a square endomorphism its kernel
    # and cokernel have the same cardinality. Count possible second coordinates.
    modulus = 2**h
    scale = pow(5, twist, modulus)
    a = scale * pow(5, -1, modulus) % modulus
    t = ((a, scale*offdiag % modulus), (0, a))
    upper = mpow(t, 2**m, modulus)
    d, b = (upper[0][0]-1) % modulus, upper[0][1]
    assert (upper[1][1]-1) % modulus == d and upper[1][0] == 0
    step = gcd(d, modulus)
    count = sum(step for y in range(0, modulus, modulus//step) if b*y % step == 0)
    assert count > 0 and count & (count-1) == 0
    return count.bit_length()-1


def matrices():
    h, m, twist = 18, 4, 1+2**20
    assert cokernel_length(h, twist, m, 0) == 36
    assert cokernel_length(h, twist, m, 8) == 25
    for h in (3, 7, 11):
        for k in (2, 3, 5, 33):
            v = ((k-1) & -(k-1)).bit_length()-1
            for m in range(0, h+1):
                r = 2+m+v
                for b in range(1, 4):
                    smaller = min(r, m+b)
                    predicted = min(h, smaller)+min(h, 2*r-smaller)
                    assert cokernel_length(h, k, m, 2**b) == predicted
                assert cokernel_length(h, k, m, 0) == 2*min(h, r)
    # An initial finite segment of a single integral 2-adic centre with very long gaps.
    prefix = 1 + 2**6
    for next_digit in (50, 137):
        centre = prefix + 2**next_digit
        modulus = 2**(next_digit+3)
        eigenvalue = pow(5, -centre, modulus)
        val = (pow(5, prefix, modulus)*eigenvalue-1) % modulus
        assert val == 2**(next_digit+2)
        prefix = centre
    print("Identical determinant curves: lengths 36 and 25 in the finite modules.")
    print("Jordan, scalar and long-gap controls passed.")


def windows():
    # Work in log_2 coordinates: X=2^3100, Ct=2, eta=1, exceptions 2^400 and 2^1599.
    exc = (400, 1599)
    bad = [(Fraction(e, 4), Fraction(e)) for e in exc]
    y_min, y_max = Fraction(3100, 31), Fraction(3100, 2)
    assert bad[0][0] <= y_min < bad[0][1]
    assert bad[1][0] <= bad[0][1] < bad[1][1] and y_max < bad[1][1]
    good_start = Fraction(99)
    assert Fraction(3100, 32) <= good_start <= y_max
    assert all(not (a <= good_start < b) for a, b in bad)
    print("At J=31 all starts are covered. At J=32, log_2(Y)=99 gives a good interval.")


if __name__ == "__main__":
    matrices()
    windows()
