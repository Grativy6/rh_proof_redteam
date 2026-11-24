"""Compute the dyadic determinant lengths in the two small arithmetic controls.

The number-field and p-adic interpolation identifications are in the companion
paper. Every character sum and divided difference here is exact.
"""
from fractions import Fraction
from math import comb, gcd, isqrt

from check_prime_window_readouts import legendre, prime_small


def v2(n):
    if not n:
        raise ValueError("valuation of zero is infinite")
    n = abs(n)
    return (n & -n).bit_length()-1


def valuation(x):
    return v2(x.numerator)-v2(x.denominator)


def ordinary_bernoulli(n):
    values = [Fraction(1)]
    for j in range(1, n+1):
        values.append(-sum(comb(j+1, i)*values[i] for i in range(j))/(j+1))
    return values


def moments(d, k, finite_twist):
    # omega_2^(−k−1) is the mod-4 odd character when k is even.
    odd_character = k % 2 == 0
    at_two = 8 if finite_twist else (4 if odd_character else 1)
    conductor = 3*d*at_two
    chi_d = [legendre(a, d) for a in range(d)]
    chi3 = (0, 1, -1)
    chi8 = (0, 1, 0, -1, 0, -1, 0, 1)
    chi4 = (0, 1, 0, -1)
    n = k+1
    totals = [0]*(n+1)
    for a in range(1, conductor+1):
        chi = chi3[a%3]*chi_d[a%d]
        if finite_twist:
            chi *= chi8[a%8]
        if odd_character:
            chi *= chi4[a%4]
        if chi:
            power = chi
            for j in range(n+1):
                totals[j] += power
                power *= a
    assert totals[0] == 0
    return conductor, totals


def interpolated_value(d, k, finite_twist):
    n = k+1
    f, s = moments(d, k, finite_twist)
    # Expansion of f^(n-1) sum_a chi(a) B_n(a/f).
    ordinary = ordinary_bernoulli(n)
    bern = sum(comb(n,j)*ordinary[j]*f**j*s[n-j] for j in range(n+1))/f
    # Independent coefficient comparison after multiplying the generating
    # function by exp(f*t)-1. This method uses no ordinary Bernoulli numbers.
    general = []
    for j in range(n+1):
        rest = sum(comb(j+1,i)*f**(j+1-i)*general[i] for i in range(j))
        general.append(Fraction((j+1)*s[j]-rest,(j+1)*f))
    assert general[-1] == bern and bern
    euler = 1+2**k if f % 2 else 1
    return -euler * bern / n


def reduced_class_number(D):
    # Primitive positive definite reduced binary quadratic forms for fundamental D<0.
    count = 0
    for a in range(1, isqrt(-D//3)+1):
        for b in range(-a, a+1):
            c, rem = divmod(b*b-D, 4*a)
            if rem or a > c or gcd(gcd(a, abs(b)), c) != 1:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            count += 1
    return count


def run():
    for d in (23, 167):
        assert prime_small(d) and d % 48 == 23
        class_numbers = tuple(reduced_class_number(-f*3*d) for f in (4,8))
        assert class_numbers == ((8,8) if d == 23 else (16,16))
        values = {}
        for k in (1, 2, 3, 4, 5, 7, 13, 35, 45, 67, 77):
            pair = tuple(interpolated_value(d,k,twist) for twist in (False,True))
            values[k] = pair
        t1, t3 = Fraction(1,5)-1, Fraction(1,125)-1
        divided = (values[3][0]-values[1][0])/(2*(t3-t1))
        assert valuation(divided) == 1
        lengths = {k: tuple(valuation(x)-1 for x in pair) for k,pair in values.items()}
        if d == 23:
            assert values[1][0] == -72 and values[3][0] == 178200
            assert all(pair == (2,2) for pair in lengths.values())
        else:
            assert values[1] == (-1440,-12864) and values[3] == (183928320,31350541344)
            assert lengths[35] == (14,4) and lengths[77] == (4,10)
            for k, pair in lengths.items():
                assert pair == (3+v2(k-2083),3+v2(k-205))
        print(f"q=3, d={d}: {lengths}")
    print("The two entries at each twist are the positive- and negative-argument determinant valuations. Both Bernoulli calculations agree.")


if __name__ == "__main__":
    run()
