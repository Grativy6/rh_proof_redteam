"""Verify the prime, scale, local squareclasses, and finite cocycle model in the dyadic receipt."""
from fractions import Fraction
from itertools import product
from math import gcd

from check_prime_window_readouts import log_interval


def lucas_trace(P, index, modulus):
    """V_j = v^j + v^-j for v + v^-1 = P, calculated by doubling."""
    a, b = 2, P
    for bit in bin(index)[2:]:
        even, odd, next_even = ((a*a - 2) % modulus, (a*b - P) % modulus,
                                (b*b - 2) % modulus)
        a, b = (even, odd) if bit == "0" else (odd, next_even)
    return a


def check_window():
    u = 1 + 4 * 3**205
    d = 3*u*u - 4
    F = 3*(u - 1)
    assert (d + 1) % F == 0 and (F-1)**2 > d and F == 4 * 3**206
    assert lucas_trace(8, d+1, d) == 2
    for p in (2, 3):
        assert gcd(lucas_trace(8, (d+1)//p, d)-2, d) == 1
    assert d.bit_length() == 656 and d % 48 == 23
    assert u % 3 and gcd(4, 3*u*u) == 1
    # Epsilon=1/55, Y=2^40, z=Y^(epsilon/5)=2^(8/55).
    zlo, zhi = Fraction(11, 10), Fraction(111, 100)
    a2, b2 = log_interval(2)
    a3, b3 = log_interval(3)
    assert zlo**55 < 2**8 < zhi**55 and zhi/2 < a3 < b3 < zlo
    assert zhi*(40*b2)**2/2 < 655*a2 <= 656*b2 < zlo*(40*a2)**2
    assert d % 16 == 7 and (d+1) % 3 == 0 and zhi < 3
    target = 40 * (2 + Fraction(8, 55))
    assert 85 < target < 86 and 86 < target + 1
    # Both embeddings of sqrt(-d) in Q_2. The roots modulo 64 cover both residues modulo 8.
    roots = {v % 8 for v in range(64) if (v*v+d) % 64 == 0}
    assert roots == {3, 5}
    assert {(2+v) % 8 for v in roots} == {5, 7}
    # At Y, sqrt(exp(Y^epsilon)) < e < 3. Through Y^2 it is < e^(3/2) < 5.
    assert 2**8 < 2**11 and 5*a2 > 3
    assert 2**16 < 3**11 and Fraction(11, 4)**3 < 25 and 8*a2 > 5
    # At x=2^b the unavoidable weighted length is at least (log 2)*x^401/4.
    # The constants below are conservative rational bounds for its logarithm.
    for b in (40, 1053):
        assert 2**b < (2*(401*b*a2-2))**55
    # At b=1054, the exact odd-twist lower bound alone no longer exceeds the budget.
    assert 2**1054 > (2*401*1054*b2)**55
    print("d = 3*(1+4*3^205)^2-4 is prime (656 bits); WinPair and PageN(86) pass.")
    print("Norm 3*u^2; dyadic residues of 2+sqrt(-d) are 5 and 7 mod 8.")


def action(group_element, value, modulus):
    # Bits record the characters of i and sqrt(alpha), in that order from the low bit.
    return (-value if group_element & 1 else value) % modulus


def coboundary(value, modulus):
    return tuple((action(g, value, modulus) - value) % modulus for g in range(4))


def representative(cocycle, boundaries, modulus):
    return min(tuple((z+b) % modulus for z, b in zip(cocycle, d)) for d in boundaries)


def strict_classes(modulus):
    cob = [coboundary(x, modulus) for x in range(modulus)]
    local = {g: {b[g] for b in cob} for g in (1, 3)}
    strict = set()
    for v in product(range(modulus), repeat=3):
        z = (0, *v)
        if any(z[g ^ h] != (z[g] + action(g, z[h], modulus)) % modulus
               for g in range(4) for h in range(4)):
            continue
        if all(z[g] in local[g] for g in (1, 3)):
            strict.add(representative(z, cob, modulus))
    return strict, cob


def check_cohomology():
    two, _ = strict_classes(2)
    four, cob = strict_classes(4)
    z = (0, 0, 2, 2)  # sqrt(alpha) character, valued in {0,1/2} inside (1/4)Z/Z.
    assert len(two) == 1 and len(four) == 2
    assert z not in cob and representative(z, cob, 4) in four
    assert z[1] == coboundary(0, 4)[1] and z[3] == coboundary(1, 4)[3]
    # A discarded hypothesis really matters: the local actions on A[4] for even twists are trivial.
    for k in range(1, 17):
        unit = pow(3, -k, 4)
        assert (unit-1) % 4 == (2 if k % 2 else 0)
    print("C2 x C2 model: strict class counts at coefficients of order 2 and 4 are 1 and 2.")
    print("The two local coboundary witnesses are respectively 0 and 1/4.")


def check_tower():
    w = 1 + 4 * 3**205
    d = 3*w*w - 4
    for p, expected in ((3, 2), (d, 4)):
        for n in range(4, 17):
            modulus = 2**n
            order = 1
            while pow(p, order, modulus) != 1:
                order *= 2
            assert modulus // (2*order) == expected
    # Gamma has cyclotomic generator 5. At a fixed layer and twist the quotients
    # stabilize in size, while inclusion of coefficients acts by multiplication by two.
    for k in (1, 2, 3, 8):
        v2 = (k & -k).bit_length() - 1
        for m in range(5):
            h = 2 + m + v2
            assert (pow(5, k*2**m, 2**(h+1))-1) % 2**(h+1) == 2**h
            image = set(range(2**h))
            for _ in range(h):
                image = {2*x % 2**h for x in image}
            assert image == {0}
    print("Cyclotomic orbit counts 2 and 4; stable finite cyclic quotients have zero limit.")


if __name__ == "__main__":
    check_window()
    check_cohomology()
    check_tower()
