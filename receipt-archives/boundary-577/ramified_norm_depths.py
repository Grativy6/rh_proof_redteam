"""Check the local norm filtration for the four first-order fields over 577."""

from math import gcd

import numpy as np

from artin_units import P, upper_units
from hilbert_reciprocity import BIG_D, ONE, Q, mul, power, roots_of_unity
from residual_directions import local_digit, table


def norm_depth(b, n):
    return n if n <= b else b + P * (n - b)


def filtration():
    assert upper_units() == [35, 387]
    e = 72
    # The coefficient of a unit of depth n in the signed quadratic residue
    # field has tame character omega^(8n). The two depths occur only once.
    breaks = [(j % (P - 1)) // 8 for j in (296, 592)]
    assert breaks == [37, 2]
    depths = [[norm_depth(b, n) for n in (35, 72)] for b in breaks]
    assert depths == [[35, 20232], [19043, 40392]]
    for b in breaks:
        different = (P - 1) * (b + 1)
        for n in range(1, 73):
            k = norm_depth(b, n)
            if n > b:
                assert (different + k) // P == n and (different + k + 1) // P == n + 1
            if n < b:
                assert (different + n) // P > n
        assert different // P == b
    # At the U break, all real digits are doubled. Choose a nonzero
    # trace-zero gamma in the actual residue field F_(p^2).
    anti = np.roll(ONE, 6)
    assert np.array_equal(mul(anti, anti), 5 * ONE)
    assert np.array_equal(power(anti, P), -anti % P)
    assert np.array_equal(power(anti, P - 1), -ONE % P)
    # Frobenius on a+b*sqrt(5) changes the sign of b, so the additive
    # norm polynomial has image the real line and kernel the other line.
    for a in range(P):
        assert (pow(a, P, P) + a) % P == 2 * a % P
    # Determine the unique lowest term of the p-adic log at depth 35.
    # A term indexed by m*p^j has depth at least p^j*35 - j*v_C(p).
    e_up = e * P
    assert e_up % (P - 1) != 0 and 73 * (P - 1) > e_up
    assert 73 + e_up == 41617 and 1 + 2 * e_up == 83089
    minima = [P**j * 35 - j * e_up for j in range(4)]
    assert minima[1] == -21349 and minima[1] < min(minima[0], *minima[2:])
    assert P * 35 * (P - 1) > e_up
    print("Cyclic norm depths for lower and diagonal:", depths)
    print(
        "U-field trace of integers starts at 37; log of a depth-35 norm witness:",
        minima[1],
    )
    print("Joint deepest input depths:", norm_depth(2, 35), 2 + 35 * P + 35 * P**2)


def explicit_lower_digit():
    roots, frob = roots_of_unity()
    y = roots[7]
    inv_y = power(y, Q - 2)
    phi = table(1, True)
    units = [i for i in range(BIG_D) if gcd(i, BIG_D) == 1]
    gauss = phi[units] @ roots[units] % P
    digit = local_digit(1)
    assert digit == 211
    gamma = digit * gauss % P
    # rho^155/pi^75 has depth 280 in the actual Kummer extension after
    # tame base change. Choose d with d^p * gamma^155 = Y^(-1).
    assert 281 * 155 - P * 75 == 280
    target = mul(inv_y, power(gamma, (-155) % (Q - 1)))
    d = power(target, P**11)
    assert np.array_equal(d * frob % P, target)
    assert np.array_equal(mul(power(d, P), power(gamma, 155)), inv_y)
    assert (
        np.array_equal(d, 223 * ONE)
        and 223 * pow(211 * 430, 155, P) * 543 * pow(5, 39, P) % P == 1
    )
    print(
        "Coefficient of the explicit first local lift in F_p[X]/(X^12-5):", d.tolist()
    )
    # Norm, uniformizer and trace-one weights checked in the tame extension.
    for i in (296, 16):
        m = P - i
        assert (P - 1) * m - P * (P - 1) == -(P - 1) * i
        for n in (35, 72):
            trace_one_depth = (P * 8 * n - (P - 1) * i) // 8
            if n > i // 8:
                assert trace_one_depth == norm_depth(i // 8, n)
    assert (P * 280 - (P - 1) * 296) // 8 == -1117


if __name__ == "__main__":
    filtration()
    explicit_lower_digit()
