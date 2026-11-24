"""Exact Fourier refinement and determinant-jet controls, using Python 3.8+."""

import math
from collections import Counter


def check_refinement(coarse, factor):
    fine = coarse * factor
    for t in range(coarse):
        for y in range(fine):
            exponents = [(y * (t + coarse * j)) % fine for j in range(factor)]
            if y % factor == 0:
                k = y // factor
                assert exponents == [factor * ((k * t) % coarse)] * factor
            else:
                order = factor // math.gcd(y, factor)
                # The fiber sum is a full regular polygon, evenly repeated.
                reduced = [((e - exponents[0]) % fine) // (fine // order) for e in exponents]
                assert all((e - exponents[0]) % (fine // order) == 0 for e in exponents)
                assert Counter(reduced) == dict.fromkeys(range(order), factor // order)
    print(f"Position level {fine} -> {coarse}: all {factor} fine indicators per fiber sum to one coarse indicator.")


def check_rectangular_jets():
    print("  m   log excess over 2*ph(m)   published log allowance (a=2,b=4)")
    for m in (1, 2, 4, 16, 64, 256):
        # D=(x11*x22-x12*x21)^m. Contraction of D with D multiplies
        # the square of each coefficient by the four exponent factorials.
        norm = sum(math.comb(m, j) ** 2 * math.factorial(j) ** 2 * math.factorial(m-j) ** 2
                   for j in range(m+1))
        assert norm == math.factorial(m) * math.factorial(m+1)
        phi = m * math.log(m) - m
        # G=exp(-ph(m)) D has optimal Gaussian growth constant 1.
        # Thus log(output norm squared) = 2log(norm)-2ph(m).
        excess = 2 * math.log(norm) - 4 * phi
        allowance = 1 + 16 * math.log(4 * m + 2)
        assert 0 < excess < allowance
        print(f"{m:3d} {excess:26.7f} {allowance:38.7f}")


if __name__ == "__main__":
    for pair in ((3, 5), (3, 3), (5, 9), (4, 6)):
        check_refinement(*pair)
    check_rectangular_jets()
