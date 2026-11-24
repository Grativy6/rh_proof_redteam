"""Compute the two exact Bernoulli numbers and the Jacobi divisor exponents."""

from math import isqrt


def quadratic_character(p):
    assert p > 2 and all(p % i for i in range(2, isqrt(p) + 1))
    values = [-1] * p
    values[0] = 0
    for x in range(1, (p + 1) // 2):
        values[x * x % p] = 1
    return values


def readings(q):
    chi = quadratic_character(q)
    eta = quadratic_character(7)
    conductor = q * 7
    m0 = m1 = m2 = 0
    bins = [0] * 5
    for a in range(conductor):
        s = chi[a % q] * eta[a % 7]
        bins[a % 5] += s
        m0 += s
        m1 += s * a
        m2 += s * a * a
    bernoulli, rem = divmod(m2, conductor)
    assert m0 == m1 == rem == 0
    assert (
        bins == {2179: [-4, -34, -34, -4, 76], 106619: [-188, -70, -70, -188, 516]}[q]
    )
    assert (bins[1] - bins[0] - bernoulli) % 5 == 0
    print("Character sums by residue", bins)
    exponents = []
    for order in (25, 125):
        inverse = [pow(i, -2, order) if i % 5 else 0 for i in range(order)]
        f = q * order
        v = sum(chi[a % q] * inverse[a % order] for a in range(f // 2 + 1, f))
        exponents.append(v % order)
    return bernoulli, exponents


def main():
    for q, expected in ((2179, (166000, [0, 0])), (106619, (45958528, [0, 50]))):
        b, k = readings(q)
        assert (b, k) == expected
        print(
            f"q={q}, conductor={7 * q}, B2={b} (mod 5: {b % 5}), Jacobi exponents mod 25 and 125: {k}"
        )


if __name__ == "__main__":
    main()
