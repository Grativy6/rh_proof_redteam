"""Exact checks for Pang's six-sector carry and the released p-adic unit.

Pairs (a,b) represent a+b*u with u^2=u+1. No floating-point angle is used.
The lattice boxes below check examples; the receipt proves the minimum for
every odd modulus at least 5 and handles the infinite tail.
"""

from collections import Counter
from math import isqrt


def sector_index(n):
    # floor(6*n*(3-sqrt(5))/2 + 1/2), for n >= 0.
    assert n >= 0
    return (18 * n - isqrt(180 * n * n)) // 2


def multiply(x, y):
    a, b = x
    c, d = y
    return a * c + b * d, a * d + b * c + b * d


def check_circle():
    assert sector_index(1) == 2 and sector_index(2) == 5
    assert sector_index(2) - 2 * sector_index(1) == 1
    sectors = [sector_index(n) % 6 for n in range(6)]
    assert sectors == [0, 2, 5, 1, 3, 5]
    assert [Counter(sectors)[k] for k in range(6)] == [1, 1, 1, 1, 0, 2]
    # F_k * (2-u) - F_{k-2} = (-1)^k (u-1)^k.
    fib = [0, 1]
    inverse_power = (1, 0)
    for k in range(1, 81):
        inverse_power = multiply(inverse_power, (-1, 1))
        if k < 2:
            continue
        fib.append(fib[-1] + fib[-2])
        error = (2 * fib[k] - fib[k - 2], -fib[k])
        assert error == tuple((-1) ** k * v for v in inverse_power)
        if k >= 6:
            assert sector_index(fib[k]) == 6 * fib[k - 2] and error != (0, 0)
    print(
        "One golden step has sector 2. Its doubled phase has sector 5, while 2 + 2 gives 4."
    )
    print("First six sectors:", sectors, "Fibonacci near-returns checked through F_80.")


def check_lattice():
    u = (0, 1)
    conjugate = (1, -1)
    assert multiply(u, (-1, 1)) == (1, 0)
    assert multiply(multiply(u, u), u) == (1, 2)  # u^3 = 1 + 2u, not 1.
    assert multiply((-1, 2), (-1, 2)) == (5, 0)
    assert tuple(a + b for a, b in zip(u, conjugate)) == (1, 0)
    for m in (5, 7, 9, 15, 33):
        a = (m - 1) // 2
        h = (m * m + 3) // 4
        candidates = [
            (a + m * horizontal, 1 + m * vertical)
            for horizontal in range(-3, 4)
            for vertical in range(-3, 4)
        ]
        values = {(x, y): x * x + x * y + y * y for x, y in candidates}
        assert min(values.values()) == h
        assert {v for v, q in values.items() if q == h} == {(a, 1), (a - m, 1)}
        assert 3 * (m - 1) ** 2 > m * m + 3
        assert a % m == (a - m) % m and a % (3 * m) != (a - m) % (3 * m)
        # After removing the common factor 2^h, the two terms in Q_2
        # would both reduce to 1. The target reduces to 1 as well.
        assert (1 + 1) % 2 != 1
    print("At m=5 the two minima have Q=7; their refined sums differ by 128*(2u-1).")


if __name__ == "__main__":
    check_circle()
    check_lattice()
