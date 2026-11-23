"""Evaluate the released two-row localiser at a transverse point modulo w^4, w^2=17."""

from collections import Counter

P = 17
MODULUS = P**2
Q = P**8


def multiply(x, y):
    a, b = x
    c, d = y
    return ((a * c + P * b * d) % MODULUS, (a * d + b * c) % MODULUS)


def power(x, n):
    value = (1, 0)
    while n:
        if n % 2:
            value = multiply(value, x)
        x = multiply(x, x)
        n //= 2
    return value


def order(x):
    def p_order(n):
        if n == 0:
            return 2
        return int(n % P == 0)

    return min(2 * p_order(x[0]), 1 + 2 * p_order(x[1]), 4)


def factor(constant):
    a, b = power((constant % MODULUS, 1), Q - 1)
    return ((1 - a) % MODULUS, -b % MODULUS)


def main():
    orders = Counter()
    for a in range(P):
        for b in range(P):
            first_row = pow(a + b, P**2, MODULUS)
            swapped = (factor(b - first_row), factor(b))
            value = order(multiply(*swapped))
            assert value == int(a != 0) + int(b != 0)
            orders[value] += 1
    assert orders == {0: 1, 1: 32, 2: 256}
    print(f'Orders on {P**2} graph matrices with entries in F_{P}: {dict(sorted(orders.items()))}.')


if __name__ == '__main__':
    main()
