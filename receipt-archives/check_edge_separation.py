"""Check the residue-field part of the binary edge calculation at p=17."""

from collections import deque

P = 17
Q = P * P
ZERO = (0, 0)
ONE = (1, 0)


def multiply(x, y):
    # F_289 = F_17[t]/(t^2 - 3).
    a, b = x
    c, d = y
    return ((a * c + 3 * b * d) % P, (a * d + b * c) % P)


def power(x, exponent):
    result = ONE
    while exponent:
        if exponent % 2:
            result = multiply(result, x)
        x = multiply(x, x)
        exponent //= 2
    return result


def separates_with_degrees(a, b):
    # The highest monomial is the only one nonzero at infinity. On F_q^times
    # its character must reappear at a positive lower exponent to cancel it.
    highest = a + P * b
    return any(0 < i + P * j < highest and (highest - i - P * j) % (Q - 1) == 0
               for i in range(a + 1) for j in range(b + 1))


def shortest_digit_collision(prime, field_degree, slots):
    modulus = prime**field_degree - 1
    increments = [prime**s for s in slots]
    queue = deque([(0, 0)])
    seen = {0}
    while queue:
        residue, length = queue.popleft()
        for increment in increments:
            target = (residue + increment) % modulus
            if target == 0:
                return length + 1
            if target not in seen:
                seen.add(target)
                queue.append((target, length + 1))
    raise AssertionError("The cyclic group must contain a nonempty return path.")


def main():
    assert pow(3, (P - 1) // 2, P) == P - 1
    for a in range(P):
        for b in range(P):
            t = (a, b)
            sigma = power(t, P)
            assert sigma == (a, -b % P)
            product = multiply(power(t, P - 1), power(sigma, P - 1))
            difference = ((product[0] - 1) % P, product[1])
            assert multiply(t, difference) == ZERO
    # The value at infinity is 1, since both X coordinates there vanish.
    assert multiply(ONE, multiply(power(ONE, P - 1), power(ONE, P - 1))) == ONE
    first = 2 * (P - 1) + 1
    for total in range(first):
        assert not any(separates_with_degrees(a, total - a) for a in range(total + 1))
    pairs = [(a, first - a) for a in range(first + 1) if separates_with_degrees(a, first - a)]
    assert pairs == [(16, 17), (17, 16)]
    for prime, degree, slots in [(5, 4, (0, 1)), (5, 4, (0, 2)),
                                 (5, 4, (0, 1, 3)), (17, 2, (0, 1))]:
        ends = (*slots[1:], degree)
        predicted = sum(prime**(b - a) - 1 for a, b in zip(slots, ends))
        assert shortest_digit_collision(prime, degree, slots) == predicted
    required = Q * (16 - 2)
    assert required == 4046 and (required - 1) // Q == 13
    print(f'{Q} competing points checked. First total degree {first}, bidegrees {pairs}.')
    print(f'Single-factor degree {required - 1}: gap at most 13, required gap 14.')


if __name__ == '__main__':
    main()
