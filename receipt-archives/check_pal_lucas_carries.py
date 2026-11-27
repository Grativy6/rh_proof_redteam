"""Replay the 385-bit Lucas example with 32-bit digits and bounded 64-bit intermediates."""

import json

from check_release_prime_large import A, B, T

BASE = 1 << 32
WORD_MAX = (1 << 64) - 1


def digits(n):
    result = []
    while n:
        n, r = divmod(n, BASE)
        result.append(r)
    return result


def integer(value):
    out = 0
    for digit in reversed(value):
        out = BASE * out + digit
    return out


def trim(value):
    while value and value[-1] == 0:
        value.pop()
    return value


def ge(left, right):
    if len(left) != len(right):
        return len(left) > len(right)
    return left[::-1] >= right[::-1]


def subtract(left, right):
    borrow = 0
    out = []
    for i, digit in enumerate(left):
        owing = (right[i] if i < len(right) else 0) + borrow
        borrow = int(digit < owing)
        out.append(digit + borrow * BASE - owing)
    assert borrow == 0
    return trim(out)


def product(left, right, stats):
    result = [0] * (len(left) + len(right))
    for i, x in enumerate(left):
        carry = 0
        for j, y in enumerate(right):
            total = x * y + result[i + j] + carry
            assert 0 <= total <= WORD_MAX
            stats["greatest_inner_sum"] = max(stats["greatest_inner_sum"], total)
            carry, result[i + j] = divmod(total, BASE)
            stats["nonzero_partial_carries"] += int(carry != 0)
        assert result[i + len(right)] == 0
        result[i + len(right)] = carry
    stats["digit_products"] += 1
    return trim(result)


def remainder(value, modulus):
    """Binary long division with a bounded one-bit carry through the digit list."""
    result = []
    for word in reversed(value):
        for bit in range(31, -1, -1):
            carry = (word >> bit) & 1
            for j, x in enumerate(result):
                total = 2 * x + carry
                carry, result[j] = divmod(total, BASE)
            if carry:
                result.append(carry)
            if ge(result, modulus):
                result = subtract(result, modulus)
    return result


def replay():
    factors = (2, 3, 571, 599, A, B)
    exponents = [T - 1, *[(T - 1) // p for p in factors]]
    stats = {"greatest_inner_sum": 0, "nonzero_partial_carries": 0, "digit_products": 0}
    mod = digits(T)
    ladder = [[5]]
    for _ in range(max(exponents).bit_length() - 1):
        last = ladder[-1]
        ladder.append(remainder(product(last, last, stats), mod))
    answers = []
    for e in exponents:
        answer = [1]
        for bit, square in enumerate(ladder):
            if (e >> bit) & 1:
                answer = remainder(product(answer, square, stats), mod)
        v = integer(answer)
        assert v == pow(5, e, T)
        answers.append(str(v))
    assert answers[0] == "1" and all(v != "1" for v in answers[1:])
    first = next(i for i, v in enumerate(ladder) if len(v) > 2)
    z = integer(ladder[first])
    carry, low = divmod(z, 2**64)
    assert (first, z, carry, low) == (5, 5**32, 1262, 3273344365508751233)
    dropped = pow(5, T - 1, 2**64)
    assert dropped == 5625304617532669953
    return {
        "base": 5,
        "modulus_bit_length": T.bit_length(),
        "stored_32_bit_digits": len(mod),
        "binary_ladder_first_value_over_64_bits": {
            "index": first,
            "exponent": 2**first,
            "whole": str(z),
            "high_64_bit_digit": carry,
            "low_64_bit_digit": str(low),
        },
        "dropping_intermediate_high_digits_at_every_product": str(dropped),
        "exact_residue_at_full_exponent": answers[0],
        "order_factor_tests": {str(p): v for p, v in zip(factors, answers[1:])},
        "bounded_multiply_run": stats,
        "maximum_allowed_inner_sum": str(WORD_MAX),
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2))
