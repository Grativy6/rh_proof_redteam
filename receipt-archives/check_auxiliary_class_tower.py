"""Exact Bernoulli norms for the first two layers in the class-tower proof.

Uses only the Python standard library. Each orbit is indexed by the exponent
of the order-five character of conductor w, with the wild character fixed.
"""

from math import gcd


def log_table(modulus, generator):
    logs = {}
    value = 1
    while value not in logs:
        logs[value] = len(logs)
        value = value * generator % modulus
    return logs


def quadratic_character(value):
    """The primitive character of discriminant -35 is (value/5)(value/7)."""
    at_five = pow(value, 2, 5)
    at_seven = pow(value, 3, 7)
    if not at_five or not at_seven:
        return 0
    return (1 if at_five == 1 else -1) * (1 if at_seven == 1 else -1)


def determinant(columns):
    """Fraction-free elimination on an integer matrix specified by columns."""
    rows = [list(row) for row in zip(*columns, strict=True)]
    size = len(rows)
    sign = 1
    previous = 1
    for k in range(size - 1):
        if not rows[k][k]:
            pivot = next((i for i in range(k + 1, size) if rows[i][k]), None)
            if pivot is None:
                return 0
            rows[pivot], rows[k] = rows[k], rows[pivot]
            sign = -sign
        diagonal = rows[k][k]
        for i in range(k + 1, size):
            for j in range(k + 1, size):
                term = diagonal * rows[i][j] - rows[i][k] * rows[k][j]
                rows[i][j], remainder = divmod(term, previous)
                assert not remainder
            rows[i][k] = 0
        previous = diagonal
    return sign * rows[-1][-1]


def cyclotomic_norm(coefficients, conductor):
    """Multiplication determinant for sum(coefficients[j] * zeta**j)/conductor."""
    order = len(coefficients)
    step = order // 5
    degree = 4 * step
    columns = []
    for power in range(degree):
        col = coefficients[-power:] + coefficients[:-power] if power else coefficients[:]
        # Phi_order(X) = 1 + X^step + ... + X^(4*step).
        for i in range(step):
            high = col[degree + i]
            for j in range(4):
                col[i + j * step] -= high
        columns.append(col[:degree])
    result, remainder = divmod(determinant(columns), conductor**degree)
    assert not remainder
    return result


def orbit_norms(w, generator, layer):
    order = 5**layer
    wild_modulus = 5 * order
    wild = log_table(wild_modulus, 2)
    tame = log_table(w, generator)
    assert len(wild) == 4 * order and len(tame) == w - 1
    norms = []
    for a in range(5):
        conductor = 7 * wild_modulus * (w if a else 1)
        totals = [0] * order
        for value in range(1, conductor):
            if gcd(value, conductor) != 1:
                continue
            exponent = wild[value % wild_modulus]
            if a:
                exponent += a * (order // 5) * tame[value % w]
            totals[exponent % order] += value * quadratic_character(value)
        norms.append(cyclotomic_norm(totals, conductor))
    return norms


def five_valuation(number):
    assert number
    result = 0
    while number % 5 == 0:
        number //= 5
        result += 1
    return result


def main():
    first = orbit_norms(11, 2, 1)
    assert first == [256, 403280, 27280, 43280, 4400]
    print("First layer at 11, exact five norms:", first)
    for w, root, expected in [(11, 2, [0, 1, 1, 1, 2]), (211, 2, [0, 1, 2, 1, 1])]:
        for layer, values in [(1, expected), (2, [0, 1, 1, 1, 1])]:
            norms = first if (w, layer) == (11, 1) else orbit_norms(w, root, layer)
            valuations = [five_valuation(v) for v in norms]
            assert valuations == values
            print(f"w={w}, layer={layer}, norm valuations={valuations}")
    print("All finite checks passed.")


if __name__ == "__main__":
    main()
