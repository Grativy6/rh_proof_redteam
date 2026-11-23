"""Exact checks for the four-place lattice example. Uses only Python's standard library."""

from itertools import combinations

P = 5
PRICE = 17
STEPS = 2
SITES = (1, 2, 3, 4)
SIZE = 8
AMBIENT_RANK = 32
BASE_COST = 8
PRECISION = len(SITES) * PRICE
MODULUS = P**PRECISION


def identity(size):
    return [[int(i == j) for j in range(size)] for i in range(size)]


def multiply(a, b, modulus):
    columns = list(zip(*b))
    return [[sum(x * y for x, y in zip(row, col)) % modulus for col in columns]
            for row in a]


def nilpotent_shift():
    return [[int(i + 1 == j) for j in range(SIZE)] for i in range(SIZE)]


def square_root_of_minus_one():
    root, precision = 2, 1
    while precision < PRECISION:
        precision = min(2 * precision, PRECISION)
        modulus = P**precision
        root = (root - (root * root + 1) * pow(2 * root, -1, modulus)) % modulus
    assert (root * root + 1) % MODULUS == 0
    return root


def positive_symmetric_lift(shift):
    root = square_root_of_minus_one()
    half = pow(2, -1, MODULUS)
    frame = [[0] * SIZE for _ in range(SIZE)]
    for i in range(SIZE // 2):
        j = SIZE - 1 - i
        frame[i][i], frame[j][i] = 1, root
        frame[i][j], frame[j][j] = half, -root * half % MODULUS
    # The Gram matrix is the matrix reversing the order of the basis vectors.
    inverse = list(reversed(list(zip(*frame))))
    assert multiply(inverse, frame, MODULUS) == identity(SIZE)
    matrix = multiply(multiply(frame, shift, MODULUS), inverse, MODULUS)
    for i in range(SIZE):
        matrix[i][i] += SIZE * MODULUS
    assert matrix == [list(row) for row in zip(*matrix)]
    assert all(row[i] > sum(abs(x) for j, x in enumerate(row) if j != i)
               for i, row in enumerate(matrix))
    return matrix


def paid_columns(block):
    """List the actual weighted subset products on the eight-dimensional summand."""
    powers = {}
    for unit in SITES:
        operator = [[unit * x % MODULUS for x in row] for row in block]
        power = identity(SIZE)
        for _ in range(STEPS):
            power = multiply(power, operator, MODULUS)
        powers[unit] = power
    columns = []
    for count in range(len(SITES) + 1):
        for subset in combinations(SITES, count):
            word = identity(SIZE)
            for unit in subset:
                word = multiply(word, powers[unit], MODULUS)
            price = P ** ((len(SITES) - count) * PRICE)
            columns.extend([[price * x % MODULUS for x in col] for col in zip(*word)])
    return columns


def smith_exponents(columns, dimension, precision):
    """Elementary row/column elimination over Z/(p^precision), with capped exponents."""
    modulus = P**precision

    def valuation(x):
        if x == 0:
            return precision
        n = 0
        while x % P == 0:
            x //= P
            n += 1
        return n

    rows = [[x % modulus for x in row] for row in zip(*columns)]
    assert len(rows) == dimension
    result = []
    while rows:
        order, i, j = min((valuation(x), i, j) for i, row in enumerate(rows)
                          for j, x in enumerate(row))
        if order == precision:
            return result + [precision] * len(rows)
        rows[0], rows[i] = rows[i], rows[0]
        divisor = P**order
        inverse_unit = pow(rows[0][j] // divisor, -1, modulus)
        first = [x * inverse_unit % modulus for x in rows[0]]
        remaining = []
        for row in rows[1:]:
            factor = row[j] // divisor
            remaining.append([(x - factor * y) % modulus
                              for col, (x, y) in enumerate(zip(row, first)) if col != j])
        # The pivot divides its whole row. Clearing that row with column operations
        # leaves this remaining block unchanged since the pivot column is now zero below.
        rows = remaining
        result.append(order)
    return result


def main():
    shift = nilpotent_shift()
    expected = sorted(i * PRICE for i in range(1, 5) for _ in range(STEPS))
    for label, block in [('shift', shift), ('positive symmetric', positive_symmetric_lift(shift))]:
        rank_mod_p = sum(e == 0 for e in smith_exponents(list(zip(*block)), SIZE, 1))
        assert rank_mod_p + AMBIENT_RANK - SIZE == 31
        exponents = smith_exponents(paid_columns(block), SIZE, PRECISION)
        assert exponents == expected
        length = (AMBIENT_RANK - SIZE) * BASE_COST + sum(max(e, BASE_COST) for e in exponents)
        rank_only_bound = AMBIENT_RANK * BASE_COST + 2 * PRICE * STEPS * len(SITES)
        assert (length, rank_only_bound) == (532, 528)
        print(f'{label}: raw block exponents {exponents}, length {length}, rank-only bound {rank_only_bound}')


if __name__ == '__main__':
    main()
