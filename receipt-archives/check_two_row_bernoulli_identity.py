"""Replay the two-row identity with one formal coefficient per residue mod f.

No Dirichlet-character values are substituted in the main test. Dictionaries
represent elements of the free Z[X]/(X^(S/2)+1)-module on residues modulo f.
"""

from collections import defaultdict


def row(level, size, conductor, representative):
    stride = level // (4 * size)
    generator = pow(5, stride, level)
    result = defaultdict(int)
    value = representative
    for j in range(size // 2):
        for x in range(value, conductor * level, level):
            result[j, x % conductor] += 1 if 2*x > conductor*level else -1
        value = value * generator % level
    return result


def shifted_difference(first, second, degree, power):
    result = defaultdict(int)
    for (j, residue), value in second.items():
        wrap, slot = divmod(j + power, degree)
        result[slot, residue] += -value if wrap % 2 else value
    for key, value in first.items():
        result[key] -= value
    return {key: value for key, value in result.items() if value}


def check_identity(e, f, n):
    size, level = 2**e, 2**n
    h = level // size
    assert f % 2 and h > size * f // 2 and h % size == 0
    sign = 1 if (size*f//2 + 1) % 4 == 1 else -1
    a = size*f//2 + sign
    other = h - size*f//2 + sign
    assert 0 < a < h and 0 < other < h
    assert a % 4 == other % 4 == 1 and (other-a) % size == 0
    assert (other-a-h) % f == 0
    stride = level // (4*size)
    c = (pow(5, stride, level) - 1) // h
    power = pow(a*c, -1, size)
    actual = shifted_difference(row(level,size,f,a), row(level,size,f,other), size//2, power)
    assert actual == {(0, sign % f): 2}, (e, f, n, actual)


def check_quartic_at_five():
    # phi has conductor 5, phi(2)=i and phi(-1)=-1. The dyadic character is even.
    level, f, degree = 64, 5, 8
    gaussian = {0: (0, 0), 1: (1, 0), 2: (0, 1), 4: (-1, 0), 3: (0, -1)}
    log = {}
    for j in range(2*degree):
        u = pow(5, j, level)
        log[u] = log[-u % level] = (j % degree, 1 if j < degree else -1)
    exact = [[0, 0] for _ in range(degree)]
    for x in range(1, f*level, 2):
        j, sign = log[x % level]
        for k, c in enumerate(gaussian[x % f]):
            exact[j][k] += x*sign*c
    for j in range(degree):
        a = pow(5, j, level)
        for k in range(2):
            signed = sum((1 if 2*x > f*level else -1)*gaussian[x % f][k]
                         for x in range(a, f*level, level))
            assert exact[j][k] == f*level*signed
            exact[j][k] = signed
    for root in (2, 3):
        coefficients = [(a+root*b) % 5 for a, b in exact]
        for beta in (2, 3):
            # At either primitive fourth root, reduce modulo X^4-beta.
            assert any((coefficients[j]+beta*coefficients[j+4]) % 5 for j in range(4))
    print("Quartic conductor 5: original numerator and both embeddings checked at level 64.")


def main():
    check_quartic_at_five()
    count = 0
    for e in range(2, 9):
        for f in range(1, 130, 2):
            # For f=1 the extra boundary has a quadratic shift, checked separately.
            minimum = max(2*e, (f*(2**(2*e-1)) - 1).bit_length())
            for n in range(minimum, minimum + 3):
                check_identity(e, f, n)
                count += 1
    assert count == 1365
    print(f"{count} exact two-row identities over the integers.")
    print("Covered odd conductors 1 through 129, e=2 through 8, three layers each.")
    print("Each difference has one surviving coefficient: twice the designated residue weight.")


if __name__ == "__main__":
    main()
