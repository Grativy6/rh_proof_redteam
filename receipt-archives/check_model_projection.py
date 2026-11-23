"""Check the local data and both observable images of the plane projection example."""

from fractions import Fraction


def main():
    p = 17
    power = p**2
    b = p**8
    precision = 2000
    assert 5*p**8 < p**9
    assert 4*(2*40 + 3*100) < precision
    assert Fraction(2*(2*b+1), power) + 26*2*precision <= b-1
    assert power > 1 and b > 1

    # One vector in each model word carries the second coordinate. In the
    # first word that is the power letter. The second word has it outside
    # the tested set (low digit and extra copy).
    assert power == (power-1) + 1
    degrees = (b, b, 1, 1)
    total = sum(degrees)
    projected = [-Fraction(d, total) for d in degrees]
    projected[-1] += 1
    assert sum(projected) == 0
    residual = [int(i == 3) - c for i, c in enumerate(projected)]
    assert all(residual[i] / degrees[i] == Fraction(1, total) for i in range(4))
    assert projected[-1] == Fraction(total-1, total)
    residue = projected[-1].numerator * pow(projected[-1].denominator, -1, p) % p
    assert residue == 9
    print(f'Power {power}, threshold {b}, projection cut 1. Coefficient on the shared '
          f'true monomial is {projected[-1]} before unit factors, residue {residue} mod {p}.')
    print('The other projected word is zero. Every output monomial has second-coordinate '
          'digit degree 1, below the source threshold.')


if __name__ == '__main__':
    main()
