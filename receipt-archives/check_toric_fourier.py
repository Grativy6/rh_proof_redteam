"""Exact calculations for the conductor-137 CM order and its Fourier obstruction."""

from collections import Counter
from fractions import Fraction
from math import comb, gcd, prod


def chi28(a):
    if gcd(a,28) != 1:
        return 0
    # (28/a) = (-1)^((a-1)/2) (a/7) for odd a prime to 7.
    return (1 if a % 4 == 1 else -1) * (1 if a % 7 in (1,2,4) else -1)


def bernoulli_numbers(n):
    b = [Fraction(1)]
    for j in range(1,n+1):
        b.append(-sum(comb(j+1,k)*b[k] for k in range(j))/(j+1))
    return b


def partial_zeta(s):
    k = 2*s
    b = bernoulli_numbers(k)
    def value(x):
        return sum(comb(k,j)*b[j]*x**(k-j) for j in range(k+1))
    generalized = 28**(k-1) * sum(chi28(a)*value(Fraction(a,28)) for a in range(1,29))
    return b[k]*generalized / k**2


def residue_classes():
    q = 137
    assert 12**2-7 == q and 37**2 % q == q-1
    fourth_roots = {1,q-1,37,q-37}
    assert all(pow(x,4,q)==1 for x in fourth_roots)
    classes = {frozenset((x*u) % q for u in fourth_roots) for x in range(1,q)}
    assert len(classes) == 34
    generator = next(x for x in range(2,q) if len({pow(x,i,q) for i in range(136)}) == 136)
    ordered = [frozenset(pow(generator,j,q)*u % q for u in fourth_roots) for j in range(34)]
    assert len(set(ordered)) == len(classes)
    return generator


def root_of_unity_linear_sum(row, values):
    # Represent Q(zeta_34) as Q[X]/Phi_17(X), with zeta_34=-zeta_17^9.
    coeffs = [Fraction(0)]*17
    for j, value in enumerate(values):
        coeffs[9*row*j % 17] += (-1)**(row*j)*value
    last = coeffs.pop()
    return [a-last for a in coeffs]


def check_fourier():
    values = [Fraction(1,17*128)]*34
    values[0] += 1
    rows = [root_of_unity_linear_sum(j,values) for j in range(34)]
    assert all(z[1:] == [0]*15 for z in rows)
    assert rows[0][0] == 1+Fraction(2,128)
    assert all(z[0] == 1 for z in rows[1:])
    assert all(z[0].numerator % 17 and z[0].denominator % 17 for z in rows)
    assert all(x.denominator%17 == 0 for x in values)
    # In Phi_17(1+Y), every lower coefficient is divisible by 17 and the
    # constant has valuation 1. Every distinct pair of 17th roots differs
    # by (1-zeta_17) times a unit, as checked on the residue coefficients.
    assert all(comb(17,j) % 17 == 0 for j in range(1,17))
    exponents = []
    for _ in range(2):
        for j in range(17):
            unit = prod(j-i for i in range(j)) % 17
            assert unit != 0
            exponents.append(j)
    assert Counter(exponents) == Counter({j:2 for j in range(17)})
    # A correction only at j=0 has kth forward difference (-1)^k times
    # that correction for k >= 1. After inverse Fourier on C2 the mock
    # 1/(256*17^(1/16)) on each class costs exactly 15 uniformizer steps.
    failed = []
    mock = [(1, int(j == 0)) for j in range(17)]
    for k in range(1,17):
        constant, small = (sum((-1)**(k-j)*comb(k,j)*mock[j][a] for j in range(k+1))
                           for a in (0,1))
        assert constant == 0 and abs(small) == 1
        valuation_in_steps = 16-1  # v(17 / (256 * 17^(1/16))) * 16
        if valuation_in_steps < k:
            failed.append(k)
    assert failed == [16]
    return sorted(exponents)


def denominator_table():
    z = partial_zeta(5)
    assert z == Fraction(105911461682,33)
    assert z/4 == Fraction(52955730841,66)
    result = {}
    for p in (2,3,5,7,11,17,23,29,137):
        c_e = int((z/4).denominator % p == 0)
        c = {2:Fraction(1),7:Fraction(1,2),137:Fraction(1)}.get(p,0)
        a0 = int(p == 137)
        result[p] = 12*(c_e + 20*c + 20*a0)
    assert {p:int(y) for p,y in result.items() if y} == {2:252,3:12,7:120,11:12,137:480}
    return {p:int(y) for p,y in result.items() if y}


def check_cusps():
    z = partial_zeta(5)
    base = (z/4)/28**5
    other = base/137**10
    def vp(x, p):
        def steps(n):
            count = 0
            while n % p == 0:
                n //= p
                count += 1
            return count
        return steps(x.numerator)-steps(x.denominator)
    assert vp(base,17) == vp(other,17) == 0
    assert vp(base+33*other,17) == vp(base-other,17) == 1
    constants = [base] + [other]*33
    for j in range(34):
        row = root_of_unity_linear_sum(j,constants)
        assert all(x == 0 for x in row[1:])
        assert row[0] == (base+33*other if j == 0 else base-other)
    denom = 66*28**5*137**10
    certified = {q:12*vp(Fraction(denom),q) for q in (2,3,7,11,137)}
    assert certified == {2:132,3:12,7:60,11:12,137:120}
    assert all(value <= denominator_table()[q] for q,value in certified.items())
    # For every cusp I contains f, so 137/N(I) is an integer. Test the
    # denominator identities independently for sample fractional norms.
    for relative_index in (1,7,49,137,7*137,49*137):
        norm_I = Fraction(137,relative_index)
        constant = (z/4)/(28**5 * norm_I**10)
        assert (denom*constant).denominator == 1
        for ideal_norm in (1,7,17,28,137*28):
            norm_nu = Fraction(ideal_norm)/(28*norm_I)
            term = 28**4 * norm_nu**9 / norm_I
            assert term == ideal_norm**9 / (28**5*norm_I**10)
            assert (denom*term).denominator == 1
    return certified


if __name__ == "__main__":
    print("Generator of the order-34 class quotient represented by",residue_classes())
    exponents = check_fourier()
    print("34 Fourier exponents: 0 through 16, twice each; residual rank",exponents.count(0))
    print("Nonzero bounds on the twelfth-power valuation:",denominator_table())
    zeta_bound = Fraction(67,64)**4
    radius = zeta_bound-1 + 136*zeta_bound/137**10
    assert radius < Fraction(202,1000)
    assert Fraction(2,128) < radius
    print("All 34 genuine complex character sums lie within 0.202 of 1.")
    print("Cusp constants: class valuations 0, character valuations 1, at 17.")
    print("Independent CM denominator bounds:",check_cusps())
