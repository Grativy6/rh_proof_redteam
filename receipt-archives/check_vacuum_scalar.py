"""Integer checks for the discriminant -439 vacuum-normalization example."""

from itertools import combinations, product
from math import gcd, isqrt


def mul(x, y):
    """Integral basis 1,w with w=(1+sqrt(-439))/2 and w^2=w-110."""
    a, b = x
    c, d = y
    return a*c-110*b*d, a*d+b*c+b*d


def conjugate(x):
    a, b = x
    return a+b, -b


def norm(x):
    a, b = mul(x, conjugate(x))
    assert b == 0
    return a


def det(x, y):
    return x[0]*y[1]-x[1]*y[0]


def index(generators):
    result = 0
    for a, b in combinations(generators, 2):
        result = gcd(result, abs(det(a, b)))
    return result


def principal_generators(x):
    return x, mul((0, 1), x)


def same_as_principal(generators, x):
    a, b = principal_generators(x)
    volume = det(a, b)
    assert volume > 0
    # Containment by Cramer's rule, then equality by the integer index.
    assert all(det(t, b) % volume == 0 and det(a, t) % volume == 0 for t in generators)
    assert index(generators) == volume


def main():
    assert all(439 % k for k in range(2, isqrt(439)+1))
    assert 439 % 16 == 7 and 440 % 11 == 0
    assert [r for r in range(13) if (r*r-r+110) % 13 == 0] == [5, 9]

    prime = ((13, 0), (-5, 1))
    conjugate_prime = tuple(conjugate(x) for x in prime)
    same_as_principal([mul(a, b) for a, b in product(prime, conjugate_prime)], (13, 0))
    alpha = (19, 4)  # 21+2sqrt(-439)
    cube = [mul(mul(a, b), c) for a, b, c in product(prime, repeat=3)]
    same_as_principal(cube, alpha)
    assert norm(alpha) == 13**3
    # 4*norm(a+b*w) = (2a+b)^2+439*b^2 exhausts this norm equation.
    solutions = set()
    for b in range(-isqrt(4*169//439), isqrt(4*169//439)+1):
        left = 4*169-439*b*b
        k = isqrt(left)
        if k*k == left:
            for z in (k, -k):
                if (z-b) % 2 == 0:
                    solutions.add(((z-b)//2, b))
    assert solutions == {(-13, 0), (13, 0)}
    gamma = (3, 2)  # 4+sqrt(-439)
    assert norm(gamma) == 13*5*7
    assert (gamma[0]+5*gamma[1]) % 13 == 0 and (gamma[0]+9*gamma[1]) % 13 != 0
    assert (alpha[0]+5*alpha[1]) % 13 == 0 and (alpha[0]+9*alpha[1]) % 13 != 0
    aa, bb = mul(alpha, alpha)
    assert 2*aa+bb == -2630  # Trace of alpha^2; alpha/bar(alpha) = alpha^2/2197.
    print("p*pbar=(13), p^3=(21+2sqrt(-439)), and the only elements of norm 169 are +/-13.")
    print("The split local basis has norm numerator 455. The correcting root satisfies 2197*X^12+2630*X^6+2197=0.")


if __name__ == "__main__":
    main()
