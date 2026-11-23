"""Exact arithmetic in Z[i, omega] for the two rank-four Hermitian lattices."""

import argparse
import ast
import hashlib
from pathlib import Path
import re
import tarfile
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import factorial

ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)
I = (0, 1, 0, 0)
OMEGA = (0, 0, 1, 0)
PI = (1, 1, 0, 0)
V4 = (1, 0, 2, 0)  # sqrt(-3) = 1 + 2*omega


def add(x, y):
    return tuple(a+b for a, b in zip(x, y))


def scale(x, n):
    return tuple(n*a for a in x)


def multiply(x, y):
    # Basis 1, i, omega, i*omega. Use i^2=-1 and omega^2=-omega-1.
    a, b, c, d = x
    e, f, g, h = y
    real, imag = c*g-d*h, c*h+d*g
    return (a*e-b*f-real, a*f+b*e-imag,
            a*g-b*h+c*e-d*f-real, a*h+b*g+c*f+d*e-imag)


def conjugate(x):
    a, b, c, d = x
    return (a-c, d-b, -c, d)


def divide_by_pi(x):
    a, b, c, d = x
    if (a+b) % 2 or (c+d) % 2:
        return None
    return ((a+b)//2, (b-a)//2, (c+d)//2, (d-c)//2)


def residue(x):
    a, b, c, d = x
    return (a+b) % 2 + 2*((c+d) % 2)


def norm_inner(x, y):
    total = ZERO
    for a, b in zip(x, y):
        total = add(total, multiply(conjugate(a), b))
    return total


def sharp_coordinates(B):
    """Coordinates of B/pi in the basis w, pi*e1, e3-e1, e4-bar(v4)*e1."""
    a = scale(B[1], -1)
    u = divide_by_pi(add(B[0], a))
    z = divide_by_pi(add(B[2], a))
    t = divide_by_pi(add(B[3], multiply(a, V4)))
    if u is None or z is None or t is None:
        return None
    b = divide_by_pi(add(add(u, scale(a,-3)), add(z, multiply(conjugate(V4), t))))
    return None if b is None else (a,b,z,t)


def roots_of_unity():
    return tuple(multiply(x, y)
                 for x in (ONE, I, scale(ONE,-1), scale(I,-1))
                 for y in (ONE, OMEGA, multiply(OMEGA,OMEGA)))


def norm_two_numerators():
    """Enumerate all y with h(y,y)=2, storing B=pi*y in integral coordinates."""
    units = roots_of_unity()
    assert len(set(units)) == 12 and all(multiply(u,conjugate(u)) == ONE for u in units)
    integral, fractional = set(), set()
    for k in range(4):
        for unit in units:
            B = [ZERO]*4
            B[k] = multiply(multiply(PI,PI), unit)
            integral.add(tuple(B))
    assert len(integral) == 48
    for k, l in combinations(range(4), 2):
        for u, v in product(units, repeat=2):
            B = [ZERO]*4
            B[k], B[l] = multiply(PI,u), multiply(PI,v)
            if sharp_coordinates(B) is not None:
                integral.add(tuple(B))
    for residue_class in (1,2,3):
        lifts = [u for u in units if residue(u) == residue_class]
        for B in product(lifts, repeat=4):
            if sharp_coordinates(B) is not None:
                fractional.add(B)
    assert (len(integral),len(fractional)) == (336,384)
    result = integral | fractional
    assert len(result) == 720
    assert all(norm_inner(B,B) == scale(ONE,4) for B in result)
    return result


def product_mod_pi(x, y):
    # Bit representation of F4, with bit 1 recording omega.
    poly = (x if y & 1 else 0) ^ (x << 1 if y & 2 else 0)
    return poly ^ 7 if poly & 4 else poly


def projective_key(B):
    reductions = tuple(map(residue, sharp_coordinates(B)))
    first = next(x for x in reductions if x)
    inverse = next(y for y in (1,2,3) if product_mod_pi(first,y) == 1)
    return tuple(product_mod_pi(x,inverse) for x in reductions)


def count_standard_neighbors():
    by_line = defaultdict(list)
    for B in norm_two_numerators():
        by_line[projective_key(B)].append(B)
    counts = []
    for vectors in by_line.values():
        remaining = set(vectors)
        while remaining:
            B = next(iter(remaining))
            group = {C for C in remaining if all(a % 4 == 0 for a in norm_inner(B,C))}
            assert B in group
            # The residue line and this congruence determine the same neighbor for
            # each member. Directly check every pair as a separate finite test.
            assert all(all(a % 4 == 0 for a in norm_inner(C,D))
                       for C,D in combinations(group, 2))
            counts.append(len(group))
            remaining -= group
    return counts, Counter(map(len, by_line.values()))


def bernoulli4(x):
    return x**4 - 2*x**3 + x**2 - Fraction(1,30)


def check_mass():
    standard = 12**4 * factorial(4)
    counts, line_sizes = count_standard_neighbors()
    assert counts == [48]*15
    departing = 2 * 3**3   # 27 full-support lines, two lifts per line
    other = standard * len(counts) // departing
    assert (standard, other) == (497664,138240)
    rank3_mass = Fraction(1,12**3*factorial(3))
    rank4_mass = Fraction(1,standard) + Fraction(1,other)
    bernoulli = sum(character*bernoulli4(Fraction(a,12))
                    for a,character in [(1,1),(5,-1),(7,-1),(11,1)])
    assert bernoulli == Fraction(-23,216)
    # Use the positive Euler values. Fourier expansion gives L(4,chi12)
    # in units of pi^4/sqrt(12); sqrt(12) cancels against d_F^(7/2).
    dirichlet_four = -Fraction(16, 2*factorial(4))*bernoulli
    expected = 12**3 * Fraction(6, 16)**2 * Fraction(1,90) * dirichlet_four
    assert rank4_mass/rank3_mass == expected == Fraction(23,240)
    def bernoulli3(x):
        return x**3 - Fraction(3,2)*x**2 + x/2
    beta_three = Fraction(2,3) * bernoulli3(Fraction(1,4))
    chi_three = Fraction(4,3) * bernoulli3(Fraction(1,3))
    # Here L(3,chi_-3) is chi_three*pi^3/sqrt(3).
    rank2_mass = Fraction(1,12**2*factorial(2))
    assert 2*12**2 * Fraction(2,8)**2 * beta_three * chi_three == rank3_mass/rank2_mass
    print("720 norm-two vectors, residue-line sizes:", dict(line_sizes))
    print("15 standard neighbors each contain 48 norm-one vectors.")
    print("Rank-four automorphism orders:", standard, other)
    print("Two class contributions relative to rank three:",
          Fraction(1,standard)/rank3_mass, Fraction(1,other)/rank3_mass)
    print("Rank-four to rank-three mass ratio:", expected)


def check_catalog(path):
    """Read the author's published class-number tables as data."""
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    assert digest == "4caf7463b3a84cefbec7626976186da0bb7b6af6d4c082a4eb3024987253c4a6"
    with tarfile.open(path, "r:bz2") as archive:
        data = archive.extractfile("res_herm.m").read().decode("ascii")
    for rank, class_number, index in [(3, 1, 9), (4, 2, 12)]:
        key = f"Result{rank}CN{class_number}:="
        raw = data.split(key, 1)[1].split(";", 1)[0].strip()
        assert re.fullmatch(r"[\s\d\[\]<>/,\-]+", raw)
        raw = raw.replace("<", "[").replace(">", "]")
        raw = re.sub(r"(-?\d+/\d+)", r"'\1'", raw)
        entry = ast.literal_eval(raw)[index-1]
        field, relative, forms = entry
        assert field == [-3,0,1] and relative == [[1,0],[0,0],[1,0]]
        form, basis = forms[0]
        expected = [[list(ONE if i == j else ZERO) for j in range(rank)] for i in range(rank)]
        assert form == [1,0] and basis == expected
        print(f"{key[:-2]} field entry {index} contains the standard rank-{rank} lattice.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--class-table", type=Path, help="Kirschmer's res_herm.tar.bz2")
    args = parser.parse_args()
    check_mass()
    if args.class_table:
        check_catalog(args.class_table)
