"""Small exact counts for the two auxiliary levels in Q(zeta_12)."""

from fractions import Fraction
from itertools import product
from math import factorial, prod


def framed_orbits(orders, shift):
    """Cyclically label each residue multiplicative group and count orbits."""
    representatives = set(product(*(range(n) for n in orders)))
    sizes = set()
    count = 0
    while representatives:
        initial = next(iter(representatives))
        point = initial
        size = 0
        while point in representatives:
            representatives.remove(point)
            point = tuple((a+b) % n for a,b,n in zip(point,shift,orders))
            size += 1
        assert point == initial
        sizes.add(size)
        count += 1
    assert sizes == {12}
    return count


def unitriangular_index(residue_size, rank):
    return prod(residue_size**j-1 for j in range(1,rank+1))


def check_count():
    assert {x for x in range(13) if (x**4-x*x+1) % 13 == 0} == {2,6,7,11}
    assert len([x for x in range(37) if (x**4-x*x+1) % 37 == 0]) == 4
    assert 5 % 12 == 5 and all((x*x-3) % 5 for x in range(5))
    assert all((x**4-x*x+1) % 5 for x in range(5))
    assert (5**2-1) % 12 == 0
    assert 3**2 + 2**2 == 13 and 144 == 12**2
    split = framed_orbits((12,12,36,36),(1,5,3,15))
    mixed = framed_orbits((24,12,12),(2,1,5))
    assert split == 15552 and mixed == 288
    erroneous = (5-1)**2 * (13-1)**2 // 12
    assert erroneous == 192
    index = (unitriangular_index(13,4)*unitriangular_index(37,4))**2
    stabilizers = (12**4 * factorial(4),138240)
    assert all(index % n == 0 for n in stabilizers)
    fiber1, fiber2 = (index//n for n in stabilizers)
    assert Fraction(fiber2,fiber1+fiber2) == Fraction(18,23)
    print("Split rank-one levels:",split,"classes, each orbit of size 12.")
    print("Mixed rank-one levels:",mixed,"classes. Treating 5 as split over Q gives",erroneous)
    print("Rank-four class contributions to the fully framed count:",fiber1,fiber2)


if __name__ == "__main__":
    check_count()
