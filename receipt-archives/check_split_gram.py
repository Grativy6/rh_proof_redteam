"""Exact finite checks for the split Gram density. Run with standard Python 3."""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import prod


def direct_density(prime, level, rows, columns):
    """Count Gram matrices by adding one row outer product at a time."""
    modulus = prime**level
    vectors = list(product(range(modulus), repeat=columns))
    contributions = Counter(
        tuple(a * b % modulus for a in left for b in right)
        for left in vectors
        for right in vectors
    )
    zero = (0,) * (columns**2)
    counts = {zero: 1}
    for _ in range(rows):
        updated = Counter()
        for gram, count in counts.items():
            for addition, ways in contributions.items():
                new_gram = tuple((a + b) % modulus for a, b in zip(gram, addition))
                updated[new_gram] += count * ways
        counts = updated
    return Fraction(counts[zero] * modulus**(columns**2), modulus**(2 * rows * columns))


def rank_probability(q, rows, columns, rank):
    """Count rank-k maps by factorization through a k-dimensional space."""
    numerator = prod((q**rows - q**i) * (q**columns - q**i) for i in range(rank))
    bases = prod(q**rank - q**i for i in range(rank))
    return Fraction(numerator, bases * q**(rows * columns))


@lru_cache(maxsize=None)
def conditional_moment(q, rows, columns, weight, level):
    """Eliminate the invertible residue block and use a uniform Schur complement."""
    if level == 0 or columns == 0:
        return Fraction(1)
    total = Fraction(0)
    for rank in range(columns + 1):
        remaining = columns - rank
        moment = conditional_moment(q, rows - rank, remaining, weight, level - 1)
        total += rank_probability(q, rows, columns, rank) * q**(weight * remaining) * moment
    return total


def limit_density(q, rows, columns):
    if rows < 2 * columns:
        raise ValueError("This limit requires at least twice as many rows as columns.")
    return prod(
        (1 - Fraction(1, q**h)) / (1 - Fraction(1, q**(h - columns)))
        for h in range(rows - columns + 1, rows + 1)
    )


def main():
    comparisons = 0
    for q, level, columns, row_choices in (
        (2, 1, 2, (2, 3, 4, 5)),
        (3, 1, 2, (3, 4)),
        (2, 2, 2, (3, 4)),
        (2, 3, 1, (1, 2)),
        (3, 2, 1, (1, 2)),
        (5, 2, 1, (1, 2)),
    ):
        for rows in row_choices:
            counted = direct_density(q, level, rows, columns)
            predicted = conditional_moment(q, rows, columns, columns, level)
            assert counted == predicted, (q, level, rows, columns, counted, predicted)
            comparisons += 1

    for q in (2, 3, 5, 7):
        for level in range(1, 8):
            stable = 1 + Fraction(1, q) * (1 - Fraction(1, q**level))
            boundary = 1 + (1 - Fraction(1, q)) * level
            assert conditional_moment(q, 2, 1, 1, level) == stable
            assert conditional_moment(q, 1, 1, 1, level) == boundary
    for columns in (1, 2, 3, 6):
        limit = limit_density(5, 2 * columns, columns)
        masses = [conditional_moment(5, 2 * columns, columns, columns, n) for n in range(5)]
        assert all(a < b for a, b in zip(masses, masses[1:]))
        assert masses[-1] < limit
    print(f"{comparisons} direct finite-ring counts agree with the independent rank recurrence.")
    print("All 56 one-column identities and four increasing sequences agree with the formulas.")
    print("q=5, t=1, N=2: two rows give 149/125; one row gives 13/5.")


if __name__ == "__main__":
    main()
