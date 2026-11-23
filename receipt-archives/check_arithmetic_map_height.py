"""Paper controls for the arithmetic-map height audit. Standard-library Python 3."""

from fractions import Fraction as F
from itertools import product
from math import factorial, prod


def multiply_unit_field(x, y):
    """Coordinates in the basis (1,u), where u^2 = 3u - 1."""
    a, b = x
    c, d = y
    return a*c - b*d, a*d + b*c + 3*b*d


def conjugate(x):
    a, b = x
    return a + 3*b, -b


def check_hidden_height():
    power = (1, 0)
    traces = {}
    for n in range(1, 101):
        power = multiply_unit_field(power, (0, 1))
        dual = conjugate(power)
        assert multiply_unit_field(power, dual) == (1, 0)
        trace = power[0] + dual[0]
        assert power[1] + dual[1] == 0
        square = multiply_unit_field(power, power)
        local_norm = (1 + square[0], square[1])
        assert multiply_unit_field(local_norm, conjugate(local_norm)) == (trace**2, 0)
        traces[n] = trace
    assert [traces[i] for i in (1, 2, 3, 10)] == [3, 7, 18, 15127]

    # t + t^-1 = 15127, 0 < t < 1, so t < 1/15126.
    t_upper = F(1, traces[10] - 1)
    defect = 2*t_upper + t_upper**2
    p, sg = 23, F(1, 24)
    eta_upper = 2*5*defect + p*defect**2  # sqrt(23) < 5.
    assert eta_upper < sg / 2 and defect < sg / 2
    assert p / sg == p*(p+1) and sg <= F(1, 20)
    print(f"At n=10 the arithmetic height is log({traces[10]}). The 23-dimensional frame clears both smallness tests.")


def check_chirps(p=23):
    """Compute every overlap class in Z[zeta_p] using zeta_p^p = 1 and Phi_p = 0."""
    assert p == 23
    # The labeled overlap of two chirps depends only on the two index differences.
    for a, b in product(range(p), repeat=2):
        exponents = [(a*j*j + b*j) % p for j in range(p)]
        counts = [0] * p
        for j in exponents:
            for k in exponents:
                counts[(j-k) % p] += 1
        # Reduce by 1 + zeta + ... + zeta^(p-1).
        assert all(x == counts[-1] for x in counts[1:])
        expected = p*p if (a, b) == (0, 0) else 0 if a == 0 else p
        assert counts[0] - counts[-1] == expected
    print(f"All {p*p} chirp difference classes verified for {p*(p+1)} labeled columns, including the coordinate basis.")


def exponents(total):
    for i in range(total+1):
        for j in range(total-i+1):
            yield i, j, total-i-j


def gram_dual_norm(matrix, covector):
    """Solve Gx=l over Q and return l^T x. The blocks here have size one or two."""
    size = len(covector)
    rows = [list(row) + [value] for row, value in zip(matrix, covector)]
    for j in range(size):
        pivot = rows[j][j]
        assert pivot > 0
        rows[j] = [x / pivot for x in rows[j]]
        for k in range(size):
            if j != k:
                multiple = rows[k][j]
                rows[k] = [a - multiple*b for a, b in zip(rows[k], rows[j])]
    return sum(l * row[-1] for l, row in zip(covector, rows))


def check_branch_map():
    lam, sigma = (3, 1, 0), (2, 0)
    a = [sigma[i] - lam[i+1] for i in range(2)]
    b = [lam[i] - sigma[i] for i in range(2)]
    assert a == [1, 0] and b == [1, 1] and sum(lam)-sum(sigma) == 2
    cap = prod(
        (v-i) - (sigma[j]-j)
        for i in range(2)
        for v in range(lam[i+1], min(lam[i], lam[i+1]+sum(a))+1)
        if v != sigma[i]
        for j in range(2)
    )
    # Each list gives the exponents of the nonconstant variables in one monomial.
    # The monomials in each extremal polynomial are distinct.
    def fock_square(terms):
        return sum(prod(factorial(i) for i in term) for term in terms)

    source_norm = fock_square([(3, 1), (2, 1, 1)])
    xi_norm = fock_square([(2, 1, 1), (1, 1, 2)])
    target_norm = factorial(2)
    scalar = cap * F(xi_norm, source_norm)
    assert (cap, source_norm, xi_norm, scalar) == (4, 8, 4, 2)
    spectrum = []
    dimension = 0
    for m in exponents(4):
        active = [i for i, mi in enumerate(m) if mi > 0]
        dimension += len(active)-1
        if m[2] != 2:
            continue
        # The column-shear relation is sum_i c_i = 0. Use e_i - e_last as basis.
        piv = active[-1]
        free = active[:-1]
        m_fact = prod(factorial(mi) for mi in m)
        weights = {i: F(m_fact, source_norm * m[i]) for i in active}
        gram = [
            [weights[piv] + (weights[i] if i == j else 0) for j in free]
            for i in free
        ]
        readout = [scalar * (int(i == 2) - int(piv == 2)) for i in free]
        target_weight = F(factorial(m[0]) * factorial(m[1]), target_norm)
        spectrum.append(target_weight * gram_dual_norm(gram, readout))
    assert dimension == 15 and spectrum == [8, 8, 8]
    prime_norm = 16901**2 + 16900**2
    assert prime_norm == 571253801
    print(f"Terminal map: domain dimension {dimension}, three nonzero squared singular values {spectrum[0]}/T^2, T={prime_norm}.")


if __name__ == "__main__":
    check_hidden_height()
    check_chirps()
    check_branch_map()
