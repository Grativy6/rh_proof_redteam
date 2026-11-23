"""Check the two scalar tests with integer arithmetic and no third-party packages."""

from collections import defaultdict
from fractions import Fraction
from math import comb, factorial, prod


def vp_positive(n, p):
    if n <= 0:
        raise ValueError("valuation input must be positive")
    value = 0
    while n % p == 0:
        n //= p
        value += 1
    return value


def factorial_vp(n, p):
    value = 0
    while n:
        n //= p
        value += n
    return value


def true_polynomial(M, N, P, shared_direction):
    """Expand in the true coordinates x1,x2,t1,t2,z1,z2,z'1,z'2."""
    coefficients = defaultdict(int)
    for i in range(M + 1):
        for side in range(2):
            for k in range(N + 1):
                for z2 in (range(N + 1) if shared_direction else [k]):
                    exponents = (M-i, i, i+P*k, M-i+1+P*(N-k),
                                 N-z2+1-side, z2+side, side, 1-side)
                    c = (-1)**(i+side) * comb(M, i) * comb(N, k)
                    c *= comb(N, z2) if shared_direction else (-1)**k
                    coefficients[exponents] += c
    return dict(coefficients)


def fock(first, second):
    return sum(c * second.get(m, 0) * prod(factorial(j) for j in m)
               for m, c in first.items())


def moment_formulas(M, N, P):
    D = P*N + 1
    C = factorial(M) * (factorial(D+M+1) // factorial(D+1)) * (N+2)
    b = [factorial(P*j) // factorial(j) for j in range(N+1)]
    raw = [b[k] * b[N-k] * (P*(N-k)+1) for k in range(N+1)]
    common = C * factorial(N)**2
    survivor = common * sum(raw)
    lost = common * sum((-1)**k * comb(N, k) * raw[k] for k in range(N+1))
    if N % 2 == 0:
        symmetric = sum((-1)**k * comb(N, k) * b[k] * b[N-k] for k in range(N+1))
        assert 2*lost == common * (2+P*N) * symmetric
    return survivor, lost


def check_finite_cases():
    for P, M, N in [(5, 1, 2), (5, 2, 3), (5, 3, 6), (7, 2, 8)]:
        source = true_polynomial(M, N, P, False)
        test = true_polynomial(M, N, P, True)
        survivor, lost = moment_formulas(M, N, P)
        assert survivor == fock(source, source)
        assert lost == fock(source, test)
        if N % 2 == 0:
            assert lost > 0
    assert moment_formulas(1, 2, 5)[1] == 4492800000
    # Check cancellation after extracting the common factorial valuation.
    for p in [5, 7, 11]:
        for N in range(2, 15, 2):
            b = [factorial(p*j) // (factorial(j) * p**j) for j in range(N+1)]
            assert all(vp_positive(x, p) == 0 for x in b)
            alternating = sum((-1)**k * comb(N, k) * b[k]*b[N-k] for k in range(N+1))
            assert alternating > 0 and alternating % p**(N//2) == 0
            if N % p == 0:
                assert sum(b[k]*b[N-k]*(p*(N-k)+1) for k in range(N+1)) % p
    # Check the balanced norm by enumerating every occupied true coefficient.
    for p, M, N in [(5, 10, 10), (7, 14, 14)]:
        D = M + p*N + 1
        twice_n0 = sum(factorial_vp(d, p) for d in (M, N+1, 1, D))
        coefficients = true_polynomial(M, N, p, False)
        twice_e = min(2*vp_positive(abs(a), p) + sum(factorial_vp(j, p) for j in m)
                      for m, a in coefficients.items())
        assert twice_e == twice_n0


def check_release_parameters():
    p = P = 79
    M = N = 79000
    c, slack = 1000, 54001
    D = P*N+1
    degrees = [M, N+1, 1, D+M, 0, 0, 0]
    chain_cut = N+1-slack
    assert M-60*c > 0
    assert chain_cut == 25000 and chain_cut-12*c == 13000
    for total in (M, N+2):
        assert 2*Fraction(total, P)+52*c <= slack
    assert p**3 < 2*sum(degrees)+2 < p**4
    bounds = [3, 3, 1, 4, 1, 1, 1]
    assert all(degree+2 < p**b for degree,b in zip(degrees,bounds))
    assert 2*sum(b+1 for b in bounds) == 42
    assert 4*(80+3*42) < c
    assert factorial_vp(D+M, p) == factorial_vp(M, p) + factorial_vp(P*N, p)
    twice_n0 = sum(factorial_vp(n, p) for n in degrees)
    common_v = (factorial_vp(M, p) + factorial_vp(D+M+1, p) - factorial_vp(D+1, p)
                + vp_positive(N+2, p) + 2*factorial_vp(N, p) + N)
    assert twice_n0 == common_v == 83048
    assert N % (2*p) == 0 and (1+P*N//2) % p == 1
    n0 = twice_n0 // 2
    return n0, n0+N//2, n0+c, n0+41


if __name__ == "__main__":
    check_finite_cases()
    n0, before, error, detection = check_release_parameters()
    print("Four direct true-polynomial expansions agree with the independent factorial formulas.")
    print("Smallest even example has nonzero pairing 4492800000.")
    print(f"Surviving value has valuation {n0}. The lost value has valuation at least {before}.")
    print(f"The required error threshold is below {error}. A detecting input must be below {detection}.")
