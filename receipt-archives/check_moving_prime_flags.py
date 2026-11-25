"""Check the local Frobenius character counts for the two moving primes.

Uses exact exponents for roots of unity. The two finite pairs test the host
congruences and both splitting behaviors at 7. The all-page argument and the
distinction from the global marked-point assertion are in the linked receipt.
"""

from math import gcd

from check_prime_window_readouts import legendre, prime_small


def dyadic_logs(m):
    modulus, order = 2 ** (m + 2), 2**m
    logs = {}
    for i in range(order):
        a = pow(5, i, modulus)
        logs[a] = logs[-a % modulus] = i
    assert len(logs) == 2 * order
    return logs


def test_pair(q, d):
    assert prime_small(q) and prime_small(d)
    assert q % 8 == 3 and d % 16 == 7 and (d + 1) % (105 * q) == 0
    assert (legendre(q, d), legendre(d, q)) == (1, -1)
    degrees = {p: (1 if legendre(p, 7) == 1 else 2) for p in (q, d)}
    assert degrees[d] == 2
    for m in range(2, 13):
        modulus, order = 2 ** (m + 2), 2**m
        logs = dyadic_logs(m)
        for ell, other in ((q, d), (d, q)):
            degree = degrees[ell]
            sign_exp = 0 if legendre(ell, other) == 1 else order // 2
            possible = set()
            for b in range(order):
                exponent = b * logs[ell % modulus] + sign_exp
                if degree * exponent % order == 0:
                    possible.add(b)
            max_order = degree if ell == q else 4
            expected = {b for b in range(order) if order // gcd(b, order) <= max_order}
            assert possible == expected
            if m == 12:
                print(
                    f"q={q}, d={d}, coefficient {ell}, residue degree {degree}: "
                    f"{len(possible)} surviving labels among {order}."
                )
    for ell in (q, d):
        degree = degrees[ell]
        for n in (1, 2, 5, 16):
            # The two controls agree through the indicated residue quotient.
            difference = pow(1 + ell**n, degree, ell ** (n + 1)) - 1
            assert difference == degree * ell**n
            for k in (1, n, n + 1, n + 2):
                modulus = ell**k
                kernel_size = gcd(pow(1 + ell**n, degree, modulus) - 1, modulus)
                assert kernel_size == ell ** min(k, n)
        for j in range(1, 31):
            weights = [j, 0, -j]
            gaps = [
                (i, k)
                for i in range(3)
                for k in range(3)
                if weights[i] - weights[k] == 1
            ]
            assert gaps == ([(0, 1), (1, 2)] if j == 1 else [])


if __name__ == "__main__":
    test_pair(67, 619079)
    test_pair(83, 209159)
