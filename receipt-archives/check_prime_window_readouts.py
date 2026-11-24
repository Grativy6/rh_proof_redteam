"""Exact controls for the arithmetic window. Python standard library only.

All ramp identities are checked coefficient by coefficient in formal log(p).
The two large d's are certified by short modular exponentiations.
"""
from fractions import Fraction
from math import gcd, isqrt


def prime_small(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % k for k in range(3, isqrt(n) + 1, 2))


def legendre(n, p):
    v = pow(n, (p - 1) // 2, p)
    if v == p - 1:
        return -1
    assert v in (0, 1)
    return v


def log_interval(n, terms=14):
    # log n = 2 atanh((n-1)/(n+1)); bound every denominator in the remainder below.
    x = Fraction(n - 1, n + 1)
    lower = 2 * sum(x**(2*j + 1) / (2*j + 1) for j in range(terms))
    upper = lower + 2*x**(2*terms+1) / ((2*terms+1)*(1-x*x))
    return lower, upper


def certify_window_primes():
    y = 2**40
    q = 3
    r = 2**521 - 1
    assert prime_small(521)
    residue = 4
    for _ in range(519):
        residue = (residue*residue - 2) % r
    assert residue == 0  # The proof of this primality test is in the receipt.
    l2, u2 = log_interval(2)
    l3, u3 = log_interval(3)
    assert Fraction(69, 100) < l2 < u2 < Fraction(7, 10)
    assert 1 < l3 < u3 < Fraction(11, 10)
    zlo, zhi = Fraction(11, 10), Fraction(111, 100)
    assert zlo**55 < 2**8 < zhi**55  # z = y^(1/275) for epsilon = 1/55
    assert zhi/2 < l3 < u3 < zlo and q % 8 == 3
    primes = []
    for j in (138, 1078):
        c = 2**197 + 21 + 24*j
        d = 2*c*r + 1
        assert r*r > d and gcd(2, d) == 1
        assert pow(2, d-1, d) == 1 and gcd(pow(2, 2*c, d)-1, d) == 1
        assert 2**719 < d < 2**720 and d % 16 == 7 and (d+1) % q == 0
        assert zhi*(40*u2)**2/2 < 719*l2 and 720*u2 < zlo*(40*l2)**2
        # z < 1.11 leaves the small odd-prime divisibility clause empty.
        primes.append(d)
    m = y + 15
    assert prime_small(m) and y <= m-1 < m+1 <= y*y
    signs = [legendre(m, d) for d in primes]
    assert signs == [-1, 1] and legendre(m, q) == 1
    print(f"Two certified WinPairs at Y=2^40; at m={m} the d-character signs are {signs}.")
    return primes


def prime_powers(end):
    terms = []
    for p in range(2, end + 1):
        if prime_small(p):
            n = p
            while n <= end:
                terms.append((n, p))
                n *= p
    return terms


def check_ramp():
    # Each coordinate is the coefficient of log(p), with exact rational breakpoints.
    terms = prime_powers(360)
    primes = sorted({p for _, p in terms})
    for modulus in (3, 7, 23):
        for y, h in ((18, 1), (24, 5), (73, 2), (40, 40), (120, 120)):
            xs = (y, y+h, y+2*h)
            for p in primes:
                powers = [n for n, base in terms if base == p]
                sums = [sum(legendre(n, modulus) * max(Fraction(x,n)-1, 0)
                            for n in powers) for x in xs]
                direct = sums[0] - 2*sums[1] + sums[2]
                tent = sum(legendre(n, modulus) * Fraction(min(n-y, y+2*h-n), n)
                           for n in powers if y < n < y+2*h)
                assert direct == tent
    # Check all four sign bins by Walsh inversion, using prime powers coprime to q*d.
    q, d, y = 19, 71, 23
    for p in primes:
        bins = {(a, b): Fraction(0) for a in (-1, 1) for b in (-1, 1)}
        fourier = [Fraction(0)] * 4
        for n, base in terms:
            if base != p or not y < n < 3*y or gcd(n, q*d) != 1:
                continue
            a, b = legendre(n, q), legendre(n, d)
            w = Fraction(min(n-y, 3*y-n), n)
            bins[a, b] += w
            for i, char in enumerate((1, a, b, a*b)):
                fourier[i] += w*char
        total, first, second, both = fourier
        for (a, b), mass in bins.items():
            assert 4*mass == total + a*first + b*second + a*b*both
    print("Exact ramp and sign-bin identities passed (formal log coefficients through n=360).")


def check_exceptional_character():
    # m0 fixes the d progression. A character of conductor 21 restricts outside m0 to mod 7.
    m0 = 16*3*5
    a0 = next(a for a in range(m0) if a % 16 == 7 and (a+1) % 15 == 0)
    for factors in ((7,), (11,), (7, 11)):
        s = 1
        for p in factors:
            s *= p
        classes = [x for x in range(a0, m0*s, m0) if gcd(x, s) == 1]
        weights = []
        for x in classes:
            weight = 1
            for p in factors:
                weight *= legendre(x, p)
            weights.append(weight)
        assert sum(weights) == 0
        if 7 in factors:
            exceptional = sum(w*legendre(x, 3)*legendre(x, 7) for w, x in zip(weights, classes))
            assert exceptional == (-len(classes) if s == 7 else 0)
    print("The exceptional term survives the mod-7 projection and cancels at modulus 77.")


if __name__ == "__main__":
    certify_window_primes()
    check_ramp()
    check_exceptional_character()
