"""Finite controls for the theta phase, the norm congruence and a mixed row.

The norm fibers, congruence lifts and coset enumeration use integer arithmetic.
The direct Jacobi average and its error use double precision, independently
of the paper's Gaussian-integral evaluation. Python standard library only.
"""

import cmath
import math
from collections import Counter
from fractions import Fraction
from itertools import product


def norm_fibers(prime, nonsquare):
    """Test one inert Hermitian block over F_(p^2) in a power basis."""
    assert pow(nonsquare, (prime - 1) // 2, prime) == prime - 1
    fibers = Counter((a * a - nonsquare * b * b) % prime
                     for a, b in product(range(prime), repeat=2))
    assert fibers[0] == 1
    assert all(fibers[r] == prime + 1 for r in range(1, prime))
    # Evaluate sum zeta^Norm using 1+...+zeta^(p-1)=0. An unmatched
    # coefficient would leave a nonrational component in this basis.
    coeffs = [fibers[i] - fibers[prime - 1] for i in range(prime - 1)]
    assert coeffs == [-prime] + [0] * (prime - 2)
    assert coeffs[0] ** 2 == prime ** 2


def check_norm_lifts(prime, nonsquare):
    """Solve Norm(l)=-1 in unramified quadratic rings modulo p,p^2,p^3."""
    a, b = next((x, y) for x, y in product(range(prime), repeat=2)
                if (x * x - nonsquare * y * y + 1) % prime == 0)
    power = prime
    for _ in range(3):
        norm = a * a - nonsquare * b * b
        assert (norm + 1) % power == 0
        correction = (-(norm + 1) // power * pow(2 * norm, -1, prime)) % prime
        factor = 1 + power * correction
        power *= prime
        a, b = a * factor % power, b * factor % power
    assert (a * a - nonsquare * b * b + 1) % power == 0


def check_finite_phases():
    for prime, nonsquare in [(3, 2), (5, 2), (7, 3), (11, 2), (13, 2)]:
        norm_fibers(prime, nonsquare)
        check_norm_lifts(prime, nonsquare)
    print("Five inert residue fields: one triangle has sign -1; two copies give +1.")
    print("Norm -1 lifts checked through the fourth power of each odd prime.")

    # At the ramified prime of Q(sqrt(-7)), norm modulo 7 is a square.
    norms = {(a * a + a * b + 2 * b * b) % 7 for a, b in product(range(7), repeat=2)}
    assert norms == {0, 1, 2, 4}
    assert 6 not in norms
    counts = Counter(2 * n * n % 7 for n in range(7))
    assert counts == {0: 1, 1: 2, 2: 2, 4: 2}
    print("Ramified control at 7: norm -1 is absent; the one-block Gaussian phase is +i.")


def check_two_lifts():
    # Integral basis 1,w with w^2=w-2. pi=1+2w, pi*bar(pi)=11.
    def multiply(x, y):
        a, b = x
        c, d = y
        return a * c - 2 * b * d, a * d + b * c + b * d

    pi, pi_bar = (1, 2), (3, -2)
    assert multiply(pi, pi_bar) == (11, 0)
    numerator = multiply(pi_bar, pi_bar)
    assert numerator == (1, -8)
    a, b = multiply((0, 1), numerator)
    phase_pairing = Fraction(b * pi[0] - a * pi[1], 11)
    assert phase_pairing == Fraction(-39, 11)
    # s=t+pi has the same selected residue as t. At the conjugate
    # prime, t vanishes and pi has nonzero residue (w=7 mod 11).
    assert (pi[0] + pi[1] * 7) % 11 != 0
    print("Two lifts agree at the selected prime; the excluded lift changes the phase by order 11.")


def check_noncentral_conjugation():
    # Roots of X^3-2 are indexed by i in alpha*zeta^i. Complex
    # conjugation sends i to -i; a Galois automorphism sends i to i+1.
    sigma = (1, 2, 0)
    conjugation = (0, 2, 1)
    assert sigma[conjugation[0]] != conjugation[sigma[0]]
    # The transported formal square has zeta^2 instead of 1 as
    # its multiplier. Its real part follows from zeta+zeta^2=-1.
    field_exponent = (sigma[conjugation[0]] + sigma[0]) % 3
    metric_exponent = (conjugation[sigma[0]] + sigma[0]) % 3
    cyclotomic_coordinates = [(1, 0), (0, 1), (-1, -1)]
    real_parts = [a - Fraction(b, 2) for a, b in cyclotomic_coordinates]
    assert real_parts[field_exponent] == Fraction(-1, 2)
    assert real_parts[metric_exponent] == 1
    print("Cubic splitting field: the wrong conjugation order gives a negative real part.")


def check_mixed_row():
    # tau^2=tau-2, u=tau/bar(tau). For v=(3,4), the unitary matrix
    # I+(u-1)vv^t/25 fixes (-4,3). Each coset of its image modulo the
    # period lattice has a representative g(-lambda,lambda).
    tau = complex(0.5, math.sqrt(7) / 2)
    area = tau.imag
    rotation = tau / tau.conjugate()

    def theta_two(z):
        return sum(cmath.exp(1j * math.pi * ((k + 0.5) ** 2 * tau + 2 * (k + 0.5) * z))
                   for k in range(-7, 8))

    constant = theta_two(0)

    def section(z):
        return cmath.exp(math.pi * z * z / (2 * area)) * theta_two(z) / constant

    def shift(v, z):
        return cmath.exp(-math.pi * (z * v.conjugate() + abs(v) ** 2 / 2) / area) * section(z + v)

    # (u-1)*lambda/25 has numerator coordinates (-4a-2b,a-3b)
    # modulo 50. Period reduction below converts large translates to
    # small ones using the exact sign and pairing before evaluation.
    seen = set()
    translates = []
    for a, b in product(range(50), repeat=2):
        real, imag = -4 * a - 2 * b, a - 3 * b
        residue = real % 50, imag % 50
        if residue in seen:
            continue
        seen.add(residue)
        reduced = []
        pairing_numerator = 0
        period_norm = 0
        for component, sign in ((3, -1), (4, 1)):
            x = 50 * sign * a + component * real
            y = 50 * sign * b + component * imag
            c, d = (x + 25) // 50, (y + 25) // 50
            h, j = x - 50 * c, y - 50 * d
            reduced.append((h + j * tau) / 50)
            pairing_numerator += j * c - h * d
            period_norm += c * c + c * d + 2 * d * d
        exponent = (pairing_numerator + 50 * period_norm) % 100
        phase = cmath.exp(1j * math.pi * exponent / 50)
        translates.append((phase, *reduced))

    assert len(translates) == 1250
    raw_phase = tau.conjugate() / math.sqrt(2)
    max_error = 0.0
    for z, w in [(0j, 0j), (0.14 + 0.07j, -0.12 + 0.23j), (-0.19j, 0.09 + 0.03j)]:
        correction = (rotation - 1) * (3 * z + 4 * w) / 25
        gz, gw = z + 3 * correction, w + 4 * correction
        terms = [phase * shift(x, gz) * shift(y, gw) for phase, x, y in translates]
        direct = complex(math.fsum(t.real for t in terms), math.fsum(t.imag for t in terms))
        direct /= math.sqrt(len(translates))
        max_error = max(max_error, abs(direct - raw_phase * section(z) * section(w)))
    assert max_error < 2e-11
    print(f"Mixed row, 1250 cosets, three arguments: largest Jacobi error {max_error:.2e}.")


if __name__ == "__main__":
    check_finite_phases()
    check_two_lifts()
    check_noncentral_conjugation()
    check_mixed_row()
