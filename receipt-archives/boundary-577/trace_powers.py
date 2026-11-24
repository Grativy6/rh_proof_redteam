"""Compare the original marked coordinates with the local Artin basis at two primes."""

from math import gcd
from pathlib import Path
import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "marked-directions-577"))
from residual_directions import P, prime_logs, table, upper
from fourier_witness import primitive, roots


def artin_exponent(a, r):
    """Evaluate the newly oriented radicand, both tame and wild inputs explicit."""
    phi = table(a, True)
    D = len(phi)
    g = primitive(r)
    Y = pow(g, (r - 1) // D * pow(P, -1, D), r)
    Z = pow(g, (r - 1) // P * pow(256, -1, P), r)
    units = np.array([i for i in range(1, D) if gcd(i, D) == 1])
    tame = roots(Y, D, r)[units]
    wild = roots(Z, P, r)[1:]
    logs = prime_logs((1 - tame[:, None] * wild[None, :]) % r, g, r)
    weights = (
        phi[units, None]
        * np.array([pow(i, 296 * a - 1, P) for i in range(1, P)])[None, :]
        % P
    )
    # prime_logs measures exponents relative to Z^256. The normalized
    # circular radicand was raised to p^12-1.
    new = -256 * int(np.sum(logs * weights)) % P
    scale = -256 * pow(D * pow(256, -1, P), 1 - 296 * a, P) % P
    assert new == scale * upper(a, r) % P
    return scale, new, new * (pow(510, a, P) - 1) % P


def main():
    controls = {
        12407809: [(86, 53, 435), (189, 306, 68)],
        19645697: [(86, 399, 564), (189, 275, 574)],
    }
    for r, expect in controls.items():
        values = [artin_exponent(a, r) for a in (1, 2)]
        assert values == expect
        print("Frobenius", r, "(scale, reading, marked commutator)", values)
    coord_u = -435 * pow(4, -1, P) % P
    coord_v = 68
    t1 = 341 * pow(coord_u, -1, P) % P
    t2 = 394 * pow(coord_v, -1, P) % P
    assert (coord_u, t1, t1 * t1 % P) == (324, 99, 569)
    assert (coord_v, t2, t2 * t2 % P) == (68, 464, 75)
    for n, r, lead, square in [(5, 2, t1, 569), (7, 3, t2, 75)]:
        # Along the two axes all possible relations have order >= 1+2*r.
        assert 1 + 2 * r == n and 2 * r < n <= 3 * r
        assert lead * lead % P == square
        print(
            "jet t^",
            n,
            "trace order",
            r,
            "square coefficient",
            square,
            "nilpotency index",
            (n + r - 1) // r,
        )
    for m in range(3, 200):
        n = 2 * m - 2
        assert (n + m - 1) // m == 2
    assert 4 * 3 < 13 <= 5 * 3
    print("A common quadratic direction gives trace order 3 at precision 13.")


if __name__ == "__main__":
    main()
