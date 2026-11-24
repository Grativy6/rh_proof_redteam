"""Exact bounds, the 32-character orbit, and the two modular-form congruences."""

from math import comb, isqrt, gcd
import numpy as np

P = 577
C = 256
F = P * C
E = 296
B = 39


def prime(p):
    return p >= 2 and all(p % i for i in range(2, isqrt(p) + 1))


def char2(exponent=1, modulus=P):
    """The Teichmuller lift of the chosen even character or its power."""
    t = pow(5, 9 * B, P)
    if modulus == P * P:
        t = pow(t, P, modulus)
    root = pow(t, exponent, modulus)
    order = 64 // gcd(64, abs(exponent))
    conductor = 4 * order
    vals = [0] * conductor
    for j in range(order):
        a = pow(5, j, conductor)
        vals[a] = vals[-a % conductor] = pow(root, j, modulus)
    return vals


def bernoulli_mod(chi, k):
    # All k used here are below p-1, so every displayed denominator is a unit.
    f = len(chi)
    bn = [1]
    for n in range(1, k + 1):
        bn.append(
            -sum(comb(n + 1, j) * bn[j] for j in range(n)) * pow(n + 1, -1, P) % P
        )
    return (
        sum(
            comb(k, j)
            * bn[j]
            * pow(f, j - 1, P)
            * sum(v * pow(a, k - j, P) for a, v in enumerate(chi))
            for j in range(k + 1)
        )
        % P
    )


def moment_check(power, weight):
    """Faulhaber at a whole block of 577 periods gives B_weight modulo 577."""
    modulus = P**2
    vals = char2(power, modulus=modulus)
    eta = (0, 1, 1, -1, 1, -1, -1)
    conductor = 7 * len(vals)
    chi = np.array(
        [eta[i % 7] * vals[i % len(vals)] % modulus for i in range(conductor)],
        dtype=np.int64,
    )
    a = np.arange(1, conductor * P + 1, dtype=np.int64)
    x = a % modulus
    powers = np.ones_like(x)
    k = weight
    while k:
        if k % 2:
            powers = powers * x % modulus
        x = x * x % modulus
        k //= 2
    moment = int(np.sum(chi[a % conductor] * powers % modulus)) % modulus
    assert moment % P == 0
    return (moment // P) * pow(conductor, -1, P) % P


def half_counts():
    g = pow(5, 9, P)
    log = {pow(g, i, P): i for i in range(64)}
    counts = np.zeros((64, 64), dtype=np.int64)
    even_log = {pow(5, i, C): i for i in range(64)}
    even_log.update({-a % C: k for a, k in list(even_log.items())})
    for a in range(F // 2 + 1, F, 2):
        if a % P:
            counts[even_log[a % C], log[pow(a, 297, P)]] += 1
    return counts


def residual_orders():
    m = P**2
    g = pow(pow(5, 9, P), P, m)
    counts = half_counts()
    indices = np.arange(64, dtype=np.int64)
    weights = np.array([pow(g, -i, m) for i in indices.tolist()], dtype=np.int64)

    def value(b, j):
        return (
            int(
                np.sum(
                    counts
                    * weights[(j * (b * indices[:, None] + indices[None, :])) % 64]
                )
            )
            % m
        )

    orbit = [value(b, 1) % P for b in range(1, 64, 2)]
    minus = [(j, value(B, j)) for j in range(1, 64, 2)]
    assert [2 * i + 1 for i, k in enumerate(orbit) if not k] == [39]
    assert [(j, k) for j, k in minus if k % P == 0] == [
        (1, 150597)
    ] and 150597 == 261 * P
    return orbit


def order_squared():
    m = P**2
    psi = np.array(
        [pow(x, -1, m) if x else 0 for x in char2(modulus=m)], dtype=np.int64
    )
    inv = np.array([pow(a, -297, m) if a % P else 0 for a in range(m)], dtype=np.int64)
    fermat = np.array(
        [(pow(a, -(P - 1), m) - 1) // P if a % P else 0 for a in range(m)],
        dtype=np.int64,
    )
    f = C * m
    total = slope = 0
    for start in range(f // 2 + 1, f, 2000000):
        a = np.arange(start, min(start + 2000000, f), 2, dtype=np.int64)
        v = psi[a % C] * inv[a % m] % m
        total += int(np.sum(v))
        slope += int(np.sum((v % P) * fermat[a % m] % P))
    k, d = total % m, slope % P
    assert (k, d) == (165599, 540) and k == 287 * P
    exceptional = (-k // P) * pow(d, -1, P) % P
    assert exceptional == 460
    return k, d, exceptional


def main():
    assert (
        prime(P)
        and pow(5, 576, P) == 1
        and all(pow(5, 576 // r, P) != 1 for r in (2, 3))
    )
    assert char2()[5] == 510 and char2(modulus=P**2)[5] == 35130
    orbit = residual_orders()
    print("Mod-577 annihilators, odd labels 1 through 63:", orbit)
    print("Order-squared multiplier, slope, exceptional twist index:", order_squared())
    eta = (0, 1, 1, -1, 1, -1, -1)
    expected = {
        (1, 297): (407, 10),
        (-1, 297): (338, 48),
        (2, 17): (110, 438),
        (-2, 17): (291, 246),
    }
    for (power, k), ans in expected.items():
        base = char2(power)
        chi = [eta[a % 7] * base[a % len(base)] % P for a in range(7 * len(base))]
        b = bernoulli_mod(chi, k)
        assert b == moment_check(power, k)
        coefficient = -b * pow(2 * k, -1, P) % P
        assert (b, coefficient) == ans
        print(
            "Weight",
            k,
            "character exponent",
            power,
            "conductor",
            len(chi),
            "B",
            b,
            "Eisenstein constant",
            coefficient,
        )
    p = 11
    char = char2()[p]
    scalar = pow(p, E, P)
    vals = []
    for label in range(1, 64, 2):
        z = scalar * pow(char, label * pow(39, -1, 64) % 64, P) % P
        vals.append((1 + z + pow(z, -1, P)) % P)
    assert (char, scalar, len(set(vals)), vals[19]) == (141, 496, 32, 537)
    assert pow(141, 32, P) == 576 and pow(11, 2 * E * 64, P) == 363
    assert 141 * 496 % P == 119 and pow(119, -1, P) == 417
    assert 417 * pow(scalar, -1, P) % P == 465 and pow(465, 64, P) == 213
    print("At split 11 all 32 labels separate. The nonzero class requires trace 537.")
    p = 3329
    assert prime(p) and p % C == 1 and pow(p, 3, 7) == 1
    assert (1 + pow(p, E, P) + pow(p, -E, P)) % P == 384
    print(
        "At split 3329 all 32 character values are 1 and the trace target reduces to 384."
    )


if __name__ == "__main__":
    main()
