"""Check residual directions, circular-unit digits, and the common commutator."""

from math import factorial
from pathlib import Path
import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "fixed-character-577"))
from bounds import P, char2, prime
from fourier_witness import primitive, roots, histogram, dft

ETA = (0, 1, 1, -1, 1, -1, -1)


def powers(x, k, p):
    result = np.ones_like(x)
    while k:
        if k % 2:
            result = result * x % p
        x = x * x % p
        k //= 2
    return result


def prime_logs(v, g, d):
    basis = roots(pow(g, (d - 1) // P, d), P, d)
    ix = np.argsort(basis)
    targets = powers(v, (d - 1) // P, d)
    out = ix[np.searchsorted(basis[ix], targets)]
    assert np.array_equal(basis[out], targets)
    return out


def table(exponent, odd):
    p = char2(exponent)
    return np.array(
        [
            p[i % len(p)] * (ETA[i % 7] if odd else 1) % P
            for i in range(len(p) * (7 if odd else 1))
        ],
        dtype=np.int64,
    )


def multiplier(char, exponent):
    f = len(char) * P
    i = np.arange(f // 2 + 1, f, 2, dtype=np.int64)
    cyc = np.array(
        [pow(a, exponent % (P - 1), P) if a else 0 for a in range(P)], dtype=np.int64
    )
    return int(np.sum(char[i % len(char)] * cyc[i % P])) % P


def local_digit(a):
    n = (1 - 296 * a) % (P - 1)
    phi = table(a, True)
    D = len(phi)
    inv = np.array([pow(int(y), -1, P) if y else 0 for y in phi])
    j = np.arange(D, dtype=np.int64)
    k = np.arange(1, P, dtype=np.int64)
    inner = inv[(k[:, None] + P * j) % D] @ j
    return (
        sum(pow(int(t), n - 1, P) * int(b) for t, b in zip(k, inner))
        * pow(D * factorial(n), -1, P)
        % P
    )


def upper(a, d):
    phi = table(a, True)
    D = len(phi)
    f = D * P
    assert (d - 1) % f == 0
    g = primitive(d)
    z = roots(pow(g, (d - 1) // f, d), f, d)
    i = np.arange(1, f, 2, dtype=np.int64)
    i = i[(i % 7 != 0) & (i % P != 0)]
    logs = prime_logs((1 - z[i]) % d, g, d)
    cyc = np.array([pow(t, (296 * a - 1) % (P - 1), P) for t in range(P)])
    return int((phi[i % D] * cyc[i % P] % P) @ logs) % P


def lower(d, hist):
    f = 256 * P
    g = primitive(d)
    z = pow(g, (d - 1) // f, d)
    a = pow(z, P * pow(P, -1, 256), d)
    b = pow(z, 256 * pow(256, -1, P), d)
    assert max(256, P) * (d - 1) ** 2 < 2**63
    values = (dft(256, a, d) @ hist % d) @ dft(P, b, d) % d
    vals = values[1::2, 1:]
    dec = prime_logs(vals, g, d)
    c = char2()
    psi = np.array([pow(c[i], -1, P) for i in range(1, 256, 2)])
    omega = np.array([pow(i, -297, P) for i in range(1, P)])
    return int(np.sum(dec * (psi[:, None] * omega[None, :] % P))) % P


def companion():
    m = P * P
    chi = char2(modulus=m)
    for p, expected in [(11, (134401, 208257, 128)), (3329, (84049, 58084, 532))]:
        a = chi[p % 256] * pow(p, 296, m) % m
        b = pow(chi[p % 256], -1, m) * pow(p, 280, m) % m
        A = (1 + a + pow(a, -1, m)) % m
        B = (1 + b + pow(b, -1, m)) % m
        assert (A - B) % P == 0
        triple = A, B, ((B - A) % m) // P
        assert triple == expected
        print("split prime", p, "two traces mod 577^2 and difference/577", triple)
    assert (pow(5, 296, P), pow(5, 280, P)) == (4, 433)
    assert 4 * 433 % P == 1 and 4 != 433


def main():
    companion()
    known = {
        -2: (479, 556, 160),
        -1: (0, 537, 229),
        1: (428, 445, 211),
        2: (524, 101, 241),
    }
    for a, want in known.items():
        v = (
            multiplier(table(a, False), 296 * a - 1),
            multiplier(table(-a, True), -296 * a),
            local_digit(a),
        )
        assert v == want
        print(
            "power",
            a,
            "even Kummer multiplier, odd class multiplier, upper-unit local digit",
            v,
        )
    h = histogram()
    chis = [pow(510, -1, P), 510, pow(510, 2, P)]
    for d, expected, trans in [
        (12407809, [82, 61, 139], [511, 468, 95]),
        (19645697, [231, 481, 206], [377, 181, 174]),
    ]:
        assert prime(d) and (d - 1) % (1792 * P) == 0
        a = [lower(d, h), upper(1, d), upper(2, d)]
        comm = [(chi - 1) * t % P for chi, t in zip(chis, a)]
        assert a == expected and comm == trans
        print("prime", d, "three translations", a, "commutator", comm)
    assert (pow(510, -1, P) - 1) * 333 % P == 506
    assert 4 * (pow(155, 2, P) - 155) % P == 275 and 506 * 275 % P == 93


if __name__ == "__main__":
    main()
