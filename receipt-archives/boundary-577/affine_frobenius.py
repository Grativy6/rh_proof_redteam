"""Check the translation Frobenii at the two new auxiliary primes."""

from pathlib import Path
import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "fixed-character-577"))
from fourier_witness import primitive, roots, histogram, dft, character

P = 577
F = 256 * P


def mul(A, B, q):
    lo = (A % 32768) @ B % q
    hi = (A // 32768) @ B % q
    assert (q // 32768 + 32768) * (q - 1) * A.shape[1] < 2**63
    return (lo + 32768 * hi) % q


def test(h, d):
    g = primitive(d)
    z = pow(g, (d - 1) // F, d)
    y = pow(z, P * pow(P, -1, 256), d)
    b = pow(z, 256 * pow(256, -1, P), d)
    v = mul(mul(dft(256, y, d), h, d), dft(P, b, d), d)[1::2, 1:]
    out = np.ones_like(v)
    n = (d - 1) // P
    while n:
        if n % 2:
            out = out * v % d
        n //= 2
        v = v * v % d
    mu = roots(pow(g, (d - 1) // P, d), P, d)
    ix = np.argsort(mu)
    logs = ix[np.searchsorted(mu[ix], out)]
    assert np.array_equal(mu[logs], out)
    w = (
        np.array([pow(character(a), -1, P) for a in range(1, 256, 2)])[:, None]
        * np.array([pow(i, -297, P) for i in range(1, P)])[None, :]
        % P
    )
    v = int(np.sum(logs * w)) % P
    controls = {2363393: 333, 4579073: 301, 340919297: 278, 1022757889: 508}
    assert v == controls[d]
    print(d, g, v, int(mu[v]), flush=True)
    return v


if __name__ == "__main__":
    h = histogram()
    for d in (2363393, 4579073, 340919297, 1022757889):
        test(h, d)
