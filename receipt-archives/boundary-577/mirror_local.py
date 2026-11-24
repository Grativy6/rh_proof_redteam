"""Local first digits for all singular mirrors of the real degree-576 field."""

from pathlib import Path
import numpy as np
import sys
from math import gcd

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "fixed-character-577"))
from fourier_witness import roots, character, reduce_product, times, power
import group_ring_witness as ring

P = 577
F = 256 * P


def project(H, C, queries):
    # queries (a,j,n) use character weight psi^(a*j) and logarithmic degree n
    units = np.arange(1, C, 2)
    y = roots(20, 64, P)
    k = np.arange(P)
    ds = sorted(set(n for _, _, n in queries))
    degree = max(ds)
    fact = np.ones((P, degree + 1), dtype=np.int64)
    for j in range(1, degree + 1):
        fact[:, j] = fact[:, j - 1] * k * pow(j, -1, P) % P
    h = H.reshape(-1, C * P).sum(axis=0)
    ux = np.arange(C)[:, None]
    b = k[None, :]
    h = h[ux + C * ((b - ux) * pow(C, -1, P) % P)]
    tab = np.zeros((len(units), degree + 1, 4), dtype=np.int64)
    for idx, v in enumerate(units):
        exponent = np.arange(C) * int(v) * (256 // C) % 256
        for s in range(4):
            active = exponent % 4 == s
            val = y[exponent[active] // 4] @ h[active] % P
            tab[idx, :, s] = val @ fact % P
    inv = power(tab[:, 0, :], P**4 - 2)
    assert np.array_equal(
        times(inv, tab[:, 0, :]), np.tile([1, 0, 0, 0], (len(units), 1))
    )
    logs = np.zeros_like(tab)
    for n in range(1, degree + 1):
        conv = np.einsum(
            "vji,vjk->vik", tab[:, 1:n, :], logs[:, n - 1 : 0 : -1, :], optimize=False
        )
        logs[:, n, :] = times((n * tab[:, n, :] - reduce_product(conv)) % P, inv)
    for a, j, n in queries:
        w = np.array([pow(character(int(v)), a * j, P) for v in units])
        ct = w @ logs[:, n, :] % P * pow(n, -1, P) % P
        values = {
            (141, 1): [0, 0, 0, 202],
            (300, 1): [522, 0, 0, 0],
            (300, 193): [93, 0, 0, 0],
            (300, 313): [425, 0, 0, 0],
            (300, 359): [311, 0, 0, 0],
            (492, 1): [93, 0, 0, 0],
            (575, 1): [0, 0, 0, 0],
        }
        assert ct.tolist() == values[a, j]
        print(a, j, n, ct.tolist(), flush=True)


def main():
    r = 1920257
    H = ring.jj.log_histogram(F, r, ring.generator(r))
    for a, js in [(141, [1]), (300, [1, 193, 313, 359]), (492, [1]), (575, [1])]:
        o = 64 // gcd(a, 64)
        C = 4 * o
        project(H, C, [(a, j, j * (1 - 296 * a) % 576) for j in js])


if __name__ == "__main__":
    main()
