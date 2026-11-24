"""Auxiliary Eisenstein constant through degree three in zeta_577 - 1."""

from pathlib import Path
import math
import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "fixed-character-577"))
from bounds import char2, P, prime
from fourier_witness import primitive


def bernoulli_kernel(k, conductor):
    b = [1]
    for n in range(1, k + 1):
        b.append(
            -sum(math.comb(n + 1, j) * b[j] for j in range(n)) * pow(n + 1, -1, P) % P
        )
    # B_{k,chi}=F^(k-1)*sum chi(a)*B_k(a/F). F=D*w = D mod P.
    co = [math.comb(k, j) * b[j] * pow(conductor, j - 1, P) % P for j in range(k + 1)]
    x = np.arange(P, dtype=np.int64)
    v = np.zeros(P, dtype=np.int64)
    for a in co:
        v = (v * x + a) % P
    return v


def phi(exponent):
    eta = (0, 1, 1, -1, 1, -1, -1)
    pc = char2(exponent)
    return np.array(
        [eta[u % 7] * pc[u % len(pc)] % P for u in range(7 * len(pc))], dtype=np.int64
    )


def distribution(w, exponent, weight):
    h = phi(exponent)
    D = len(h)
    assert prime(w) and w % P == 1 and h[w % D] == 1
    Pk = bernoulli_kernel(weight, D)
    x = np.arange(D * P + D, dtype=np.int64)
    tab = h[x % D] * Pk[x % P] % P
    pref = np.r_[np.int64(0), np.cumsum(tab)]
    block = (pref[D : D + D * P] - pref[: D * P]) % P
    # Enumerate b as a multiplicative power modulo w. theta(b)=zeta^i.
    gen = primitive(w)
    step = 65536
    s = np.empty(step, dtype=np.int64)
    z = 1
    for i in range(step):
        s[i] = z
        z = z * gen % w
    B = pow(D, -1, P)
    inv = pow(w, -1, D)
    scale = 1
    dist = np.zeros(P, dtype=np.int64)
    for j in range(0, w - 1, step):
        n = min(w - 1 - j, step)
        v = s[:n] * scale % w
        d = v * inv % D
        y = d + D * ((v - d) * B % P)
        np.add.at(dist, np.arange(j, j + n) % P, block[y])
        scale = scale * z % w
    return dist % P, gen


def coeff(t, n, weight):
    return (
        -sum(math.comb(i, n) * int(v) for i, v in enumerate(t) if i >= n)
        * pow(2 * weight, -1, P)
        % P
    )


if __name__ == "__main__":
    expected = {
        515839: (3, [0, 348, 343, 309], [0, 304, 327, 264]),
        1106687: (7, [0, 23, 199, 523], [0, 53, 344, 53]),
        2363393: (3, [0, 187, 42, 360], [0, 558, 448, 432]),
        4579073: (3, [0, 404, 385, 479], [0, 222, 311, 7]),
        6647041: (13, [0, 524, 198, 70], [0, 502, 76, 506]),
        12407809: (22, [0, 291, 216, 361], [0, 506, 110, 247]),
    }
    for w, (g0, first, second) in expected.items():
        for exponent, weight, want in ((1, 297, first), (2, 17, second)):
            hist, g = distribution(w, exponent, weight)
            out = [coeff(hist, k, weight) for k in range(4)]
            assert (g, out) == (g0, want)
            print(w, g, weight, out, flush=True)
