"""Independent direct local evaluations of all Jacobi norm factors."""

import argparse
import sys
import math
from pathlib import Path
import numpy as np

try:
    from gmpy2 import mpz as integer
except ImportError:
    integer = int
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "fixed-character-577"))
from fourier_witness import primitive, roots

P = 577
C = 256
F = C * P


def histogram(r):
    g = primitive(r)
    logs = np.empty(r, dtype=np.int32)
    x = 1
    i = 0
    gi = pow(g, -1, r)
    for _ in range(r - 1):
        logs[x] = i
        x = x * gi % r
        i = (i - 1) % F
    assert x == 1 and i == 0
    out = np.zeros(F, dtype=np.int64)
    step = 65536
    for j in range(2, r, step):
        m = min(step, r - j)
        v = -(logs[j : j + m] + logs[r + 2 - j - m : r + 2 - j][::-1]) % F
        np.add.at(out, v, 1)
    u = np.arange(C, dtype=np.int64)[:, None]
    v = np.arange(P, dtype=np.int64)[None, :]
    return out[u + C * ((v - u) * pow(C, -1, P) % P)]


def act(a, k):
    return a[:, np.arange(P) * pow(k, -1, P) % P]


class Ring:
    def __init__(self, m, t, degree):
        self.m = m
        self.t = t
        self.degree = degree
        self.one = np.zeros((degree, P), dtype=np.int64)
        self.one[0, 0] = 1
        self.size = degree * 2 * P
        assert degree * P * (m - 1) ** 2 < 2**63

    def mul(self, a, b):
        if self.degree == 1:
            co = np.convolve(a[0], b[0])
            co[: P - 1] += co[P:]
            return (co[:P] % self.m).reshape(1, P)

        def packed(v):
            data = np.zeros((self.degree, 2 * P), dtype="<u8")
            data[:, :P] = v
            return integer.from_bytes(data.tobytes(), "little")

        raw = (packed(a) * packed(b)).to_bytes(self.size * 16, "little")
        z = np.frombuffer(raw, dtype="<u8").reshape(2 * self.degree, 2 * P)
        v = ((z[:, :P] + z[:, P:]) % self.m).astype(np.int64)
        return (v[: self.degree] + self.t * v[self.degree :]) % self.m

    def pw(self, a, n):
        out = self.one
        while n:
            if n & 1:
                out = self.mul(out, a)
            n //= 2
            if n:
                a = self.mul(a, a)
        return out

    def one_j(self, h, v):
        de = self.degree
        ex = (np.arange(C) * v) % C
        scal = roots(self.t, C // de, self.m)[ex // de]
        return np.array(
            [scal[ex % de == i] @ h[ex % de == i] % self.m for i in range(de)]
        )

    def norm(self, h):
        val = self.one
        for i in range(64):
            for sign in [1, -1]:
                v = sign * pow(5, i, C) % C
                x = self.one_j(h, v)
                for j in range(9):
                    val = self.mul(val, act(x, pow(5, 441 * i + 64 * j, P)))
        return val


def readings(r, folded=None, anchor=2363393):
    if folded is None:
        h = histogram(r)
    else:
        values = np.fromfile(folded, dtype="<u2")
        assert len(values) == F * P
        j = values.reshape(P, F).sum(axis=0, dtype=np.int64)
        u = np.arange(C)[:, None]
        b = np.arange(P)[None, :]
        h = j[u + C * ((b - u) * pow(C, -1, P) % P)]
    assert int(h.sum()) == r - 2
    m = P * P
    ring = Ring(m, pow(20, P, m), 4)
    norm = ring.norm(h)
    b = ring.one
    for i in range(64):
        t = ring.pw(act(norm, pow(5, -i, P)), pow(20, i, P))
        b = ring.mul(b, t)
    w = ring.pw(b, P - 1)
    w = (w[:, :-1] - w[:, -1, None]) % m
    w[0, 0] = (w[0, 0] - 1) % m
    assert np.all(w % P == 0) and np.all(np.sum(w // P, axis=1) % P == 0)
    v = (
        w
        // P
        @ np.array([pow(j, 297, P) for j in range(P - 1)])
        % P
        * pow(math.factorial(297), -1, P)
        % P
    )
    d = anchor
    g = primitive(d)
    root = pow(g, (d - 1) // F, d)
    Y = pow(root, P * pow(P, -1, C), d)
    z = pow(root, C * pow(C, -1, P), d)
    field = Ring(d, Y, 1)
    norm = field.norm(h)
    zv = roots(z, P, d)
    h = 1
    for i in range(64):
        x = int(act(norm, pow(5, -i, P))[0] @ zv) % d
        h = h * pow(x, pow(20, i, P), d) % d
    mu = roots(pow(g, (d - 1) // P, d), P, d)
    j = np.flatnonzero(mu == pow(h, (d - 1) // P, d)).item()
    print(r, j, v.tolist(), flush=True)
    return j, v


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--folded",
        nargs=2,
        metavar=("PRIME", "HISTOGRAM"),
        help="reuse a large second-level histogram",
    )
    args = parser.parse_args()
    controls = {
        1920257: (333, 511),
        4579073: (388, 60),
        6647041: (84, 548),
        340919297: (507, 514),
        1022757889: (101, 367),
    }
    if args.folded and args.folded[0] not in {"340919297", "1022757889"}:
        parser.error("--folded expects one of the two recorded level-squared primes")
    tests = (
        [(int(args.folded[0]), args.folded[1])]
        if args.folded
        else [(r, None) for r in (1920257, 4579073, 6647041)]
    )
    for r, f in tests:
        u, v = readings(r, f)
        assert (u, v.tolist()) == (controls[r][0], [0, controls[r][1], 0, 0])
    assert (333 * 60 - 388 * 511) % P == 5 and (507 * 367 - 101 * 514) % P == 291
