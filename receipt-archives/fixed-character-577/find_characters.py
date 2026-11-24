"""Screen the mirror divisor and its complementary real circular unit on the actual even 2-power characters."""

import argparse
import json
import math
from pathlib import Path
import numpy as np


def prime(n):
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


def roots(g, n, p):
    ans = np.empty(n, dtype=np.int64)
    x = 1
    for i in range(n):
        ans[i] = x
        x = x * g % p
    assert x == 1
    return ans


def powers(x, n, p):
    out = np.ones_like(x)
    while n:
        if n & 1:
            out = (out * x) % p
        x = x * x % p
        n //= 2
    return out


class Sectors:
    def __init__(self, ell, m, g):
        self.ell = ell
        self.m = m
        C = self.C = 4 * m
        self.f = C * ell
        self.b = np.arange(1, m, 2)
        self.e = np.array(
            [e for e in range(2, ell - 1, 2) if 2 * e % (ell - 1)], dtype=np.int64
        )
        self.entry = np.ones((len(self.b), len(self.e)), dtype=bool)
        self.known = np.zeros_like(self.entry)
        self.exps = roots(g, ell - 1, ell)
        k = np.arange(ell - 1)
        self.sub = roots(pow(g, (ell - 1) // m, ell), m, ell)
        x = roots(5, m, C)[:, None]
        self.log2 = {int(z): i for i, z in enumerate(x[:, 0])}
        self.log2.update({-z % C: k for z, k in list(self.log2.items())})
        self.plus = x + C * ((self.exps[None, :] - x) * pow(C, -1, ell) % ell)
        a = -x % C
        self.minus = a + C * ((self.exps[None, :] - a) * pow(C, -1, ell) % ell)
        self.x = self.sub[(-self.b[:, None] * np.arange(m)[None, :]) % m]
        self.y = self.exps[(-k[:, None] * (self.e[None, :] + 1)) % (ell - 1)]
        self.xx = self.sub[(self.b[:, None] * np.arange(m)[None, :]) % m]
        self.yy = self.exps[(k[:, None] * self.e[None, :]) % (ell - 1)]

    def mirror(self):
        u = 1
        ell = self.ell
        while not self.known.all():
            u += 2
            if u % ell == 0:
                continue
            z = self.log2[u % self.C]
            active = (
                self.sub[self.b * z % self.m, None]
                * np.array([pow(u, int(e), ell) for e in self.e])[None, :]
            ) % ell != 1
            if not np.any(active & ~self.known):
                continue
            h = u * self.plus // self.f + u * self.minus // self.f
            v = ((self.x @ h) % ell @ self.y) % ell
            self.entry &= v == 0
            self.known |= active
        return np.argwhere(self.entry)

    def real(self, r):
        ell, f = self.ell, self.f
        g = generator(r)
        z = roots(pow(g, (r - 1) // f, r), f, r)
        logs = roots(pow(g, (r - 1) // ell, r), ell, r)
        v = powers((1 - z) % r, (r - 1) // ell, r)
        ix = np.argsort(logs)
        li = np.zeros(f, dtype=np.int64)
        li[1:] = ix[np.searchsorted(logs[ix], v[1:])]
        assert np.all(logs[li[1:]] == v[1:])
        h = li[self.plus] + li[self.minus]
        tab = ((self.xx @ h) % ell @ self.yy) % ell
        return tab


def fast_factors(n):
    out = []
    i = 2
    while i * i <= n:
        if n % i == 0:
            out.append(i)
            while n % i == 0:
                n //= i
        i += 1
    if n > 1:
        out.append(n)
    return out


def generator(p):
    fs = fast_factors(p - 1)
    return next(g for g in range(2, p) if all(pow(g, (p - 1) // v, p) != 1 for v in fs))


def run(L, limit):
    tested = mir = 0
    surv = []
    half = []
    for ell in range(5, L + 1):
        if ell == 7 or not prime(ell):
            continue
        g = generator(ell)
        m = 2
        while (ell - 1) % m == 0 and m <= limit:
            A = Sectors(ell, m, g)
            hits = A.mirror()
            tested += A.entry.size
            mir += len(hits)
            remain = A.entry.copy()
            r = 1
            reads = []
            for j in range(4):
                if not remain.any():
                    break
                r += A.f
                while not prime(r):
                    r += A.f
                tab = A.real(r)
                reads.append(r)
                remain &= tab == 0
                if j == 0:
                    half.extend(
                        [int(ell), int(m), int(A.b[i]), int(A.e[t])]
                        for i, t in np.argwhere(remain)
                    )
            for i, t in np.argwhere(remain):
                v = [int(ell), int(m), int(A.b[i]), int(A.e[t]), reads]
                print("candidate", v, flush=True)
                surv.append(v)
            m *= 2
    print(tested, mir, len(half), len(surv), flush=True)
    return dict(tested=tested, mirror=mir, one=half, surv=surv)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-prime", type=int, default=2200)
    parser.add_argument("--max-order", type=int, default=256)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    out = run(args.max_prime, args.max_order)
    if (args.max_prime, args.max_order) == (2200, 256):
        assert (out["tested"], out["mirror"], len(out["one"]), out["surv"]) == (
            1180660,
            1271,
            2,
            [[577, 64, 39, 296, [1920257, 2363393, 4579073, 6647041]]],
        )
    if args.output:
        args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="ascii")
