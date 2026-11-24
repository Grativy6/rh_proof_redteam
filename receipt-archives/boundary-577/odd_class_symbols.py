"""Power-residue witnesses for all four singular CM eigenspaces."""

import sys
import math
import numpy as np
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "fixed-character-577"))
from fourier_witness import primitive, roots, dft
import group_ring_witness as ring

P = 577
eta = (0, 1, 1, -1, 1, -1, -1)


def run():
    r = 12407809
    d = 19645697
    Q = 1792 * P
    g = primitive(d)
    H = ring.jj.log_histogram(Q, r, primitive(r))
    for a in (276, 336, 407, 447):
        o = 64 // math.gcd(64, a)
        C = 4 * o if o > 1 else 1
        D = 7 * C
        f = D * P
        h = H.reshape(-1, f).sum(axis=0)
        i = np.arange(D)[:, None]
        k = np.arange(P)[None, :]
        h = h[i + D * ((k - i) * pow(D, -1, P) % P)]
        z = pow(g, (d - 1) // f, d)
        Y = pow(z, P * pow(P, -1, D), d)
        T = pow(z, D * pow(D, -1, P), d)
        v = (dft(D, Y, d) @ h % d) @ dft(P, T, d) % d
        units = [x for x in range(1, D) if math.gcd(x, D) == 1]
        v = v[units, 1:]
        ex = (d - 1) // P
        out = np.ones_like(v)
        while ex:
            if ex % 2:
                out = out * v % d
            v = v * v % d
            ex //= 2
        mu = roots(pow(g, (d - 1) // P, d), P, d)
        ix = np.argsort(mu)
        logs = ix[np.searchsorted(mu[ix], out)]
        assert np.array_equal(mu[logs], out)
        cl = {pow(5, i, C): i for i in range(o)}
        cl.update({-v % C: i for v, i in list(cl.items())})
        weights = (
            np.array([eta[i % 7] * pow(5, -351 * a * cl[i % C], P) for i in units])[
                :, None
            ]
            * np.array([pow(i, -296 * a, P) for i in range(1, P)])[None, :]
            % P
        )
        val = int(np.sum(logs * weights)) % P
        assert val == {276: 12, 336: 234, 407: 48, 447: 215}[a]
        print(a, D, val, flush=True)


if __name__ == "__main__":
    run()
