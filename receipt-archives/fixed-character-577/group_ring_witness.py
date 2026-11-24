"""Independent packed-integer group-ring replay at the fixed conductor 256."""

from pathlib import Path
import numpy as np
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "selmer-order-25"))
import jacobi_obstruction as jj
from fourier_witness import primitive as generator, roots, factors

L = 577
C = 256
F = C * L
G = 5
IDX = np.arange(F, dtype=np.int64)


def crt(x, y):
    return int(x + C * ((y - x) * pow(C, -1, L) % L)) % F


def act(v, k):
    return v[IDX * pow(k, -1, F) % F]


def mul(a, b, m):
    return jj.cyclic_mul(a, b, m)


def power(v, n, m):
    if n == 0:
        u = np.zeros(F, dtype=np.int64)
        u[0] = 1
        return u
    u = v
    for bit in bin(n)[3:]:
        u = mul(u, u, m)
        if bit == "1":
            u = mul(u, v, m)
    return u


def kergen():
    return [(crt(-1, 1), 2), (crt(1, pow(G, 64, L)), 9), (crt(5, pow(G, 441, L)), 64)]


def ker_norm(v, m):
    for g, n in kergen():
        h = 1
        for p in {2: [2], 9: [3, 3], 64: [2] * 6}[n]:
            src = v
            for j in range(1, p):
                v = mul(v, act(src, pow(g, h * j, F)), m)
            h *= p
        assert h == n and np.array_equal(v, act(v, g))
    return v


SIG = crt(1, pow(G, -1, L))


def proj(v, m):
    for h in [1, 2, 4, 8, 16, 32]:
        v = mul(v, power(act(v, pow(SIG, h, F)), pow(20, h, L), m), m)
    return v


def tensor(v, m):
    a = np.arange(C, dtype=np.int64)[:, None]
    b = np.arange(L, dtype=np.int64)[None, :]
    q = v[a + C * ((b - a) * pow(C, -1, L) % L)]
    q = (q[: C // 2] - q[C // 2 :]) % m
    return (q[:, :-1] - q[:, -1, None]) % m


def ksum():
    psi = [0] * C
    for i in range(64):
        a = pow(5, i, C)
        psi[a] = psi[-a % C] = pow(5, 9 * 39 * i, L)
    a = np.arange(F // 2 + 1, F, 2, dtype=np.int64)
    a = a[a % L != 0]
    return sum(pow(psi[int(k) % C] * pow(int(k), 297, L), -1, L) for k in a) % L


def run(r, ds):
    assert ksum() == 0
    print("divisor exponent", ksum(), flush=True)
    assert r % F == 1 and factors(r) == [r]
    J = jj.log_histogram(F, r, generator(r))
    m = L * L
    K = ker_norm(J % m, m)
    z = proj(K, m)
    w = tensor(power(z, L - 1, m), m)
    w[0, 0] = (w[0, 0] - 1) % m
    assert (
        np.count_nonzero(w % L) == 0
        and np.count_nonzero(np.sum(w // L, axis=1) % L) == 0
        and np.count_nonzero(w) == 36244
    )
    print(
        "local mod 577 nonzero coeffs",
        np.count_nonzero(w % L),
        "derivative residue",
        np.count_nonzero(np.sum(w // L, axis=1) % L),
        flush=True,
    )
    print("nonzero mod 577^2", np.count_nonzero(w), flush=True)
    for d in ds:
        assert d % F == 1 and d != r and factors(d) == [d]
        assert F * (d - 1) ** 2 < 2**63
        K = ker_norm(J % d, d)
        exp = roots(pow(generator(d), (d - 1) // F, d), F, d)
        a = 1
        for j in range(64):
            val = int(K @ exp[IDX * pow(SIG, j, F) % F]) % d
            a = a * pow(val, pow(20, j, L), d) % d
        b = pow(a, (d - 1) // L, d)
        print("d", d, "beta", a, "root-of-unity reading", b, flush=True)
        assert (a, b) == (628907, 1497311)
        return


if __name__ == "__main__":
    run(1920257, [2363393])
