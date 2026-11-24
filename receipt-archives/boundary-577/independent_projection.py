"""Independent local order-577^2 calculation with quartic coefficients and exact integer convolution."""

import argparse
import time
import numpy as np
from gmpy2 import mpz

P = 577
M = P**2
MOD = P**3
D = P * (P - 1)
C = 256
IDX = np.arange(M, dtype=np.int64)
T = pow(20, M, MOD)
TS = np.array([pow(T, i, MOD) for i in range(64)], dtype=np.int64)
G = pow(5, P, M)
E = 265256
NOW = time.monotonic()


def say(*x):
    print(round(time.monotonic() - NOW, 1), *x, flush=True)


def packed(a):
    v = np.zeros((4, 2 * M, 3), dtype="<u4")
    v[:, :M, 0] = a
    return mpz.from_bytes(v.tobytes(), "little")


def mul(a, b):
    v = np.frombuffer(
        (packed(a) * packed(b)).to_bytes(16 * M * 12, "little"), dtype="<u4"
    ).reshape(8, 2 * M, 3)
    # 96-bit digits. A raw digit is at most 4*m*(MOD-1)^2 < 2^96.
    q = (
        v[:, :, 0].astype(np.int64)
        + v[:, :, 1].astype(np.int64) * (2**32 % MOD)
        + v[:, :, 2].astype(np.int64) * (2**64 % MOD)
    ) % MOD
    q = (q[:, :M] + q[:, M:]) % MOD
    return (q[:4] + T * q[4:]) % MOD


def pw(v, n):
    if n == 0:
        o = np.zeros_like(v)
        o[0, 0] = 1
        return o
    a = v
    for b in bin(n)[3:]:
        a = mul(a, a)
        if b == "1":
            a = mul(a, v)
    return a


def act(v, k, fr=1):
    li = IDX * pow(k, -1, M) % M
    return v[:, li] * TS[(np.arange(4) * (fr - 1) // 4) % 64, None] % MOD


def kernel(hist):
    # Store the input in independent CRT order; run through the 32
    # representatives on the 256th root before taking the remaining norm 36.
    H = np.empty((256, M), dtype=np.uint16)
    for i in range(256):
        H[i] = hist[IDX + M * ((i - IDX) * pow(M, -1, 256) % 256)]
    lg = {}
    for k in range(64):
        s = pow(5, k, 256)
        lg[s] = lg[-s % 256] = k
    i = np.arange(256)
    a = None
    for u in range(1, 64, 2):
        raw = np.zeros((4, M), dtype=np.int64)
        ix = i * u % 256
        for b in range(4):
            mask = ix % 4 == b
            raw[b] = TS[ix[mask] // 4] @ H[mask] % MOD
        raw = act(raw, pow(G, 441 * lg[u], M))
        a = raw if a is None else mul(a, raw)
        if u % 16 == 15:
            say("coset", u)
    zgen = pow(G, 441 * lg[65] + 64, M)
    h = 1
    for t in [3, 2, 3, 2]:
        v = a
        for j in range(1, t):
            a = mul(a, act(v, pow(zgen, h * j, M), pow(65, h * j, 256)))
        h *= t
    assert h == 36 and np.array_equal(a, act(a, zgen, 65))
    return a


def process(r):
    h = np.fromfile(f"hist-{r}.bin", dtype="<u2")
    assert int(h.sum()) == r - 2
    v = kernel(h)
    say("kernel")
    # Reversed generator and a different tame weight representative.
    for k in (1, 2, 4, 8, 16, 32):
        v = mul(v, pw(act(v, pow(G, k, M)), pow(T, -k, MOD)))
    say("tame")
    # Work directly at the exceptional exponent with the inverse wild generator.
    g = 1 - P
    w = pow(g, -(E + 1), M)
    a = v
    d = 1
    # Left-to-right twisted binary norm for the bits of 577.
    for bit in bin(P)[3:]:
        a = mul(a, pw(act(a, pow(g, d, M)), pow(w, d, M)))
        d *= 2
        if bit == "1":
            a = mul(a, pw(act(v, pow(g, d, M)), pow(w, d, M)))
            d += 1
    assert d == P
    v = pw(a, P - 1)
    # Align lower-layer embedding, as zeta_(256*p^2)^p has unramified part Y^p.
    v = v * TS[48 * np.arange(4) % 64, None] % MOD
    v = v.reshape(4, P, P)
    v = (v[:, :-1, :] - v[:, -1:, :]) % MOD
    v[0, 0, 0] = (v[0, 0, 0] - 1) % MOD
    np.save(f"alt-{r}-e265256.npy", v.astype("<u4"))
    say("completed independent specialization")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("prime", type=int, nargs="?", default=340919297)
    args = parser.parse_args()
    process(args.prime)
