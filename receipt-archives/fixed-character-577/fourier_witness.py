"""Check the local and global Kummer readings independently via two finite Fourier calculations."""

import math
import numpy as np

L = 577
C = 256
F = C * L
R = 1920257
D = 2363393


def factors(n):
    ans = []
    for p in range(2, math.isqrt(n) + 1):
        if n % p == 0:
            ans.append(p)
            while n % p == 0:
                n //= p
    if n > 1:
        ans.append(n)
    return ans


def primitive(p):
    assert factors(p) == [p]
    return next(
        z
        for z in range(2, p)
        if all(pow(z, (p - 1) // a, p) != 1 for a in factors(p - 1))
    )


def roots(g, n, p):
    v = np.empty(n, dtype=np.int64)
    z = 1
    for k in range(n):
        v[k] = z
        z = z * g % p
    assert z == 1
    return v


def histogram():
    g = primitive(R)
    log = np.empty(R, dtype=np.int32)
    x = 1
    i = 0
    for _ in range(1, R):
        log[x] = i
        x = x * g % R
        i = (i + 1) % F
    assert x == 1 and i == 0
    exponents = -(log[2:] + log[:1:-1]) % F
    h = np.bincount(exponents, minlength=F)
    a = np.arange(C)[:, None]
    b = np.arange(L)[None, :]
    return h[a + C * ((b - a) * pow(C, -1, L) % L)]


def character(v):
    for i in range(64):
        a = pow(5, i, C)
        if v in (a, -a % C):
            return pow(5, 9 * 39 * i, L)
    raise ValueError("not a unit")


def dft(x, root, p):
    return roots(root, x, p)[np.outer(np.arange(x), np.arange(x)) % x]


def detect(h):
    g = primitive(D)
    z = pow(g, (D - 1) // F, D)
    a = pow(z, L * pow(L, -1, C), D)
    b = pow(z, C * pow(C, -1, L), D)
    values = (dft(C, a, D) @ h % D) @ dft(L, b, D) % D
    # Keep only the character of the residue, an element of mu_577.
    logs = roots(pow(g, (D - 1) // L, D), L, D)
    logmap = {int(x): k for k, x in enumerate(logs)}
    zlog = 0
    for v in range(1, C, 2):
        psi = character(v)
        for u in range(1, L):
            root = pow(int(values[v, u]), (D - 1) // L, D)
            zlog += logmap[root] * pow(psi * pow(u, 297, L), -1, L)
    return int(logs[zlog % L]), zlog % L


def reduce_product(matrix):
    # The unramified field is F_577[Y]/(Y^4-20).
    out = np.zeros((len(matrix), 4), dtype=np.int64)
    for i in range(4):
        for j in range(4):
            out[:, (i + j) % 4] += matrix[:, i, j] * (20 if i + j >= 4 else 1)
    return out % L


def times(a, b):
    return reduce_product(a[:, :, None] * b[:, None, :])


def power(a, n):
    r = np.zeros_like(a)
    r[:, 0] = 1
    while n:
        if n % 2:
            r = times(r, a)
        n //= 2
        a = times(a, a)
    return r


def local_digit(h):
    # Substitute zeta_577=exp(X); only the weight-297 logarithmic coefficient
    # can survive the sum over the tame inertia characters.
    degree = 297
    units = np.arange(1, C, 2)
    y = roots(20, 64, L)
    jcoef = np.empty((len(units), degree + 1, 4), dtype=np.int64)
    a = np.arange(C)
    k = np.arange(L)
    moments = np.ones((L, degree + 1), dtype=np.int64)
    for j in range(1, degree + 1):
        moments[:, j] = moments[:, j - 1] * k * pow(j, -1, L) % L
    for i, u in enumerate(units):
        yexp = (a * u) % C
        for v in range(4):
            mask = yexp % 4 == v
            coeff = y[yexp[mask] // 4] @ h[mask] % L
            jcoef[i, :, v] = coeff @ moments % L
    inv = power(jcoef[:, 0, :], L**4 - 2)
    assert np.array_equal(
        times(jcoef[:, 0, :], inv), np.tile([1, 0, 0, 0], (len(units), 1))
    )
    logs = np.zeros_like(jcoef)
    for n in range(1, degree + 1):
        convolution = np.einsum(
            "vji,vjk->vik", jcoef[:, 1:n, :], logs[:, n - 1 : 0 : -1, :], optimize=False
        )
        term = (n * jcoef[:, n, :] - reduce_product(convolution)) % L
        logs[:, n, :] = times(term, inv)
    # Nearby character labels give visible nonzero digits with the same Jacobi sum.
    for label, expected in ((37, 416), (41, 70)):
        exponent = -label * pow(39, -1, 64) % 64
        controls = np.array([pow(character(int(u)), exponent, L) for u in units])
        value = (controls @ logs[:, degree, :]) * pow(degree, -1, L) % L
        assert value.tolist() == [0, 0, 0, expected]
    weight = np.array([pow(character(int(u)), -1, L) for u in units])
    terms = logs[:, degree, :] * weight[:, None] * pow(degree, -1, L) % L
    partial = [np.sum(terms[units % 8 == c], axis=0) % L for c in [1, 3, 5, 7]]
    return (
        [x.tolist() for x in partial],
        np.sum(terms, axis=0) % L,
        np.count_nonzero(np.any(terms, axis=1)),
    )


def prime_inputs():
    return (
        all(factors(p) == [p] for p in (L, R, D))
        and R % F == D % F == 1
        and pow(20, 32, L) == L - 1
        and pow(20, 64, L) == 1
    )


def main():
    h = histogram()
    assert h.shape == (256, 577) and int(h.sum()) == R - 2 and prime_inputs()
    detected = detect(h)
    assert detected == (1497311, 333) and pow(detected[0], 577, D) == 1
    print("Detecting prime", D, "(root, discrete exponent)", detected, flush=True)
    a, b, k = local_digit(h)
    assert (
        a == [[0, 64, 0, 0], [0, 513, 0, 0], [0, 513, 0, 0], [0, 64, 0, 0]]
        and not np.any(b)
        and k == 128
    )
    print(
        "Local projection subtotals",
        a,
        "sum",
        b.tolist(),
        "nonzero terms",
        k,
        flush=True,
    )


if __name__ == "__main__":
    main()
