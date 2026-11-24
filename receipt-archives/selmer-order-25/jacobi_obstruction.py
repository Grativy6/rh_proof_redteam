"""Exact local Jacobi-sum test. Coefficients live in cyclic group rings modulo 5**k."""

from math import comb, isqrt
import argparse
import numpy as np

try:
    from gmpy2 import mpz as integer
except ImportError:
    # Built-in integers use the same exact packing and can take longer.
    integer = int


def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def prime_factors(n):
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def generator(r):
    fs = prime_factors(r - 1)
    return next(g for g in range(2, r) if all(pow(g, (r - 1) // p, r) != 1 for p in fs))


def log_histogram(f, r, g):
    logs = np.zeros(r, dtype=np.int32)
    step = 8192
    short = np.array([pow(g, i, r) for i in range(step)], dtype=np.int64)
    inc = pow(g, step, r)
    scale = 1
    for j in range(0, r - 1, step):
        m = min(step, r - 1 - j)
        where = short[:m] * scale % r
        logs[where] = np.arange(j, j + m) % f
        scale = scale * inc % r
    exps = -(logs[2:] + logs[2:][::-1]) % f
    out = np.bincount(exps, minlength=f)
    assert int(out.sum()) == r - 2
    return out


def cyclic_mul(a, b, M):
    n = len(a)
    assert n * (M - 1) ** 2 < 2**64
    x = integer.from_bytes(np.asarray(a, dtype="<u8").tobytes(), "little")
    y = integer.from_bytes(np.asarray(b, dtype="<u8").tobytes(), "little")
    words = np.frombuffer((x * y).to_bytes(16 * n, "little"), dtype="<u8")
    return ((words[:n] + words[n:]) % M).astype(np.int64)


def norm_q_squares(J, q, m, M):
    f = m * q
    n = (q - 1) // 2
    h = 1 + m * ((5 - 1) * pow(m, -1, q) % q)
    assert pow(h, n, f) == 1 and all(pow(h, n // p, f) != 1 for p in prime_factors(n))
    idx = np.arange(f, dtype=np.int64)

    def acted(v, j):
        return v[(idx * pow(h, -j, f)) % f]

    def rec(k):
        if k == 1:
            return J
        v = rec(k // 2)
        z = cyclic_mul(v, acted(v, k // 2), M)
        if k % 2:
            z = cyclic_mul(z, acted(J, k - 1), M)
        return z

    a = rec(n)
    assert np.array_equal(a, acted(a, 1))
    return a


class Cyclo:
    def __init__(self, m, M):
        self.m = m
        self.M = M
        self.step = m // 5
        self.d = m - self.step
        self.one = np.r_[np.int64(1), np.zeros(self.d - 1, dtype=np.int64)]
        self.z = np.roll(self.one, 1)
        self.parameter = (2 * self.one - self.z - self.action(self.z, -1)) % M
        self.binom = [
            [(-1) ** j * comb(i, j) % M for i in range(j, self.d)]
            for j in range(self.d)
        ]

    def reduce(self, b):
        a = np.zeros(self.m, dtype=np.int64)
        for i in range(0, len(b), self.m):
            block = b[i : i + self.m]
            a[: len(block)] += block
        top = a[self.d :]
        for j in range(4):
            a[j * self.step : (j + 1) * self.step] -= top
        return a[: self.d] % self.M

    def mul(self, a, b):
        return self.reduce(np.convolve(a, b))

    def power(self, a, n):
        v = self.one
        while n:
            if n & 1:
                v = self.mul(v, a)
            a = self.mul(a, a)
            n //= 2
        return v

    def action(self, a, j):
        out = np.zeros(self.m, dtype=np.int64)
        out[np.arange(self.d) * j % self.m] = a
        return self.reduce(out)

    def vreal(self, a):
        best = None
        for j, row in enumerate(self.binom):
            h = int(np.dot(a[j:], row)) % self.M
            if not h:
                continue
            t = j
            while h % 5 == 0:
                h //= 5
                t += self.d
            best = t if best is None else min(best, t)
        if best is None:
            h = self.M
            t = 0
            while h % 5 == 0:
                h //= 5
                t += self.d
            return t // 2
        assert best % 2 == 0
        return best // 2


def projected_beta(q, m, r, M):
    f = q * m
    assert r % f == 1 and trial_prime(r)
    J = log_histogram(f, r, generator(r)) % M
    v = norm_q_squares(J, q, m, M)
    i = np.arange(m, dtype=np.int64)

    def at(j):
        return v[i + m * ((j - i) * pow(m, -1, q) % q)]

    nonsq = next(a for a in range(2, q) if pow(a, (q - 1) // 2, q) == q - 1)
    root = next(a for a in range(M) if (a * a + q) % M == 0)
    period = (-1 + root) * pow(2, -1, M) % M
    c = Cyclo(m, M)
    plus = c.reduce(at(0) + at(1) * period + at(nonsq) * (-1 - period))
    minus = c.reduce(at(0) + at(nonsq) * period + at(1) * (-1 - period))
    scalar = pow(r, (q - 1) // 2, M)
    assert np.array_equal(c.mul(plus, c.action(minus, -1)), scalar * c.one % M)
    beta = c.one
    for a in range(1, m):
        if a % 5 == 0:
            continue
        weight = pow(a, -2, m)
        if weight > m // 2:
            weight -= m
        side = plus if weight > 0 else minus
        ratio = c.mul(c.action(side, a), c.action(side, -a)) * pow(scalar, -1, M) % M
        beta = c.mul(beta, c.power(ratio, abs(weight)))
    assert np.array_equal(beta, c.action(beta, -1))
    return c, beta


def local_test(c, beta, n):
    M = c.M
    target = c.power(beta, 4)
    got = c.one.copy()
    e = c.d // 2
    cutoff = e * n + e // 4
    first = c.vreal((target - got) % M)
    corrections = []
    for j in range(1, e // 4 + 1):
        k = j
        for _ in range(n):
            k = min(5 * k, e + k)
        now = c.vreal((target - got) % M)
        if now > cutoff:
            return True, first, now, corrections
        if now < k:
            return False, first, now, corrections
        if now > k:
            continue
        digit = c.power((c.one + c.power(c.parameter, j)) % M, 5**n)
        assert c.vreal((digit - c.one) % M) == k
        for t in range(1, 5):
            new = c.mul(got, c.power(digit, t))
            if c.vreal((target - new) % M) > k:
                got = new
                corrections.append((j, t))
                break
        else:
            raise ValueError("residue field has a missing unit digit")
    now = c.vreal((target - got) % M)
    return now > cutoff, first, now, corrections


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--coefficients",
        action="store_true",
        help="print the reduced polynomial coefficients",
    )
    args = parser.parse_args()
    q, m, M, r = 2179, 125, 625, 5447501
    assert (
        r == 20 * m * q + 1
        and generator(r) == 2
        and prime_factors(r - 1) == [2, 5, 2179]
    )
    chi = [0] + [1 if pow(a, (q - 1) // 2, q) == 1 else -1 for a in range(1, q)]
    inv = [0 if i % 5 == 0 else pow(i, -2, m) for i in range(m)]
    k = sum((2 * a // (m * q)) * chi[a % q] * inv[a % m] for a in range(1, m * q)) % m
    assert k == 0
    c, b = projected_beta(q, m, r, M)
    results = [local_test(c, b, n) for n in (1, 2, 3)]
    assert [u[0] for u in results] == [True, True, False]
    assert results[-1][1:] == (
        75,
        161,
        [(1, 2), (2, 2), (3, 4), (4, 2), (5, 3), (6, 2), (8, 1), (10, 2), (12, 2)],
    )
    print(
        "Every Jacobi divisor is a multiple of 125. The local fifth and 25th powers exist."
    )
    print(
        "For a 125th power the first unmatched digit is 161; the neighboring permitted digits are 160 and 163."
    )
    if args.coefficients:
        print(b.tolist())


if __name__ == "__main__":
    main()
