"""Verify the weight-two cuspidal summand and its trace valuations at level 15253.

Requires Python 3 and NumPy. The integral Manin matrices are rebuilt from the
level. Both charts are untrusted coordinates, checked against the full space.
"""

import base64
import json
import zlib
from pathlib import Path
import numpy as np
from weight_two_symbols import Cusp

MODULUS = 5**6
LEVEL = 7 * 2179
PRIMES = (2, 3, 5, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 71, 79)


def legendre(x, p):
    return {0: 0, 1: 1, p - 1: -1}[pow(x % p, (p - 1) // 2, p)]


def full_rank_mod5(matrix):
    work = (matrix % 5).astype(np.uint8)
    n = len(work)
    for h in range(n):
        nz = np.flatnonzero(work[h:, h])
        if not len(nz):
            return False
        j = h + int(nz[0])
        if j != h:
            work[[h, j], h:] = work[[j, h], h:]
        v = work[h, h:] * pow(int(work[h, h]), -1, 5) % 5
        a = work[h + 1 :, h:]
        mult = (5 - a[:, 0, None]) % 5
        a[:] = (a + mult * v) % 5
    return True


def read_chart(encoded):
    raw = zlib.decompress(base64.b64decode(encoded, validate=True))
    assert len(raw) == 1450 * 2 * 2
    return np.frombuffer(raw, dtype="<u2").astype(np.int64).reshape(1450, 2)


def check_sign(sign, encoded):
    mod = MODULUS
    space = Cusp(sign, mod)
    assert (len(space.reps), len(space.brow), space.n) == (1452, 2, 1450)
    chart = read_chart(encoded)
    assert np.array_equal(chart[:2], np.eye(2, dtype=np.int64))
    t2 = space.apply(2, np.eye(space.n, dtype=np.int64))
    assert np.array_equal(t2 @ chart % mod, chart * 1999 % mod)
    # T2+1 on the quotient by the graph of chart[2:]. Invertibility
    # proves this chart exhausts the generalized (-1)-space.
    primary = t2 + np.eye(space.n, dtype=np.int64)
    quotient = (primary[2:, 2:] - chart[2:] @ primary[:2, 2:]) % 5
    assert full_rank_mod5(quotient)
    ops = {}
    for p in PRIMES:
        im = space.apply(p, chart)
        op = im[:2]
        assert np.array_equal(im, chart @ op % mod)
        ops[p] = op
    identity = np.eye(2, dtype=np.int64)
    lam, mu = 14879, 746
    e = (ops[3] - mu * identity) * pow(lam - mu, -1, mod) % mod
    assert np.array_equal(e @ e % mod, e) and int(np.trace(e)) % mod == 1
    assert np.array_equal(ops[3], (lam * e + mu * (identity - e)) % mod)
    vals = {}
    for p, op in ops.items():
        a = int(np.trace(op @ e)) % mod
        b = int(np.trace(op @ (identity - e))) % mod
        assert np.array_equal(op @ e % mod, a * e % mod)
        assert np.array_equal(op @ (identity - e) % mod, b * (identity - e) % mod)
        chi = legendre(p, 7) * legendre(p, 2179)
        assert (a - 1 - chi * p) % 125 == 0
        assert (b - legendre(p, 7) * a) % mod == 0
        vals[p] = (a, b)
    return vals


def main():
    weights = [legendre(a, 7) * legendre(a, 2179) for a in range(LEVEL)]
    assert sum(weights) == sum(a * w for a, w in enumerate(weights)) == 0
    b2, rest = divmod(sum(a * a * w for a, w in enumerate(weights)), LEVEL)
    assert b2 == 166000 and rest == 0
    charts = json.loads(
        Path(__file__).with_name("weight_two_charts.json").read_text(encoding="ascii")
    )
    plus = check_sign(1, charts["1"])
    assert plus == check_sign(-1, charts["-1"])
    print("B2 =", b2, "; signed cuspidal spaces both have dimension 1450.")
    print("T2+1 is invertible on both 1448-dimensional quotients modulo 5.")
    a5 = plus[5][0]
    assert a5 == 4621 and legendre(5, 7) * legendre(5, 2179) == -1
    roots = [x for x in range(1, MODULUS, 5) if (x * x - a5 * x - 5) % MODULUS == 0]
    assert roots == [3376] and (pow(roots[0], 4, MODULUS) - 1) % MODULUS == 13500
    print("Ordinary unit root at 5 is 3376 modulo 15625; v5(root^4-1) = 3.")
    print("T3 roots modulo", MODULUS, ":", plus[3])
    for p in [11, 23, 29, 37, 43]:
        a, b = plus[p]
        psi = legendre(p, 2179)
        assert legendre(p, 7) == 1 and a == b
        target = 1 + psi * p
        diff = (a - target) * (a + target) % MODULUS
        v = next((i for i in range(6) if diff % 5 ** (i + 1)), 6)
        assert v == {11: 4, 23: 3, 29: 4, 37: 3, 43: 6}[p]
        print(
            f"p={p}, a_p mod {MODULUS}={a}, target={target}, adjoint valuation {'>=' if v == 6 else '='}{v}"
        )


if __name__ == "__main__":
    main()
