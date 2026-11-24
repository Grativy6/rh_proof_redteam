"""Compute the two real circular-unit norm targets for the four slope tests."""

from math import factorial
from pathlib import Path
import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "fixed-character-577"))
from bounds import char2
from fourier_witness import primitive, roots
from dual_primes import P, Ring, act

C = 256
MOD = P**2


def kernel_norm(ring, j):
    """Norm of 1-Y^(5^j)Z over the kernel of z, using its 128 linear factors."""
    out = ring.one.copy()
    for k in range(8):
        a = pow(5, j + 8 * k, C)
        for sign in (-1, 1):
            h = sign * a % C
            for b in range(8):
                t = pow(5, 45 * k + 72 * b, P)
                rotated = np.roll(np.roll(out, t, axis=1), h % 4, axis=0)
                if h % 4:
                    rotated[: h % 4] = rotated[: h % 4] * ring.t % MOD
                out = (out - pow(ring.t, h // 4, MOD) * rotated) % MOD
    return out


def inertia_product(ring, x, weight):
    g = pow(5, P, MOD)
    stride = 1
    result = x
    for factor in (2, 2, 2, 3, 3):
        block = result
        for j in range(1, factor):
            conjugate = act(block, pow(5, stride * j, P))
            exponent = pow(g, 296 * weight * stride * j, MOD)
            result = ring.mul(result, ring.pw(conjugate, exponent))
        stride *= factor
    assert stride == 72
    return result


def local_readings():
    ring = Ring(MOD, pow(20, P, MOD), 4)
    g = pow(5, P, MOD)
    factors = [kernel_norm(ring, j) for j in range(8)]
    for weight, n, expected in [(1, 280, [0, 0, 0, 78]), (-1, 296, [0, 496, 0, 0])]:
        unit = ring.one.copy()
        for j, base in enumerate(factors):
            value = inertia_product(ring, base, weight)
            unit = ring.mul(unit, ring.pw(value, pow(g, 351 * j * weight, MOD)))
        w = ring.pw(unit, P - 1)
        w = (w[:, :-1] - w[:, -1, None]) % MOD
        w[0, 0] = (w[0, 0] - 1) % MOD
        if weight == 1:
            assert not np.any(w % P)
            w = w // P
        # Z=exp(X) in the truncated residue polynomial. Verify all earlier
        # coefficients vanish, then extract the first possible tame digit.
        j = np.arange(P - 1, dtype=np.int64)
        exp = np.ones(P - 1, dtype=np.int64)
        for degree in range(n + 1):
            values = w @ exp % P
            if degree < n:
                assert not np.any(values)
            exp = exp * j % P * pow(degree + 1, -1, P) % P
        assert values.tolist() == expected
    # Independent finite sum for the z-sector digit.
    phi = char2(-1)
    inv = [pow(v, -1, P) if v else 0 for v in phi]
    b = sum(
        pow(h, 295, P) * sum(t * inv[(h + P * t) % C] for t in range(C))
        for h in range(1, P)
    )
    b = b * pow(C * factorial(296), -1, P) % P
    tau = [
        sum(phi[j] * pow(20, j // 4, P) for j in range(i, C, 4)) % P for i in range(4)
    ]
    assert b == 31 and tau == [0, 16, 0, 0] and b * tau[1] % P == 496
    lower = -78 * 20 % P
    upper = -496 % P
    assert (lower, upper, 8 * lower % P, 8 * upper % P) == (171, 81, 214, 71)
    assert -389 * 214 * pow(495, -1, P) % P == 16 and 2 * 71 == 142
    print(
        "Base-unit coefficients 171 and 81. First norm-lift row (214,16,0) after removing the upper direction."
    )


def base_residue(r):
    """Read the unique global root by taking one p-squared residue symbol."""
    g = primitive(r)
    Y = roots(pow(g, (r - 1) // C * pow(P, -1, C), r), C, r)
    Z = roots(pow(g, (r - 1) // P * pow(C, -1, P), r), P, r)
    v = np.arange(1, C, 2)
    teich = np.array(char2(modulus=MOD), dtype=np.int64)
    wild = np.array([pow(t, 296 * P, MOD) for t in range(1, P)], dtype=np.int64)
    weights = teich[v, None] * wild[None, :] % MOD
    x = (1 - Y[v, None] * Z[None, 1:]) % r
    values = np.ones_like(x)
    while np.any(weights):
        values = np.where(weights % 2, values * x % r, values)
        weights //= 2
        x = x * x % r
    values = values.ravel()
    while len(values) > 1:
        if len(values) % 2:
            values = np.append(values, 1)
        values = values[::2] * values[1::2] % r
    raw = int(values[0])
    symbol = pow(raw, (r - 1) // MOD, r)
    mu = pow(g, (r - 1) // P, r)
    idx = next(i for i in range(P) if pow(mu, i, r) == symbol)
    return raw, symbol, idx


def finite_reciprocity():
    for r, unram, ram, expected in [
        (340919297, 507, 514, (314362705, 256025499, 26, 330)),
        (1022757889, 101, 367, (59948425, 681724258, 488, 557)),
    ]:
        raw, symbol, idx = base_residue(r)
        h = (406 * unram + 178 * ram) % P
        local = 8 * 223 * h * 171 % P
        assert local == (P - 1) * 298 * idx % P
        # Different lifts of the projector exponents may change raw by a
        # p^2-th power. These values use the direct least residues above.
        assert (raw, symbol, idx, local) == expected
        print(
            "Split prime",
            r,
            "root exponent",
            idx,
            "reciprocity sum on either side",
            local,
        )


if __name__ == "__main__":
    local_readings()
    finite_reciprocity()
