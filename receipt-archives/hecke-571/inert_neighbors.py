"""Hyperspecial two-step neighbours in the inert computations at 3 and 5."""

from itertools import product
import numpy as np
from operators import IDENTITY, P, SIGNED, times
from split_neighbors import (
    ONE,
    ZERO,
    OMEGA,
    cmul,
    cadd,
    conj,
    cpow,
    norm,
    dot,
    vectors_of_norm,
    find_frame,
    modular_matrix,
    tau,
    transpose,
    check_integral_frame,
)


def reduced(a, modulus):
    return a[0] % modulus, a[1] % modulus


def inverse_ring(a, modulus):
    n = pow(norm(a), -1, modulus)
    c, d = conj(a)
    return c * n % modulus, d * n % modulus


def level_vector(target, p):
    v, t = target
    pivot = next(i for i, a in enumerate(v) if a != ZERO)
    z = list(v)
    z[pivot] = cadd(z[pivot], (p * t[0], p * t[1]))
    return z


def target_code(z, p):
    modulus = p * p
    pivot = next(i for i, a in enumerate(z) if reduced(a, p) != ZERO)
    inv = inverse_ring(z[pivot], modulus)
    lifted = [reduced(cmul(a, inv), modulus) for a in z]
    v = tuple(reduced(a, p) for a in lifted)
    dy = [((a - c) // p, (b - d) // p) for (a, b), (c, d) in zip(lifted, v)]
    t = reduced(dot(v, dy), p)
    assert dot(v, v)[0] % p == 0 and (dot(v, v)[0] // p + 2 * t[0] + t[1]) % p == 0
    return v, t


def all_targets(p):
    field = tuple(product(range(p), repeat=2))
    for pivot in range(3):
        for tail in product(field, repeat=2 - pivot):
            v = (ZERO,) * pivot + (ONE,) + tail
            h = sum(norm(a) for a in v)
            if h % p:
                continue
            for t in field:
                if (h // p + 2 * t[0] + t[1]) % p == 0:
                    yield v, t


def target_orbits(i, p):
    modulus = p * p
    matrices = [tuple((x, 0) for x in g) for g in SIGNED]
    inverses = [tuple(x % P for x in transpose(g)) for g in SIGNED]
    if i:
        numer = ((-1, 0), (1, -1), (1, 0), (-1, 0), (-1, 1), (1, 0), (0, 1), (0, 0), (0, 1))
        inv2 = pow(2, -1, modulus)
        matrices.append(tuple((a * inv2 % modulus, b * inv2 % modulus) for a, b in numer))
        inverses.append(transpose(tau(1 - 159, P)))
    targets = list(all_targets(p))
    assert len(targets) == p * (p**3 + 1) == len(set(targets))
    seen = set()
    for target in targets:
        if target in seen:
            continue
        orbit = {target: IDENTITY}
        queue = [target]
        for t in queue:
            z = level_vector(t, p)
            for g, inv in zip(matrices, inverses):
                out = []
                for a in range(3):
                    x, y, k = [cmul(g[3 * a + b], z[b]) for b in range(3)]
                    out.append(cadd(x, cadd(y, k)))
                h = target_code(out, p)
                if h not in orbit:
                    orbit[h] = times(orbit[t], inv)
                    queue.append(h)
        assert not seen.intersection(orbit)
        seen.update(orbit)
        yield target, orbit
    assert seen == set(targets)


def matching_indices(values, target, p):
    v, t = target
    z = np.array(v, dtype=np.int64)
    pivot = next(i for i, c in enumerate(v) if c != ZERO)
    c = values[:, pivot, :] % p
    a, b = c[:, 0, None], c[:, 1, None]
    u, h = z[:, 0], z[:, 1]
    dx = values[:, :, 0] - (a * u - 2 * b * h)
    dy = values[:, :, 1] - (a * h + b * u + b * h)
    first = np.flatnonzero(np.all(dx % p == 0, axis=1) & np.all(dy % p == 0, axis=1))
    xx, yy = dx[first] // p, dy[first] // p
    val0 = xx @ (u + h) + 2 * (yy @ h)
    val1 = yy @ u - xx @ h
    a, b = c[first, 0], c[first, 1]
    ok = ((val0 - (a * t[0] - 2 * b * t[1])) % p == 0) & (
        (val1 - (a * t[1] + b * t[0] + b * t[1])) % p == 0
    )
    return first[ok]


def inert_denominators(i, j, p):
    lam = cmul((p, 0), cmul(cpow(OMEGA, j), cpow(conj(OMEGA), i)))
    det = cmul((p**3, 0), cmul(cpow(OMEGA, i + 2 * j), cpow(conj(OMEGA), 2 * i + j)))
    return lam, det


def inert_blocks(p):
    # The quadratic ring must be unramified and nonsplit at this odd prime.
    assert p in (3, 5) and pow(-7 % p, (p - 1) // 2, p) == p - 1
    blocks = [[[], []], [[], []]]
    certs = []
    for i in range(2):
        for target, orbit in target_orbits(i, p):
            for j in (0, 1):
                lam, det = inert_denominators(i, j, p)
                r = norm(lam)
                allv = vectors_of_norm(r)
                vals = allv[matching_indices(allv, target, p)]

                def accepts(third):
                    return bool(len(matching_indices(np.asarray([third]), target, p)))

                cols = find_frame(vals, r, det, i, j, accepts)
                if cols is not None:
                    break
            else:
                raise RuntimeError(f"missing a unitary isometry for {(i, target)}")
            check_integral_frame(cols, r, det, i, j)
            assert len(matching_indices(np.asarray(cols), target, p)) == 3
            assert any(
                target_code(c, p) == target for c in cols if any(reduced(a, p) != ZERO for a in c)
            )
            certs.append((i, j, len(orbit)))
            inv = transpose(modular_matrix(cols, lam, 1 - 159, P))
            blocks[i][j].extend(times(inv, a) for a in orbit.values())
        assert sum(map(len, blocks[i])) == p * (p**3 + 1)
    return blocks, certs
