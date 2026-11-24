"""Assemble both directed Hecke operators at 2 on the signed line orbits at 571."""

from array import array
from pathlib import Path

import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_unitary_level_571 import (
    IDENTITY,
    INV,
    LEGENDRE,
    LINES,
    P,
    SIGNED,
    determinant,
    group,
    move,
    neighbours,
    normalize,
    times,
    transposed,
    vector,
)


class Fiber:
    """Orbit representatives, their signed coordinates, and their integration weights."""

    def __init__(self, generators, group_order):
        self.coordinates = array("i", [0]) * LINES
        self.representatives = []
        self.weights = []
        visited = bytearray(LINES)
        actions = [(g, LEGENDRE[determinant(g)]) for g in generators]
        for seed in range(LINES):
            if visited[seed]:
                continue
            orbit = [seed]
            visited[seed] = 1
            supported = True
            for j in orbit:
                x, y, z = vector(j)
                for (a, b, c, d, e, f, g, h, i), det_sign in actions:
                    dest, scale = normalize(
                        (a * x + b * y + c * z) % P,
                        (d * x + e * y + f * z) % P,
                        (g * x + h * y + i * z) % P,
                    )
                    sign = visited[j] if det_sign * LEGENDRE[scale] == 1 else 3 - visited[j]
                    if not visited[dest]:
                        visited[dest] = sign
                        orbit.append(dest)
                    elif visited[dest] != sign:
                        supported = False
            if supported:
                self.representatives.append(vector(seed))
                self.weights.append(len(orbit) * (336 // group_order))
                index = len(self.representatives)
                for j in orbit:
                    self.coordinates[j] = index if visited[j] == 1 else -index


def scaled_identity_plus_ones(t):
    return tuple((u + t) % P for u in IDENTITY)


def operators_at_two(w, tau, big_group):
    pos, neg = neighbours(w), neighbours((1 - w) % P)
    delta = scaled_identity_plus_ones(INV[w * w % P])
    delta_inv = scaled_identity_plus_ones(INV[(1 - w) ** 2 % P])
    assert times(delta, delta_inv) == IDENTITY
    assert all(times(times(delta_inv, g), delta) in big_group for g in SIGNED)
    powers = [IDENTITY]
    for _ in range(6):
        powers.append(times(powers[-1], tau))
    assert len(set(powers)) == 7 and times(powers[-1], tau) == IDENTITY
    forward = (([transposed(g) for g in neg], [IDENTITY]), ([times(delta, h) for h in powers], []))
    backward = (([transposed(g) for g in pos], [delta_inv]), (powers, []))
    return forward, backward


def assemble(fibers, blocks):
    rows = []
    offsets = (0, len(fibers[0].representatives))
    for i, src in enumerate(fibers):
        for v in src.representatives:
            row = {}
            for j, dest in enumerate(fibers):
                for g in blocks[i][j]:
                    k, scale = move(g, v)
                    coord = dest.coordinates[k]
                    if coord:
                        h = offsets[j] + abs(coord) - 1
                        value = LEGENDRE[determinant(g)] * LEGENDRE[scale]
                        row[h] = row.get(h, 0) + (value if coord > 0 else -value)
            rows.append({h: a for h, a in row.items() if a})
    return rows


def product_row(row, other):
    out = {}
    for j, a in row.items():
        for k, b in other[j].items():
            out[k] = out.get(k, 0) + a * b
    return {k: a for k, a in out.items() if a}


def verify_pair(a, b, weights):
    for x, y in ((a, b), (b, a)):
        for i, row in enumerate(x):
            assert all(weights[i] * v == weights[j] * y[j].get(i, 0) for j, v in row.items())
    assert all(product_row(ai, b) == product_row(bi, a) for ai, bi in zip(a, b))


def matrix_market(path, rows):
    with Path(path).open("w", encoding="ascii", newline="\n") as f:
        f.write("%%MatrixMarket matrix coordinate integer general\n")
        f.write(f"{len(rows)} {len(rows)} {sum(map(len, rows))}\n")
        for i, row in enumerate(rows, 1):
            for j, a in sorted(row.items()):
                f.write(f"{i} {j + 1} {a}\n")


def build():
    w = 159
    assert (w * w - w + 2) % P == 0
    signed = [tuple(x % P for x in g) for g in SIGNED]
    tau = tuple(x * INV[2] % P for x in (-1, 1 - w, 1, -1, w - 1, 1, w, 0, w))
    big = signed + [tau]
    fibers = [Fiber(signed, 48), Fiber(big, 336)]
    assert [len(f.representatives) for f in fibers] == [13396, 1874]
    directions = operators_at_two(w, tau, group(big, 336))
    a, b = (assemble(fibers, blocks) for blocks in directions)
    weights = fibers[0].weights + fibers[1].weights
    verify_pair(a, b, weights)
    return fibers, a, b, weights


def entries(fibers, blocks):
    """Yield one neighbour's signed destination on every source orbit in its block."""
    offsets = (0, len(fibers[0].representatives))
    inverse = np.array(INV, dtype=np.int32)
    leg = np.array(LEGENDRE, dtype=np.int32)
    coords = [np.asarray(f.coordinates) for f in fibers]
    for i, f in enumerate(fibers):
        reps = np.array(f.representatives, dtype=np.int32).T.copy()
        rows = np.arange(offsets[i], offsets[i] + reps.shape[1], dtype=np.int32)
        for j, matrices in enumerate(blocks[i]):
            for g in matrices:
                x, y, z = np.array(g, dtype=np.int32).reshape(3, 3) @ reps % P
                scale = np.where(x, x, np.where(y, y, z))
                inv = inverse[scale]
                idx = np.where(
                    x,
                    (y * inv % P) * P + (z * inv % P),
                    np.where(y, P * P + (z * inv % P), P * P + P),
                )
                coord = coords[j][idx]
                sign = np.sign(coord) * leg[scale] * LEGENDRE[determinant(g)]
                dest = np.maximum(abs(coord) - 1, 0) + offsets[j]
                yield rows, dest, sign


def apply_batch(fibers, blocks, vectors):
    a = np.asarray(vectors, dtype=np.int32)
    # Each coordinate of the inputs is at most four for the modular runs.
    out = np.zeros(a.shape, dtype=np.int64)
    for rows, dest, sign in entries(fibers, blocks):
        out[rows] += a[dest] * sign[:, None]
    return out


def sparse_table(fibers, blocks, weights, reverse=False):
    """Canonical integer entries of mass times the operator, optionally transposed."""
    n = len(weights)
    keys = []
    vals = []
    w = np.array(weights, dtype=np.int32)
    for rows, dest, sign in entries(fibers, blocks):
        good = sign != 0
        a, b = (dest, rows) if reverse else (rows, dest)
        keys.append(a[good] * n + b[good])
        vals.append(sign[good] * w[rows[good]])
    key = np.concatenate(keys)
    val = np.concatenate(vals)
    order = key.argsort(kind="stable")
    key, val = key[order], val[order]
    starts = np.r_[0, np.flatnonzero(key[1:] != key[:-1]) + 1]
    key, val = key[starts], np.add.reduceat(val, starts)
    live = val != 0
    return key[live], val[live]


def verify_mass(fibers, blocks, weights):
    a, av = sparse_table(fibers, blocks[0], weights)
    b, bv = sparse_table(fibers, blocks[1], weights, reverse=True)
    assert np.array_equal(a, b) and np.array_equal(av, bv)
    return len(a)
