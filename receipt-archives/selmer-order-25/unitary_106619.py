"""Count the signed rank-three space and test two split-prime operators at 106619.

The heavy projective-line space is never enumerated. The row calculation uses
the rational neighbour construction on both global lattice classes.
"""

from collections import deque
from itertools import combinations
from pathlib import Path
import sys

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "hecke-571"))
from split_neighbors import (
    IDENTITY,
    SIGNED,
    check_seed,
    conj,
    denominators,
    find_seed,
    modular_matrix,
    norm,
    plane_orbits,
    split_generator,
    tau,
    transpose,
)


def multiply(a, b, q):
    return tuple(
        sum(a[3 * i + k] * b[3 * k + j] for k in range(3)) % q
        for i in range(3)
        for j in range(3)
    )


def determinant(m, q):
    a, b, c, d, e, f, g, h, i = m
    return (a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)) % q


def group(gens, q, size):
    seen = {IDENTITY}
    queue = deque([IDENTITY])
    while queue:
        a = queue.popleft()
        for g in gens:
            v = multiply(a, g, q)
            if v not in seen:
                seen.add(v)
                queue.append(v)
                assert len(seen) <= size
    assert len(seen) == size
    return sorted(seen)


def char(a, q):
    return {1: 1, q - 1: -1}[pow(a % q, (q - 1) // 2, q)]


def nullity(m, q):
    if determinant(m, q):
        return 0
    pairs = list(combinations(range(3), 2))
    if any(
        (m[3 * i + j] * m[3 * k + h] - m[3 * i + h] * m[3 * k + j]) % q
        for i, k in pairs
        for j, h in pairs
    ):
        return 1
    return 2 if any(m) else 3


def dimension(G, q):
    roots = [a for a in range(1, q) if pow(a, len(G), q) == 1]
    count = 0
    for g in G:
        det = determinant(g, q)
        for u in roots:
            n = nullity(tuple((x - u * y) % q for x, y in zip(g, IDENTITY)), q)
            count += (q**n - 1) // (q - 1) * char(det * u, q)
    assert count % len(G) == 0
    return count // len(G)


def transport_actions(lattice, q, w):
    """Lift the old orbit words through the same 48 or 336 exact stabilizers."""

    def generators(p, root):
        g = [transpose(a) for a in SIGNED]
        if lattice:
            g.append(transpose(tau(1 - root, p)))
        return g

    pair = list(zip(generators(571, 159), generators(q, w)))
    entries = {IDENTITY: IDENTITY}
    queue = deque([IDENTITY])
    while queue:
        x = queue.popleft()
        for a, b in pair:
            old = multiply(x, a, 571)
            new = multiply(entries[x], b, q)
            if old in entries:
                assert entries[old] == new
            else:
                queue.append(old)
                entries[old] = new
    assert len(set(entries.values())) == len(entries) == (336 if lattice else 48)
    return entries


def neighbor_blocks(pi, q, w):
    p = norm(pi)
    root = -pi[0] * pow(pi[1], -1, p) % p
    blocks = [[[], []], [[], []]]
    for i in range(2):
        target = transport_actions(i, q, w)
        for h, orbit in plane_orbits(i, p, root):
            for j in range(2):
                cols = find_seed(pi, i, j, h)
                if cols is not None:
                    break
            else:
                raise ValueError("Missing a neighbour isometry")
            check_seed(cols, pi, i, j, h)
            lam, _ = denominators(pi, i, j)
            base = transpose(modular_matrix(cols, lam, 1 - w, q))
            blocks[i][j].extend(
                multiply(base, target[old], q) for old in orbit.values()
            )
        assert sum(map(len, blocks[i])) == p * p + p + 1
    return blocks


def move(g, v, q):
    x = tuple(sum(g[3 * i + j] * v[j] for j in range(3)) % q for i in range(3))
    t = next(i for i in x if i)
    return tuple(a * pow(t, -1, q) % q for a in x), char(determinant(g, q) * t, q)


def orbit_values(y, G, q):
    values = {}
    for g in G:
        h, s = move(g, y, q)
        if h in values and values[h] != s:
            return {}
        values[h] = s
    return values


def row(probe, blocks, G, q):
    assert orbit_values(probe, G, q)
    images = [[move(g, probe, q) for g in ops] for ops in blocks]
    for y, _ in images[0]:
        v = orbit_values(y, G, q)
        readings = [sum(s * v.get(k, 0) for k, s in im) for im in images]
        if (readings[0] - readings[1]) % 5:
            return y, readings
    raise ValueError("no signed witness on this row")


def normalized_codes(mats, points, q, inverses):
    """All projective images, encoded as three injective base-q digits."""
    raw = np.einsum("aij,bj->abi", mats, points) % q
    scale = np.where(
        raw[:, :, 0] != 0,
        raw[:, :, 0],
        np.where(raw[:, :, 1] != 0, raw[:, :, 1], raw[:, :, 2]),
    )
    coords = raw * inverses[scale][:, :, None] % q
    return (coords[:, :, 0] * q + coords[:, :, 1]) * q + coords[:, :, 2], scale


def joint_entry(first, second, probe, q, characters, inverses, labels, signs):
    """Read one signed orbit after both operators, through both lattice classes."""
    total = 0
    for i in range(2):
        moved = [move(g, probe, q) for g in first[0][i]]
        if not moved or not second[i][0]:
            continue
        points = np.asarray([v for v, _ in moved], dtype=np.int64)
        first_sign = np.asarray([s for _, s in moved], dtype=np.int8)
        group = second[i][0]
        mats = np.asarray(group, dtype=np.int64).reshape(-1, 3, 3)
        second_sign = np.asarray(
            [characters[determinant(g, q)] for g in group], dtype=np.int8
        )
        codes, scale = normalized_codes(mats, points, q, inverses)
        indices = np.searchsorted(labels, codes)
        orbit = (codes == labels[indices]) * signs[indices]
        total += int(
            np.sum(
                orbit * first_sign[None, :] * second_sign[:, None] * characters[scale]
            )
        )
    return total


def joint_check(ops, probe, G, q):
    chars = np.array([0] + [char(a, q) for a in range(1, q)], dtype=np.int8)
    inv = np.array([0] + [pow(a, -1, q) for a in range(1, q)], dtype=np.int64)
    y = (1, 2736, 98987)
    roots = orbit_values(y, G, q)
    assert roots.get(y) == 1
    table = sorted(((x[0] * q + x[1]) * q + x[2], s) for x, s in roots.items())
    # A sentinel keeps searchsorted defined for every projective code.
    table.append((q**3, 0))
    labels = np.array([k for k, _ in table], dtype=np.int64)
    signs = np.array([v for _, v in table], dtype=np.int8)

    def products(p, r):
        return [
            joint_entry(a, b, probe, q, chars, inv, labels, signs)
            for a in ops[p]
            for b in ops[r]
        ]

    forward = products(11, 29)
    reverse = products(29, 11)
    assert forward == [1, 0, 0, 0] and forward == [
        reverse[0],
        reverse[2],
        reverse[1],
        reverse[3],
    ]
    print(
        "Both prime orders on test orbit",
        y,
        "four products",
        forward,
        "mixed difference",
        forward[0] - forward[1] - forward[2] + forward[3],
        flush=True,
    )


def main():
    q = 106619
    roots = [u for u in range(q) if (u * u - u + 2) % q == 0]
    assert len(roots) == 2
    signed = group(SIGNED, q, 48)
    dims = [
        (dimension(signed, q), dimension(group(list(SIGNED) + [tau(w, q)], q, 336), q))
        for w in roots
    ]
    assert roots == [38102, 68518] and dims[0] == dims[1] == (473614926, 67651660)
    print(
        "roots", roots, "signed dimensions", dims[0], "total", sum(dims[0]), flush=True
    )
    ops = {}
    probe = (1, 2, 3)
    for p in [11, 29]:
        pi = split_generator(p)
        ops[p] = [neighbor_blocks(a, q, roots[0]) for a in [pi, conj(pi)]]
        blocks = [x[0][0] for x in ops[p]]
        y, readings = row(probe, blocks, signed, q)
        expected = {
            11: (117, (1, 71080, 57700), [1, 0]),
            29: (759, (1, 71080, 25563), [-1, 0]),
        }[p]
        assert (
            len(blocks[0]) == len(blocks[1]) == expected[0]
            and (y, readings) == expected[1:]
        )
        print(
            "p",
            p,
            "standard neighbours",
            list(map(len, blocks)),
            "input",
            probe,
            "test orbit",
            y,
            "readings",
            readings,
            flush=True,
        )

    joint_check(ops, probe, signed, q)


if __name__ == "__main__":
    main()
