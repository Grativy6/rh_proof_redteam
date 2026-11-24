"""Weight-two signed Manin symbols in the primitive quadratic character of 7*2179."""

from collections import Counter
from functools import lru_cache
from math import gcd
import heapq
import numpy as np

LEVEL_PRIMES = (7, 2179)
S = (0, -1, 1, 0)
U = (0, -1, 1, -1)
U2 = (-1, 1, -1, 0)
C = (-1, 0, 0, 1)


def local_action(p, g):
    leg = [0] + [1 if pow(z, (p - 1) // 2, p) == 1 else -1 for z in range(1, p)]
    inv = [0] + [pow(z, -1, p) for z in range(1, p)]
    a, b, c, d = g
    idx = []
    sign = []
    for j in range(p + 1):
        x, y = (1, j) if j < p else (0, 1)
        u, v = (x * a + y * c) % p, (x * b + y * d) % p
        assert u or v
        idx.append(v * inv[u] % p if u else p)
        sign.append(leg[u if u else v])
    return np.asarray(idx, dtype=np.int32), np.asarray(sign, dtype=np.int8)


@lru_cache(maxsize=1024)
def action(g):
    (i, s), (j, t) = (local_action(p, g) for p in LEVEL_PRIMES)
    return (i[:, None] * (LEVEL_PRIMES[1] + 1) + j).ravel(), (s[:, None] * t).ravel()


def boundaries():
    """Signed endpoints at the four cusps of squarefree level."""
    tabs = []
    for p in LEVEL_PRIMES:

        def cusp(a, c):
            x = (c if c else a) % p
            return int(c == 0), 1 if pow(x, (p - 1) // 2, p) == 1 else -1

        tabs.append(
            [
                (cusp(0, 1), cusp(-1, j)) if j < p else (cusp(1, 0), cusp(0, 1))
                for j in range(p + 1)
            ]
        )
    out = []
    for first in tabs[0]:
        for second in tabs[1]:
            v = [0] * 4
            for e, (a, b) in zip((1, -1), zip(first, second)):
                v[2 * a[0] + b[0]] += e * a[1] * b[1]
            out.append(v)
    return np.asarray(out, dtype=np.int64)


def signed_edges(parity):
    """Impose the two-term Manin relation and the complex-conjugation sign."""
    actions = [(*action(S), -1), (*action(C), parity)]
    n = len(actions[0][0])
    seen = np.zeros(n, dtype=np.int8)
    edge = np.full(n, -1, dtype=np.int32)
    roots = []
    for i in range(n):
        if seen[i]:
            continue
        queue = [i]
        seen[i] = 1
        valid = True
        for j in queue:
            for dest, sgn, t in actions:
                k = dest[j]
                v = t * int(sgn[j]) * int(seen[j])
                if not seen[k]:
                    seen[k] = v
                    queue.append(k)
                elif seen[k] != v:
                    valid = False
        if valid:
            edge[queue] = len(roots)
            roots.append(i)
    return np.asarray(roots), edge, seen


def relation_rows(edges, signs):
    idx1, s1 = action(U)
    idx2, s2 = action(U2)
    rows = set()
    for i in range(len(edges)):
        t = Counter()
        for j, v in [(i, 1), (idx1[i], s1[i]), (idx2[i], s2[i])]:
            k = int(edges[j])
            if k >= 0:
                t[k] += int(v) * int(signs[j])
        raw = sorted((k, a) for k, a in t.items() if a)
        if raw:
            div = gcd(*(abs(a) for _, a in raw)) * (1 if raw[0][1] > 0 else -1)
            assert div % 5
            rows.add(tuple((k, a // div) for k, a in raw))
    return [dict(row) for row in sorted(rows)]


def eliminate(input_rows, n, mod):
    """Solve the three-term relations using only units, recording each pivot."""
    rows = [row.copy() for row in input_rows]
    inc = [set() for _ in range(n)]
    heap = []
    for i, row in enumerate(rows):
        heapq.heappush(heap, (len(row), i))
        for j in row:
            inc[j].add(i)
    steps = []
    while heap:
        count, i = heapq.heappop(heap)
        row = rows[i]
        if not row or count != len(row):
            continue
        unit = [h for h, a in row.items() if a % 5]
        assert unit, "nonunit relation"
        j = min(unit, key=lambda c: (len(inc[c]), c))
        mult = pow(int(row[j]), -1, mod)
        piv = {c: -a * mult % mod for c, a in row.items() if c != j}
        steps.append((j, piv))
        hits = inc[j].copy()
        for c in row:
            inc[c].remove(i)
        rows[i] = {}
        for h in hits - {i}:
            dst = rows[h]
            b = dst.pop(j)
            inc[j].remove(h)
            for c, val in piv.items():
                old = dst.get(c, 0)
                new = (old + b * val) % mod
                if new:
                    dst[c] = new
                    if not old:
                        inc[c].add(h)
                elif old:
                    del dst[c]
                    inc[c].remove(h)
            if dst:
                heapq.heappush(heap, (len(dst), h))
    used = {j for j, _ in steps}
    free = [j for j in range(n) if j not in used]
    return steps, np.array(free, dtype=np.int32)


def independent(a):
    work = a.copy() % 5
    piv = []
    indices = list(range(len(work)))
    for col in range(a.shape[1]):
        h = len(piv)
        ids = np.flatnonzero(work[h:, col])
        if len(ids):
            j = h + ids[0]
            work[[h, j]] = work[[j, h]]
            indices[h], indices[j] = indices[j], indices[h]
            v = work[h] * pow(int(work[h, col]), -1, 5) % 5
            work[h + 1 :] = (work[h + 1 :] - work[h + 1 :, col, None] * v) % 5
            piv.append(col)
    return np.array(indices[: len(piv)], dtype=np.int32), np.array(piv, dtype=np.int32)


def unit_inverse(a, m):
    n = len(a)
    b = np.column_stack((a, np.eye(n, dtype=np.int64))) % m
    for h in range(n):
        j = next(i for i in range(h, n) if b[i, h] % 5)
        b[[h, j]] = b[[j, h]]
        b[h] = b[h] * pow(int(b[h, h]), -1, m) % m
        c = b[:, h].copy()
        c[h] = 0
        b = (b - c[:, None] * b[h]) % m
    return b[:, n:]


class Cusp:
    def __init__(self, parity, mod):
        self.mod = mod
        roots, edges, sgn = signed_edges(parity)
        rel = relation_rows(edges, sgn)
        steps, free = eliminate(rel, len(roots), mod)
        self.reps = roots[free]
        self.parity = parity
        self.edges = edges
        self.signs = sgn
        self.free = free
        self.steps = steps
        self.edge_count = len(roots)
        b = boundaries()
        d, s = action(C)
        bd = (b + parity * s[:, None] * b[d]) % mod
        B = bd[self.reps]
        selected, cols = independent(B)
        self.bd = B[:, cols]
        self.brow = selected
        self.untwist = unit_inverse(self.bd[selected], mod)
        self.keep = np.array([i for i in range(len(free)) if i not in selected])
        self.n = len(self.keep)
        full = self.expand_relative(B)
        assert np.array_equal(full, bd)
        self.rel = rel

    def expand_relative(self, coords):
        m = self.mod
        flows = np.zeros((self.edge_count, coords.shape[1]), dtype=np.int64)
        flows[self.free] = coords
        for j, pivot in reversed(self.steps):
            for k, a in pivot.items():
                flows[j] += a * flows[k]
            flows[j] %= m
        vals = flows[np.maximum(self.edges, 0)] * self.signs[:, None]
        vals[self.edges < 0] = 0
        return vals % m

    def expand(self, coords):
        r = np.zeros((len(self.reps), coords.shape[1]), dtype=np.int64)
        r[self.keep] = coords
        return self.expand_relative(r)

    def quotient(self, vals):
        return (
            vals[self.keep]
            - self.bd[self.keep] @ (self.untwist @ vals[self.brow] % self.mod)
        ) % self.mod

    def apply(self, p, coords):
        """Apply the Heilbronn--Merel representatives on the cuspidal quotient."""
        v = self.expand(coords)
        r = np.zeros((len(self.reps), v.shape[1]), dtype=np.int64)
        for h in heilbronn(p):
            j, s = action(h)
            q = self.reps
            r += s[q, None] * v[j[q]]
        return self.quotient(r % self.mod)


def heilbronn(p):
    for a in range(1, p + 1):
        for d in range(1, p + 1):
            for b in range(a):
                if b == 0:
                    if a * d == p:
                        for c in range(d):
                            yield (a, 0, c, d)
                else:
                    c, rem = divmod(a * d - p, b)
                    if rem == 0 and 0 <= c < d:
                        yield (a, b, c, d)
