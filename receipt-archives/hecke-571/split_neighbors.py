"""Certify split-prime neighbours of both maximal lattice classes over Q(sqrt(-7))."""

from functools import lru_cache
from itertools import product
from math import isqrt
import numpy as np

from operators import IDENTITY, P, SIGNED, times

ONE = (1, 0)
ZERO = (0, 0)
OMEGA = (0, 1)


def cmul(x, y):
    a, b = x
    c, d = y
    return a * c - 2 * b * d, a * d + b * c + b * d


def conj(x):
    a, b = x
    return a + b, -b


def cadd(x, y):
    return x[0] + y[0], x[1] + y[1]


def csub(x, y):
    return x[0] - y[0], x[1] - y[1]


def cpow(x, n):
    out = ONE
    for _ in range(n):
        out = cmul(out, x)
    return out


def norm(x):
    a, b = x
    return a * a + a * b + 2 * b * b


def dot(x, y):
    out = ZERO
    for a, b in zip(x, y):
        out = cadd(out, cmul(conj(a), b))
    return out


def determinant_ring(cols):
    u, v, w = cols
    out = ZERO
    for i in range(3):
        a, b = (i + 1) % 3, (i + 2) % 3
        out = cadd(out, cmul(w[i], csub(cmul(u[a], v[b]), cmul(u[b], v[a]))))
    return out


def split_generator(p):
    for b in range(1, isqrt(4 * p // 7) + 1):
        s = 4 * p - 7 * b * b
        t = isqrt(s)
        if t * t == s and (t - b) % 2 == 0:
            return (t - b) // 2, b
    raise ValueError(f"{p} has no selected split generator")


def modular_matrix(cols, lam, w, p):
    t = pow((lam[0] + lam[1] * w) % p, -1, p)
    return tuple((cols[j][i][0] + w * cols[j][i][1]) * t % p for i in range(3) for j in range(3))


def tau(w, p):
    return tuple(a * pow(2, -1, p) % p for a in (-1, 1 - w, 1, -1, w - 1, 1, w, 0, w))


def transpose(g):
    return tuple(g[3 * j + i] for i in range(3) for j in range(3))


def plane_action(g, h, p):
    v = [sum(g[3 * i + j] * h[j] for j in range(3)) % p for i in range(3)]
    scale = pow(next(z for z in v if z), -1, p)
    return tuple(z * scale % p for z in v)


def plane_orbits(i, p, root):
    # If gamma acts on columns, its inverse transpose acts on the plane normal.
    dual = [tuple(a % p for a in g) for g in SIGNED]
    inv = [tuple(a % P for a in transpose(g)) for g in SIGNED]
    if i:
        dual.append(tau((1 - root) % p, p))
        inv.append(transpose(tau(1 - 159, P)))
    planes = (
        [(1, a, b) for a in range(p) for b in range(p)]
        + [(0, 1, b) for b in range(p)]
        + [(0, 0, 1)]
    )
    seen = set()
    for h in planes:
        if h in seen:
            continue
        orbit = {h: IDENTITY}
        todo = [h]
        for z in todo:
            for a, b in zip(dual, inv):
                new = plane_action(a, z, p)
                if new not in orbit:
                    orbit[new] = times(orbit[z], b)
                    todo.append(new)
        assert not seen.intersection(orbit)
        seen.update(orbit)
        yield h, orbit
    assert len(seen) == p * p + p + 1


@lru_cache(maxsize=12)
def vectors_of_norm(r):
    buckets = [[] for _ in range(r + 1)]
    for b in range(-isqrt(4 * r // 7), isqrt(4 * r // 7) + 1):
        for a in range(-2 * isqrt(r) - 2, 2 * isqrt(r) + 3):
            d = norm((a, b))
            if d <= r:
                buckets[d].append((a, b))
    vals = []
    for d, b1 in enumerate(buckets):
        for v in range(r - d + 1):
            vals.extend(product(b1, buckets[v], buckets[r - d - v]))
    return np.array(vals, dtype=np.int64)


def denominators(pi, i, j):
    lam = cmul(conj(pi), cmul(cpow(OMEGA, j), cpow(conj(OMEGA), i)))
    det = cmul(
        cmul(pi, cpow(conj(pi), 2)), cmul(cpow(OMEGA, i + 2 * j), cpow(conj(OMEGA), 2 * i + j))
    )
    return lam, det


def dyadic_codes(cols, i, j):
    # alpha = [1,0,0;0,1,0;-1,-1,2] on the branch omega = 2 mod 4.
    small = 2 ** (i + j)
    z = (cols[:, :, 0] + 2 * cols[:, :, 1]) % small
    if i:
        z = np.column_stack((2 * z[:, 0], 2 * z[:, 1], z.sum(axis=1))) % small
    return z


def check_seed(cols, pi, i, j, h):
    p = norm(pi)
    w = -pi[0] * pow(pi[1], -1, p) % p
    lam, det = denominators(pi, i, j)
    r = norm(lam)
    check_integral_frame(cols, r, det, i, j)
    assert all(sum(h[k] * (a + w * b) for k, (a, b) in enumerate(col)) % p == 0 for col in cols)


def check_integral_frame(cols, r, det, i, j):
    assert all(
        dot(u, v) == ((r, 0) if k == l else ZERO)
        for k, u in enumerate(cols)
        for l, v in enumerate(cols)
    )
    assert determinant_ring(cols) == det
    z = dyadic_codes(np.asarray(cols), i, j)
    if j:
        assert (
            np.all(z[0] == z[1]) and np.all(z[1] == z[2]) and not np.any((2 * z[2]) % 2 ** (i + j))
        )
    else:
        assert not np.any(z)


def find_seed(pi, i, j, h):
    p = norm(pi)
    w = -pi[0] * pow(pi[1], -1, p) % p
    lam, det = denominators(pi, i, j)
    r = norm(lam)
    allv = vectors_of_norm(r)
    vals = allv[(((allv[:, :, 0] + w * allv[:, :, 1]) @ h) % p) == 0]

    def accept(third):
        return sum(h[k] * (a + w * b) for k, (a, b) in enumerate(third)) % p == 0

    cols = find_frame(vals, r, det, i, j, accept)
    if cols is not None:
        check_seed(cols, pi, i, j, h)
    return cols


def find_frame(vals, r, det, i, j, accept):
    codes = dyadic_codes(vals, i, j)
    if j:
        ok = np.all((2 * codes) % 2 ** (i + j) == 0, axis=1)
    else:
        ok = np.all(codes == 0, axis=1)
    vals, codes = vals[ok], codes[ok]
    re, im = vals[:, :, 0], vals[:, :, 1]
    for k in range(len(vals)):
        x, y = re[k], im[k]
        orth = (re @ (x + y) + 2 * (im @ y) == 0) & (im @ x - re @ y == 0)
        if j:
            orth &= np.all(codes == codes[k], axis=1)
        for l in np.flatnonzero(orth):
            u, v = (tuple((int(a), int(b)) for a, b in vals[index]) for index in (k, l))
            third = []
            for s in range(3):
                a, b = (s + 1) % 3, (s + 2) % 3
                m, n = cmul(det, conj(csub(cmul(u[a], v[b]), cmul(u[b], v[a]))))
                if m % (r * r) or n % (r * r):
                    break
                third.append((m // (r * r), n // (r * r)))
            if len(third) != 3 or not accept(third):
                continue
            dz = dyadic_codes(np.asarray([third]), i, j)[0]
            if not np.all(dz == codes[k]):
                continue
            return (u, v, tuple(third))
    return None


def split_blocks(pi, seeds=None):
    p = norm(pi)
    w = -pi[0] * pow(pi[1], -1, p) % p
    blocks = [[[], []], [[], []]]
    certificates = []
    for i in range(2):
        for h, orbit in plane_orbits(i, p, w):
            if seeds is None:
                for j in (0, 1):
                    cols = find_seed(pi, i, j, h)
                    if cols is not None:
                        break
                else:
                    raise ValueError(f"no certified isometry for {(pi, i, h)}")
            else:
                j, cols = seeds[(i, h)]
            check_seed(cols, pi, i, j, h)
            certificates.append([i, h, j, cols])
            lam, _ = denominators(pi, i, j)
            inv = transpose(modular_matrix(cols, lam, 1 - 159, P))
            for action in orbit.values():
                blocks[i][j].append(times(inv, action))
        assert sum(map(len, blocks[i])) == p * p + p + 1
    return blocks, certificates
