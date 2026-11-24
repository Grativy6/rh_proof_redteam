"""The two-step operator on the self-dual lattice at ramified 7."""

from itertools import product
import numpy as np
from operators import P, SIGNED, IDENTITY, times
from split_neighbors import (
    OMEGA,
    cmul,
    conj,
    cpow,
    norm,
    check_integral_frame,
    vectors_of_norm,
    find_frame,
    transpose,
    tau,
    modular_matrix,
)


def local(a):
    """a_0+a_1*omega = x + y*sqrt(-7) modulo 7."""
    return (a[0] + 4 * a[1]) % 7, (4 * a[1]) % 7


def targets_7():
    for i in range(3):
        for rest in product(range(7), repeat=2 - i):
            v = (0,) * i + (1,) + rest
            if sum(a * a for a in v) % 7 == 0:
                for t in range(7):
                    yield v, t


def code7(x, y):
    i = next(k for k in range(3) if x[k] % 7)
    c = pow(x[i] % 7, -1, 7)
    v = tuple(h * c % 7 for h in x)
    return v, sum(a * b for a, b in zip(v, y)) * c % 7


def orbit7(i):
    actions = [[(a % 7, 0) for a in g] for g in SIGNED]
    inverses = [tuple(a % P for a in transpose(g)) for g in SIGNED]
    if i:
        nums = ((-1, 0), (1, -1), (1, 0), (-1, 0), (-1, 1), (1, 0), (0, 1), (0, 0), (0, 1))
        actions.append([tuple(t * 4 % 7 for t in local(a)) for a in nums])
        inverses.append(transpose(tau(1 - 159, P)))
    all_codes = set(targets_7())
    assert len(all_codes) == 56
    seen = set()
    for t in sorted(all_codes):
        if t in seen:
            continue
        orbit = {t: IDENTITY}
        queue = [t]
        for item in queue:
            v, s = item
            j = next(k for k in range(3) if v[k])
            y = [s if h == j else 0 for h in range(3)]
            for g, inv in zip(actions, inverses):
                x1 = [sum(g[3 * a + b][0] * v[b] for b in range(3)) % 7 for a in range(3)]
                y1 = [
                    sum(g[3 * a + b][1] * v[b] + g[3 * a + b][0] * y[b] for b in range(3)) % 7
                    for a in range(3)
                ]
                new = code7(x1, y1)
                if new not in orbit:
                    orbit[new] = times(orbit[item], inv)
                    queue.append(new)
        assert not seen.intersection(orbit)
        seen.update(orbit)
        yield t, orbit
    assert seen == all_codes


def match7(values, target):
    v, t = target
    pivot = next(i for i, a in enumerate(v) if a)
    x = (values[:, :, 0] + 4 * values[:, :, 1]) % 7
    y = (4 * values[:, :, 1]) % 7
    c = x[:, pivot]
    vv = np.array(v)
    return np.flatnonzero(
        np.all((x - c[:, None] * vv) % 7 == 0, axis=1) & ((y @ vv - c * t) % 7 == 0)
    )


def blocks7():
    blocks = [[[], []], [[], []]]
    uniformizer = (-1, 2)
    certs = []
    for i in range(2):
        for target, orbit in orbit7(i):
            for j in (0, 1):
                lam = cmul(uniformizer, cmul(cpow(OMEGA, j), cpow(conj(OMEGA), i)))
                det = cmul(
                    cpow(uniformizer, 3), cmul(cpow(OMEGA, i + 2 * j), cpow(conj(OMEGA), 2 * i + j))
                )
                r = norm(lam)
                allv = vectors_of_norm(r)
                vals = allv[match7(allv, target)]
                cols = find_frame(
                    vals, r, det, i, j, lambda v: len(match7(np.asarray([v]), target)) > 0
                )
                if cols is not None:
                    break
            else:
                raise RuntimeError(f"missing ramified isometry for {(i, target)}")
            check_integral_frame(cols, r, det, i, j)
            assert len(match7(np.array(cols), target)) == 3
            certs.append((i, j, len(orbit)))
            inv = transpose(modular_matrix(cols, lam, 1 - 159, P))
            blocks[i][j].extend(times(inv, action) for action in orbit.values())
        assert sum(map(len, blocks[i])) == 56
    return blocks, certs
