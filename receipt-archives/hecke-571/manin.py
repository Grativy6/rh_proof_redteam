"""Weight-two Manin-symbol test with the four cusp boundaries retained explicitly."""

from collections import Counter
from pathlib import Path
import argparse
import numpy as np

PRIMES = (7, 571)


def heilbronn(p):
    return [
        (a, b, c, d)
        for a in range(1, p + 1)
        for d in range(1, p + 1)
        for b in range(a)
        for c in range(d)
        if a * d - b * c == p
    ]


def local_table(prime, mats):
    leg = [0] + [1 if pow(a, (prime - 1) // 2, prime) == 1 else -1 for a in range(1, prime)]
    inv = [0] + [pow(a, -1, prime) for a in range(1, prime)]
    rows = []
    for a, b, c, d in mats:
        idx = []
        sgn = []
        for t in range(prime + 1):
            u, v = (1, t) if t < prime else (0, 1)
            x, y = (u * a + v * c) % prime, (u * b + v * d) % prime
            idx.append((y * inv[x]) % prime if x else prime)
            sgn.append(leg[x if x else y])
        rows.append((np.array(idx), np.array(sgn)))
    return rows


def transforms(mats):
    a, b = [local_table(p, mats) for p in PRIMES]
    for (i, s), (j, t) in zip(a, b):
        yield (i[:, None] * 572 + j).ravel(), (s[:, None] * t).ravel()


def operator(mats):
    n = 8 * 572
    out = [Counter() for _ in range(n)]
    for indices, signs in transforms(mats):
        for row, j, s in zip(out, indices.tolist(), signs.tolist()):
            row[j] += s
    return [{j: a for j, a in row.items() if a} for row in out]


def boundary():
    local = []
    for p in PRIMES:
        leg = lambda a: 1 if pow(a % p, (p - 1) // 2, p) == 1 else -1

        def cusp(a, c):
            return (int(c == 0), leg(a if c == 0 else c))

        endpoints = []
        for t in range(p + 1):
            a, b, c, d = (0, -1, 1, t) if t < p else (1, 0, 0, 1)
            endpoints.append((cusp(a, c), cusp(b, d)))
        local.append(endpoints)
    data = []
    for a in local[0]:
        for b in local[1]:
            v = [0] * 4
            for s, (left, right) in zip((1, -1), zip(a, b)):
                v[2 * left[0] + right[0]] += s * left[1] * right[1]
            data.append(v)
    return np.array(data, dtype=np.int64)


def image(rows, b):
    return np.stack(
        [sum((a * b[j] for j, a in row.items()), start=np.zeros(b.shape[1], int)) for row in rows]
    )


def independent_rows(a):
    piv = []
    selected = []
    for i, row in enumerate(a):
        v = row.copy() % 5
        for col, b in piv:
            v = (v - v[col] * b) % 5
        if np.any(v):
            col = np.flatnonzero(v)[0]
            v = v * pow(int(v[col]), -1, 5) % 5
            piv.append((col, v))
            selected.append(i)
            if len(selected) == a.shape[1]:
                return selected
    raise ValueError("not full column rank")


def write(path, rows, width):
    count = sum(sum(int(a) != 0 for a in row.values()) for row in rows)
    with path.open("w", encoding="ascii", newline="\n") as f:
        f.write(f"%%MatrixMarket matrix coordinate integer general\n{len(rows)} {width} {count}\n")
        for i, row in enumerate(rows, 1):
            for j, a in sorted(row.items()):
                if a:
                    f.write(f"{i} {j + 1} {a}\n")


def main(out):
    n = 8 * 572
    b = boundary()
    piv = independent_rows(b)
    S = (0, -1, 1, 0)
    U = (0, -1, 1, -1)
    U2 = (-1, 1, -1, 0)
    empty = (1, 0, 0, 1)
    rel = operator([empty, S]) + operator([empty, U, U2])
    assert not np.any(image(rel, b))
    t2 = operator(heilbronn(2))
    t29 = operator(heilbronn(29))
    t2sq = []
    for h, row in enumerate(t2):
        x = Counter({h: -1})
        for i, a in row.items():
            x.update({j: a * c for j, c in t2[i].items()})
        t2sq.append(x)
    from packet import inverse_unit

    for rows in (t2sq, t29):
        im = image(rows, b) % 5
        T = inverse_unit(b[piv], 5) @ im[piv] % 5
        assert np.array_equal(b @ T % 5, im)
    extra = []
    for h, rows in enumerate((t2sq, t29)):
        for i, row in enumerate(rows):
            rr = dict(row)
            rr.update({n + 4 * h + j: -int(x) for j, x in enumerate(b[i]) if x})
            extra.append(rr)
    out.mkdir(parents=True, exist_ok=True)
    write(out / "manin-rel.mtx", rel, n)
    write(out / "manin-two-tests.mtx", rel + extra, n + 8)
    print(
        "Wrote the relative-symbol relations and the two Hecke conditions modulo the four cusp boundaries."
    )


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("output", type=Path)
    main(p.parse_args().output)
