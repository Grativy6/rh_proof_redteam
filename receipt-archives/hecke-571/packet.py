"""Replay the four-dimensional Hecke calculation and write an independent rank test."""

import argparse
import base64
from hashlib import sha256
from itertools import combinations, permutations
import json
from math import prod
from pathlib import Path
import zlib

import numpy as np

from operators import P, LEGENDRE, build, apply_batch, verify_mass, matrix_market
from split_neighbors import split_blocks, split_generator, conj
from inert_neighbors import inert_blocks
from ramified_neighbors import blocks7


def read_witness():
    path = Path(__file__).with_name("primary_vectors.json")
    record = json.loads(path.read_text("ascii"))
    n, k = record["dimension"], record["number_of_vectors"]
    raw = zlib.decompress(base64.b64decode(record["compressed"], validate=True))
    assert (n, k) == (15270, 13) and len(raw) == n * k
    assert sha256(raw).hexdigest() == record["sha256"] and max(raw) < 5
    return np.frombuffer(raw, dtype=np.uint8).reshape(k, n).T.astype(np.int64), record


def rref(matrix):
    a = np.array(matrix, dtype=np.int64) % 5
    m, n = a.shape
    pivots = []
    for j in range(n):
        h = len(pivots)
        if h == m:
            break
        choices = np.flatnonzero(a[h:, j])
        if not len(choices):
            continue
        i = h + choices[0]
        a[[h, i]] = a[[i, h]]
        a[h] = (a[h] * pow(int(a[h, j]), -1, 5)) % 5
        factors = a[:, j].copy()
        factors[h] = 0
        a = (a - factors[:, None] * a[h]) % 5
        pivots.append(j)
    return a, pivots


def kernel(matrix):
    a, pivots = rref(matrix)
    free = [j for j in range(a.shape[1]) if j not in pivots]
    v = np.zeros((a.shape[1], len(free)), dtype=np.int64)
    for i, j in enumerate(free):
        v[j, i] = 1
        for h, p in enumerate(pivots):
            v[p, i] = -a[h, j] % 5
    assert not np.any(matrix @ v % 5)
    return v


def inverse_unit(matrix, modulus):
    n = len(matrix)
    a = np.column_stack((matrix, np.eye(n, dtype=np.int64))) % modulus
    for h in range(n):
        j = next(i for i in range(h, n) if a[i, h] % 5)
        a[[h, j]] = a[[j, h]]
        a[h] = a[h] * pow(int(a[h, h]), -1, modulus) % modulus
        factors = a[:, h].copy()
        factors[h] = 0
        a = (a - factors[:, None] * a[h]) % modulus
    return a[:, n:]


def coordinates(basis, image):
    _, pivots = rref(basis.T)
    assert len(pivots) == basis.shape[1]
    a = inverse_unit(basis[pivots], 5) @ image[pivots] % 5
    assert np.array_equal(basis @ a % 5, image % 5)
    return a


def primary(m, eigenvalue):
    a = (m - eigenvalue * np.eye(len(m), dtype=np.int64)) % 5
    power = np.eye(len(m), dtype=np.int64)
    dims = [0]
    while True:
        power = power @ a % 5
        v = kernel(power)
        dims.append(v.shape[1])
        if dims[-1] == dims[-2]:
            return v, dims[1:]


def determinant_small(a):
    total = 0
    for perm in permutations(range(len(a))):
        inversions = sum(perm[i] > perm[j] for i in range(len(a)) for j in range(i + 1, len(a)))
        total += (-1) ** inversions * prod(int(a[i, j]) for i, j in enumerate(perm))
    return total


def second_coefficient(a):
    return sum(determinant_small(a[np.ix_(h, h)]) for h in combinations(range(len(a)), 2))


def sparse_image(rows, vectors):
    out = np.zeros(vectors.shape, dtype=np.int64)
    for i, row in enumerate(rows):
        if row:
            indices = list(row)
            out[i] = np.array([row[j] for j in indices]) @ vectors[indices]
    return out


def export_minor(path, rows, u, omitted):
    n, k = u.shape
    assert len(set(omitted)) == k
    retained = [j for j in range(n + k) if j not in omitted]
    assert len(retained) == n
    cols = {j: i + 1 for i, j in enumerate(retained)}
    count = sum(j in cols for row in rows for j in row) + sum(j in cols for j in range(n))
    count += sum(np.count_nonzero(u[:, j]) for j in range(k) if n + j in cols)
    with path.open("w", encoding="ascii", newline="\n") as f:
        f.write(f"%%MatrixMarket matrix coordinate integer general\n{n} {n} {count}\n")
        for i, row in enumerate(rows):
            for j, v in sorted(row.items()):
                if j in cols:
                    f.write(f"{i + 1} {cols[j]} {v}\n")
        for j in range(n):
            if j in cols:
                f.write(f"{j + 1} {cols[j]} -2\n")
        for j in range(k):
            if n + j in cols:
                for i in np.flatnonzero(u[:, j]):
                    f.write(f"{i + 1} {cols[n + j]} {-u[i, j]}\n")
    assert (
        sha256(path.read_bytes()).hexdigest()
        == "6fb63964ca2b784195d7820d0ede52471bc5dc9f88020c129791865d17ac913a"
    )


def cut(v, eigenvectors, image, eigenvalue):
    m = coordinates(v, image)
    e = coordinates(v, eigenvectors)
    a = m - eigenvalue * np.eye(len(m), dtype=np.int64)
    e = eigenvectors @ kernel(a @ e % 5) % 5
    sub, dims = primary(m, eigenvalue)
    return v @ sub % 5, e, dims


def validate_local_algebra(mod_five, lifts):
    eye = np.eye(4, dtype=np.int64)
    x = (mod_five[2][0] - 2 * eye) % 5
    y = (mod_five[23][0] - 3 * eye) % 5
    z = x @ x % 5
    assert np.any(z) and not np.any(x @ z % 5) and not np.any(y @ z % 5)
    assert np.array_equal(x @ y % 5, z) and np.array_equal(y @ x % 5, z)
    assert np.array_equal(y @ y % 5, 4 * z % 5)
    cyclic = np.column_stack([a[:, -1] for a in (eye, x, y, z)])
    assert determinant_small(cyclic) % 5
    assert not np.any((mod_five[2][1] - 2 * eye + x - 3 * z) % 5)
    assert not np.any((mod_five[23][1] - 3 * eye + y - 4 * z) % 5)
    d = (lifts[2][0] - lifts[2][1]) % 25
    assert len(rref(d % 5)[1]) == 2
    assert second_coefficient(d) % 25 == 20
    assert determinant_small(d) % 125 == 75
    return d @ d % 25


def leading_branches(p, matrices, square):
    eye = np.eye(4, dtype=np.int64)
    target = p + LEGENDRE[p % P] * (p * p + 1)
    real = ((matrices[0] + matrices[1]) * 13 - target * eye) % 25
    anti = (matrices[0] - matrices[1]) % 25
    out = []
    for a in (real, anti @ anti % 25):
        c = next(i for i in range(5) if not np.any((a - i * square) % 5))
        rest = ((a - c * square) % 25) // 5
        b = int(np.trace(rest)) * 4 % 5
        out.append([(b + c * u) % 5 for u in (4, 2)])
    return out


def check_level_prime(fiber, eigenline):
    # The first principal line orbit with this simple global transporter and nonzero value.
    points = np.array(
        [(1, b, c) for b in range(P) for c in range(P)]
        + [(0, 1, c) for c in range(P)]
        + [(0, 0, 1)],
        dtype=np.int64,
    )
    coord = np.asarray(fiber.coordinates)
    values = eigenline[np.maximum(abs(coord) - 1, 0), 0] * np.sign(coord)
    signs = np.asarray(LEGENDRE)
    # v=(1,1+omega,2), h(v,v)=9; its conjugate coordinate uses omega=1-159.
    covector = np.array([1, 2 - 159, 2])
    s = signs[9] * signs[(points @ covector) % P] @ values
    val = values[160 * P + 2] % 5
    assert val and s % 5 == val
    print(
        f"At 571 the parahoric operator reads {int(s) * pow(int(val), -1, 5) % 5} on the residual line."
    )


def run(minor=None, two_directory=None):
    fibers, a, b, masses = build()
    u, record = read_witness()
    if minor is not None:
        export_minor(minor, a, u, record["omit_zero_based_columns"])
    if two_directory is not None:
        two_directory.mkdir(parents=True, exist_ok=True)
        for name, rows in (("two", a), ("two_bar", b)):
            matrix_market(two_directory / (name + ".mtx"), rows)
    assert len(rref(u.T)[1]) == 13
    v = u
    eigenline = u
    needed = {2: 2, 11: 3, 23: 3, 29: 1, 37: 2, 43: 3, 53: 3, 67: 2, 71: 4, 79: 2}
    dims = {2: (5, 12), 11: (4, 9), 23: (2, 8), 29: (1, 4)}
    small_blocks = {}
    for p in (2, 11, 23, 29):
        lam = needed[p]
        if p == 2:
            for i, rows in enumerate((a, b)):
                v, eigenline, growth = cut(v, eigenline, sparse_image(rows, v), lam)
                if i == 0:
                    assert growth == [7, 10, 13, 13]
        else:
            pi = split_generator(p)
            blocks = [split_blocks(h)[0] for h in (pi, conj(pi))]
            small_blocks[p] = blocks
            if p == 11:
                assert verify_mass(fibers, blocks, masses) == 1984669
            for op in blocks:
                v, eigenline, _ = cut(v, eigenline, apply_batch(fibers, op, v), lam)
        assert (eigenline.shape[1], v.shape[1]) == dims[p]
        print(
            f"Through split {p}: common eigenspace {eigenline.shape[1]}, primary space {v.shape[1]}."
        )
    eigenline = eigenline * pow(int(eigenline[np.flatnonzero(eigenline)[0], 0]), -1, 5) % 5
    assert np.count_nonzero(eigenline) == 12121
    check_level_prime(fibers[0], eigenline)
    dual = v.T * np.array(masses)
    gram = dual @ v
    assert determinant_small(gram) % 5 == 2
    project = inverse_unit(gram, 25) @ dual % 25
    e = coordinates(v, eigenline)
    mod5, lifts = {}, {}
    for p in (2, 3, 5, 7, 11, 23, 29, 37, 43, 53, 67, 71, 79):
        if p == 2:
            images = [sparse_image(rows, v) for rows in (a, b)]
        elif p in (3, 5, 7):
            op, certs = blocks7() if p == 7 else inert_blocks(p)
            if p in (5, 7):
                assert verify_mass(fibers, [op, op], masses) == {5: 9143223, 7: 836823}[p]
            images = [apply_batch(fibers, op, v)]
        elif p in small_blocks:
            images = [apply_batch(fibers, op, v) for op in small_blocks[p]]
        else:
            pi = split_generator(p)
            images = [apply_batch(fibers, split_blocks(h)[0], v) for h in (pi, conj(pi))]
        mod5[p] = [coordinates(v, image) for image in images]
        lifts[p] = [project @ image % 25 for image in images]
        lam = needed[p] if p in needed else {3: 4, 5: 0, 7: 1}[p]
        assert all(not np.any((m @ e - lam * e) % 5) for m in mod5[p])
        assert all(np.array_equal(a % 5, b) for a, b in zip(lifts[p], mod5[p]))
        print(f"At {p}: eigenvalue {lam} modulo 5 on the same line ({len(images)} direction(s)).")
    square = validate_local_algebra(mod5, lifts)
    leading = {p: leading_branches(p, lifts[p], square) for p in needed}
    assert leading[2] == [[3, 1], [4, 2]] and leading[11] == [[1, 2], [0, 0]]
    assert leading[29] == [[1, 3], [1, 3]]
    print("At 2 the skew characteristic coefficient is 20 mod 25, its determinant is 75 mod 125.")
    for p in (2, 11, 23, 29, 37, 71, 79):
        print(f"{p}: real difference / 5 and squared skew difference / 5, modulo 5: {leading[p]}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--minor", type=Path, help="write the sparse square minor for certify_minor.cpp"
    )
    parser.add_argument(
        "--export-two", type=Path, help="write both integer split-prime matrices at 2"
    )
    args = parser.parse_args()
    run(args.minor, args.export_two)
