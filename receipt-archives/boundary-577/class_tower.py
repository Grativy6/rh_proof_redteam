"""Character-by-character Bernoulli checks in the real affine field and its CM partner."""

from collections import defaultdict
from math import gcd, lcm
import numpy as np

P = 577
ORD = P - 1


def abelian_moments(mirror):
    # mirror=True: B_1 for (omega*z^(-a))^(-1).
    # mirror=False: B_1 for (eta*z^a)^(-1).
    q = P**3
    root = pow(5, P**2, q)
    log = np.zeros(P, dtype=np.int64)
    for j in range(ORD):
        log[pow(5, j, P)] = j
    groups = defaultdict(list)
    for a in range(ORD):
        order = 64 // gcd(64, a)
        conductor = 4 * order if order > 1 else 1
        groups[conductor, mirror or (296 * a) % ORD != 0].append(a)
    results = {}
    for (conductor, at_p), labels in groups.items():
        f = conductor * (1 if mirror else 7) * (P if at_p else 1)
        x = np.arange(1, f + 1, dtype=np.int64)
        if conductor > 1:
            x = x[x % 2 != 0]
        if not mirror:
            x = x[x % 7 != 0]
        if at_p:
            x = x[x % P != 0]
        phi = np.zeros(conductor, dtype=np.int64)
        for i in range(max(1, conductor // 4)):
            t = pow(5, i, conductor)
            phi[t] = phi[-t % conductor] = 351 * i
        exp = phi[x % conductor]
        if at_p:
            exp += 296 * log[x % P]
        if mirror:
            values = np.array([pow(root, -i, q) for i in range(ORD)], dtype=np.int64)
            weights = x * values[log[x % P]] % q
        else:
            eta = np.array([0, 1, 1, -1, 1, -1, -1], dtype=np.int64)
            weights = x * eta[x % 7]
        counts = np.zeros(ORD, dtype=np.int64)
        np.add.at(counts, exp % ORD, weights)
        nonzero = [(j, int(v)) for j, v in enumerate(counts) if v]
        for a in labels:
            if mirror and not a:
                continue
            s = sum(v * pow(root, (a if mirror else -a) * j, q) for j, v in nonzero) % q
            if at_p:
                assert s % P == 0
                b = s // P * pow(f // P, -1, P**2) % P**2
            else:
                b = s * pow(f, -1, P**2) % P**2
            results[a] = b
    return results


def mirror_family(a):
    m = P * P
    root = pow(5, P, m)
    logs = np.zeros(P, dtype=np.int64)
    for i in range(576):
        logs[pow(5, i, P)] = i
    order = 64 // gcd(a, 64)
    C = 4 * order
    n = (1 - 296 * a) % 576
    degree = lcm(order, 576 // gcd(576, n))
    f = C * P
    log2 = np.zeros(C, dtype=np.int64)
    for k in range(order):
        t = pow(5, k, C)
        log2[t] = log2[-t % C] = -351 * a * k
    v = np.arange(f // 2 + 1, f, 2, dtype=np.int64)
    v = v[v % P != 0]
    counts = np.bincount((log2[v % C] + n * logs[v % P]) % 576, minlength=576)
    return {
        j: sum(int(k) * pow(root, -j * i, m) for i, k in enumerate(counts) if k) % m
        for j in range(1, degree, 2)
    }


def main():
    mirrors = abelian_moments(True)
    assert len(mirrors) == 575
    singular = {a: b // P for a, b in mirrors.items() if b % P == 0}
    assert singular == {141: 209, 300: 21, 492: 291, 575: 419}
    print("Singular even-field mirrors and first quotients:", sorted(singular.items()))
    odd = abelian_moments(False)
    assert len(odd) == 576
    singular = {a: b // P for a, b in odd.items() if b % P == 0}
    assert singular == {276: 149, 336: 392, 407: 324, 447: 222}
    print("Singular base CM characters and first quotients:", sorted(singular.items()))
    for a, want in [
        (141, {1: 418}),
        (300, {1: 42, 193: 5, 313: 194, 359: 536}),
        (492, {1: 5, 121: 194, 385: 42, 551: 536}),
        (575, {1: 261}),
    ]:
        values = mirror_family(a)
        found = {j: v // P for j, v in values.items() if v % P == 0}
        assert found == want
        print("z exponent", a, "singular odd constituents of its mirror field", found)
    assert sum((j + 2) * 2 ** (j - 1) for j in range(1, 7)) * 9 == 4023
    assert P - (1 + 576 // 72) == 568
    print("Degree-577 real resolvent discriminant = 2^4023 * 577^568.")


if __name__ == "__main__":
    main()
