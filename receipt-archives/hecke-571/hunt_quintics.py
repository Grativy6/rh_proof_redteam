"""Targeted Hunter search for the totally real quintic residual alternative."""

from itertools import product
from math import comb, isqrt
from pathlib import Path
import sys


def multiply(a, b, p):
    z = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            z[i + j] = (z[i + j] + x * y) % p
    return tuple(z)


def power(a, n, p):
    b = (1,)
    for _ in range(n):
        b = multiply(b, a, p)
    return b


def divisible(f, g, p):
    f = list(f)
    for i in range(len(f) - len(g) + 1):
        c = f[i]
        for j, b in enumerate(g):
            f[i + j] = (f[i + j] - c * b) % p
    return not any(f)


def four_cycle(p):
    linear = [(1, a) for a in range(p)]
    irr2 = [
        (1,) + s
        for s in product(range(p), repeat=2)
        if not any(divisible((1,) + s, g, p) for g in linear)
    ]
    irr4 = [
        (1,) + s
        for s in product(range(p), repeat=4)
        if not any(divisible((1,) + s, g, p) for g in linear + irr2)
    ]
    orbit = [power(g, 4, p) for g in linear] + [power(g, 2, p) for g in irr2] + irr4
    return {multiply(g, l, p)[1:] for g in orbit for l in linear}


def positive_discriminant(a):
    # Positive definite power-trace form is necessary for five distinct real roots.
    s = [5]
    for k in range(1, 9):
        v = sum(a[j - 1] * s[k - j] for j in range(1, min(k, 6)))
        s.append(-v - (k * a[k - 1] if k <= 5 else 0))
    h = [s[i : i + 5] for i in range(5)]
    previous = 1
    for k in range(4):
        pivot = h[k][k]
        if pivot <= 0:
            return 0
        for i in range(k + 1, 5):
            for j in range(i, 5):
                h[i][j] = (h[i][j] * pivot - h[i][k] * h[k][j]) // previous
                h[j][i] = h[i][j]
        previous = pivot
    return max(0, h[-1][-1])


def congruent(residue, limit):
    p = 571
    return range(-limit + (residue + limit) % p, limit + 1, p)


def search(exponent, frob):
    q = 571
    target = 5**exponent * q * q
    bound = {3: 77, 5: 170}[exponent]
    limits = [isqrt(comb(5, j) ** 2 * bound**j // 5**j) for j in range(6)]
    tame = {multiply(power((1, a), 4, 5), (1, b), 5)[1:] for a in range(5) for b in range(5)}
    counts = [0, 0, 0]
    result = []
    for a in range(3) if exponent == 3 else [0]:
        for b in range(-bound, (a * a) // 2 + 1):
            if not 0 < a * a - 2 * b <= bound or (exponent == 5 and b % 5):
                continue
            for A in range(q):
                C = (a - 2 * A) % q
                B = ((b - A * A - 2 * A * C) * 286) % q
                rc = (2 * A * B + C * (A * A + 2 * B)) % q
                rd = (B * B + 2 * A * B * C) % q
                re = B * B * C % q
                for c in congruent(rc, limits[3]):
                    if exponent == 5 and c % 5:
                        continue
                    for d in congruent(rd, limits[4]):
                        if exponent == 5 and d % 5:
                            continue
                        for e in congruent(re, limits[5]):
                            t = (a, b, c, d, e)
                            if not e:
                                continue
                            if exponent == 3 and tuple(v % 5 for v in t) not in tame:
                                continue
                            counts[0] += 1
                            if any(tuple(v % p for v in t) not in allowed for p, allowed in frob):
                                continue
                            counts[1] += 1
                            disc = positive_discriminant(t)
                            if not disc or disc % target:
                                continue
                            index = isqrt(disc // target)
                            if index * index * target != disc:
                                continue
                            result.append(t)
                            counts[2] += 1
    assert len(set(result)) == len(result)
    return counts, result


def main():
    from pentagons import simple_integral_root

    frob = [(p, four_cycle(p)) for p in (2, 3, 7)]
    for exponent, expected in [(3, [15178, 488, 11]), (5, [1282714, 36004, 58])]:
        counts, forms = search(exponent, frob)
        assert counts == expected
        roots = [simple_integral_root(f) for f in forms]
        assert len(roots) == len(forms)
        print(
            f"5-exponent {exponent}: {counts}. Every survivor has a simple rational resolvent root."
        )
        if len(sys.argv) > 1:
            path = Path(sys.argv[1]) / f"hunter-{exponent}.txt"
            with path.open("w", encoding="ascii", newline="\n") as stream:
                for f in forms:
                    stream.write("[" + ",".join(map(str, f)) + "]\n")


if __name__ == "__main__":
    main()
