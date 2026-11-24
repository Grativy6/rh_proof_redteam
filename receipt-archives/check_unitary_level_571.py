"""Count the two projective-line fibers at 571 for Loeffler's definite U(3)."""
from collections import deque
from fractions import Fraction

P = 571
LINES = P*P + P + 1
IDENTITY = (1,0,0, 0,1,0, 0,0,1)
SIGNED = ((-1,0,0, 0,1,0, 0,0,1), (0,1,0, 1,0,0, 0,0,1), (1,0,0, 0,0,1, 0,1,0))
INV = [0] + [pow(x, -1, P) for x in range(1, P)]
LEGENDRE = [0] + [1 if pow(x, (P-1)//2, P) == 1 else -1 for x in range(1, P)]


def times(a, b):
    return tuple(sum(a[3*i+k]*b[3*k+j] for k in range(3)) % P
                 for i in range(3) for j in range(3))


def determinant(m):
    a,b,c,d,e,f,g,h,i = m
    return (a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)) % P


def group(generators, size):
    seen = {IDENTITY}
    queue = [IDENTITY]
    for g in queue:
        for h in generators:
            gh = times(g, h)
            if gh not in seen:
                seen.add(gh)
                queue.append(gh)
                assert len(seen) <= size
    assert len(seen) == size
    return seen


def nullity(m):
    if determinant(m):
        return 0
    for i, k in ((0,1), (0,2), (1,2)):
        for j, h in ((0,1), (0,2), (1,2)):
            if (m[3*i+j]*m[3*k+h] - m[3*i+h]*m[3*k+j]) % P:
                return 1
    return 2 if any(m) else 3


def burnside(matrices):
    plain = line = quotient = 0
    for g in matrices:
        det_sign = LEGENDRE[determinant(g)]
        # An eigenvalue in F_p^* has order dividing both group orders.
        for u in range(1, P):
            if pow(u, len(matrices), P) != 1:
                continue
            m = tuple((x - u*e) % P for x, e in zip(g, IDENTITY))
            count = (P**nullity(m) - 1)//(P-1)
            plain += count
            line += count*LEGENDRE[u]
            quotient += count*LEGENDRE[u]*det_sign
    weights = (plain, line, quotient)
    assert all(v % len(matrices) == 0 for v in weights)
    return tuple(v//len(matrices) for v in weights)


def vector(index):
    if index < P*P:
        a, b = divmod(index, P)
        return 1, a, b
    if index < P*P + P:
        return 0, 1, index-P*P
    return 0, 0, 1


def normalize(a, b, c):
    if a:
        return (b*INV[a] % P)*P + c*INV[a] % P, a
    if b:
        return P*P + c*INV[b] % P, b
    return P*P + P, c


def signed_orbits(generators):
    signs = bytearray(LINES)
    plain = supported = 0
    mats = [(g, LEGENDRE[determinant(g)]) for g in generators]
    for start in range(LINES):
        if signs[start]:
            continue
        plain += 1
        signs[start] = 1
        good = True
        queue = deque([start])
        while queue:
            j = queue.popleft()
            x, y, z = vector(j)
            for (a,b,c,d,e,f,g,h,i), det_sign in mats:
                dest, scale = normalize((a*x+b*y+c*z) % P, (d*x+e*y+f*z) % P,
                                        (g*x+h*y+i*z) % P)
                sign = signs[j] if LEGENDRE[scale]*det_sign == 1 else 3-signs[j]
                if not signs[dest]:
                    signs[dest] = sign
                    queue.append(dest)
                elif signs[dest] != sign:
                    good = False
        supported += good
    return plain, supported


def neighbours(w):
    a = w*INV[(1-w) % P] % P
    diag = []
    for j in range(3):
        g = list(IDENTITY)
        g[4*j] = a
        diag.append(tuple(g))
    t = w*INV[2] % P
    rows = ((1,0,0), (0,t,-t % P), (0,t,t))
    for j in range(3):
        diag.append(sum(rows[j:] + rows[:j], ()))
    return diag


def transposed(m):
    return tuple(m[3*j+i] for i in range(3) for j in range(3))


def move(m, v):
    return normalize(*(sum(m[3*i+j]*v[j] for j in range(3)) % P for i in range(3)))


def orbit_values(v, matrices):
    values = {}
    for g in matrices:
        pos, scale = move(g, v)
        val = LEGENDRE[determinant(g)]*LEGENDRE[scale]
        if pos in values and val != values[pos]:
            return {}
        values[pos] = val
    return values


def row_entry(operators, v, values):
    total = 0
    for g in operators:
        pos, scale = move(g, v)
        total += LEGENDRE[determinant(g)]*LEGENDRE[scale]*values.get(pos, 0)
    return total


def compare_neighbours(w, matrices):
    direct, opposite = neighbours(w), neighbours((1-w) % P)
    assert all(times(g, transposed(h)) == IDENTITY for g, h in zip(direct, opposite))
    forward = [transposed(h) for h in opposite]
    backward = [transposed(g) for g in direct]
    v = (1, 2, 3)
    assert orbit_values(v, matrices)
    for g in forward:
        pos, _ = move(g, v)
        y = vector(pos)
        values = orbit_values(y, matrices)
        if values:
            a, b = (row_entry(ops, v, values) for ops in (forward, backward))
            if (a-b) % 5:
                return v, y, a, b
    raise AssertionError("Missing a directed Hecke witness")


def main():
    assert P % 4 == 3 and LINES == 326613
    roots = [w for w in range(P) if (w*w-w+2) % P == 0]
    assert len(roots) == 2
    signed = [tuple(x % P for x in g) for g in SIGNED]
    base = group(signed, 48)
    answers = []
    for w in roots:
        tau = tuple(x*INV[2] % P for x in (-1, 1-w, 1, -1, w-1, 1, w, 0, w))
        generators = signed + [tau]
        other = group(generators, 336)
        rows = [burnside(base), burnside(other)]
        if not answers:
            assert signed_orbits(signed) == (rows[0][0], rows[0][2])
            assert signed_orbits(generators) == (rows[1][0], rows[1][2])
        answers.append(rows)
    assert answers[0] == answers[1]
    assert answers[0] == [(13825, 0, 13396), (2017, 0, 1874)]
    probe = compare_neighbours(roots[0], base)
    assert (roots[0], probe) == (159, ((1, 2, 3), (1, 157, 521), 1, 0))
    print("Directed split-prime test at 2:", probe)
    for size, row in zip((48, 336), answers[0]):
        print(f"stabilizer {size}: trivial={row[0]}, line character={row[1]}, "
              f"quotient determinant={row[2]}")
    print("Mass =", LINES*(Fraction(1,48)+Fraction(1,336)))


if __name__ == "__main__":
    main()
