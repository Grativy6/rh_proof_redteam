"""Two directed trace differences over F_577[t]/t^4, computed by matrix products."""

import numpy as np

P = 577
N = 4


def e(i, j):
    m = np.zeros((3, 3), dtype=np.int64)
    m[i - 1, j - 1] = 1
    return m


L = e(2, 1) - e(3, 2)
U = e(1, 2) + e(2, 3)
V = e(1, 3)
eye = np.eye(3, dtype=np.int64)


def constant(m):
    M = np.zeros((N, 3, 3), dtype=np.int64)
    M[0] = m
    return M


one = constant(eye)


def multiply(A, B):
    out = np.zeros_like(A)
    for k in range(N):
        for j in range(k + 1):
            out[k] += A[j] @ B[k - j]
    return out % P


def inverse(A):
    # All constant terms used in this check are invertible diagonal matrices.
    assert np.array_equal(A[0], np.diag(np.diag(A[0])))
    out = np.zeros_like(A)
    out[0] = np.diag([pow(int(a), -1, P) for a in np.diag(A[0])])
    for k in range(1, N):
        term = sum(
            (A[j] @ out[k - j] for j in range(1, k + 1)),
            start=np.zeros((3, 3), dtype=np.int64),
        )
        out[k] = -out[0] @ term % P
    assert np.array_equal(multiply(A, out), one)
    return out


def conj(A, B):
    return multiply(multiply(A, B), inverse(A))


def comm(A, B):
    return multiply(conj(A, B), inverse(B))


def root(M):
    A = one.copy()
    A[1] = M % P
    A[2] = M @ M * pow(2, -1, P) % P
    return A


def directed(A):
    return np.trace((A - inverse(A)) % P, axis1=1, axis2=2) % P


def words(x, u, v):
    h = constant(np.diag([510, 1, 155]))
    g = multiply(multiply(root(x * L), root(u * U)), root(v * V))
    g1 = conj(h, g)
    g2 = conj(h, g1)
    w2 = multiply(h, comm(g, g1))
    w3 = multiply(h, comm(g, comm(g1, g2)))
    return directed(w2), directed(w3)


def main():
    s = 510
    f = (4 - 2 * (s + pow(s, -1, P))) % P
    c1 = (s - pow(s, -1, P)) * f % P
    c2 = (pow(s, 3, P) - 1) * f % P
    assert (f, c1, c2, c1 * c2 % P) == (405, 102, 473, 355)
    a, b = words(1, 1, 0)
    assert a[:3].tolist() == [0, 0, 102] and not np.any(b[:3])
    a, b = words(1, 0, 1)
    assert b.tolist() == [0, 0, 0, 473]
    a, b = words(511, 468, 95)
    # The order-three comparison ignores the nearest-upper entries in its
    # weight-zero contribution. Only two lowers and one highest upper contribute.
    assert int(a[2]) == 421 and int(b[3]) == 573
    print("Directed trace derivative diagonal:", c1, c2, "determinant", c1 * c2 % P)
    print(
        "Common arithmetic commutator, second and third order readings:",
        int(a[2]),
        int(b[3]),
    )


if __name__ == "__main__":
    main()
