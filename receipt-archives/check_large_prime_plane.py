"""Check determinant averages in exact factorial digit weights at a larger prime."""

from math import comb, factorial, prod

from check_plane_determinant import first_weight


def weak_compositions(total, size):
    if size == 1:
        yield (total,)
        return
    for i in range(total + 1):
        for rest in weak_compositions(total-i, size-1):
            yield (i, *rest)


def valuation(p, n):
    assert n > 0
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def weight_table(p, residue, degree, modulus):
    """The factorial ratio for P=p, by its two exact integer-product identities."""
    inv = [0] + [pow(j, -1, modulus) for j in range(1, p)]
    values = []
    core = 1
    for k in range(degree + 1):
        factor = 1
        low = 1
        for j in range(1, p):
            factor = factor * (1+p*k*inv[j]) % modulus
            if j == residue:
                low = factor
        values.append(core*low % modulus)
        core = core*factor % modulus
    return values


def check_average(p, r, degree, digits):
    size = comb(degree + r - 1, r - 1)
    t = valuation(p, size)
    modulus = p**(t+1)
    tables = [weight_table(p, residue, degree, modulus) for residue in digits]
    total = sum(prod(table[k] for table, k in zip(tables, parts))
                for parts in weak_compositions(degree, r)) % modulus
    assert (total - size) % modulus == 0
    for digit, table in zip(digits, tables):
        for k in range(min(4, degree+1)):
            ratio = factorial(p*k+digit)//(factorial(digit)*factorial(k)*factorial(p)**k)
            assert ratio % modulus == table[k]
    print(f'p={p}, r={r}, a={degree}: {size} compositions, '
          f'valuation of both sums {t}, normalized mean 1 modulo {p}.')


def lifted_ratio(p, target, precision):
    """Return two legal low digits whose positive factorial units have this ratio."""
    assert target % p == 1
    u = v = 0
    for height in range(1, precision):
        modulus = p**(height+1)
        old = (first_weight(p, height-1, u, modulus)
               * pow(first_weight(p, height-1, v, modulus), -1, modulus)) % modulus
        assert (target-old) % p**height == 0
        delta = (target-old)//p**height % p
        if delta:
            digit = pow(delta, -1, p)
            du, dv = digit, digit-1
        else:
            du = dv = 0
        u, v = p*u+du, p*v+dv
        ratio = (first_weight(p, height, u, modulus)
                 * pow(first_weight(p, height, v, modulus), -1, modulus)) % modulus
        assert ratio == target % modulus
    return u, v


def check_near_determinant(p, rank, precision):
    a = p-rank+1
    u, v = lifted_ratio(p, -(a+rank-2), precision)
    modulus = p**precision
    w1, w2 = (first_weight(p, precision-1, k, modulus) for k in (u, v))
    assert (w1 + (a+rank-2)*w2) % modulus == 0
    assert factorial(rank-1)*factorial(a-1)*w1 % p
    print(f'p={p}, rank={rank}, row degree={a}, digits=({u}, {v}): '
          f'exact-type pairing 0 modulo {modulus}, cofactor a unit.')


def check_all_cells_binary(p, degree):
    modulus = p**(valuation(p, degree+1) + 1)
    tabs = [weight_table(p, d, degree, modulus) for d in (1, 7, 11, 19)]
    total = sum(tabs[0][k]*tabs[1][degree-k]*tabs[2][degree-k]*tabs[3][k]
                for k in range(degree+1))
    assert (total - (degree+1)) % modulus == 0
    print(f'p={p}, binary determinant degree={degree}: normalized four-cell '
          'average 1 in the residue field.')


def main():
    check_near_determinant(79, 3, 4)
    check_near_determinant(17, 4, 5)
    check_all_cells_binary(53, 53**2-1)
    check_average(17, 3, 15, (1, 7, 16))
    check_average(17, 3, 287, (1, 7, 16))
    check_average(19, 4, 17, (3, 5, 7, 18))


if __name__ == '__main__':
    main()
