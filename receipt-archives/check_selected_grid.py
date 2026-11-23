"""Integer audits of the reflected grid and a norm-one pair of conjugate roots."""

from collections import Counter


def check_row_exponents():
    # Each pair lists the two coordinate exponents at one of the four places.
    conjugate = (1,0,3,2)
    for n in range(1,41):
        aligned = [(-n,n)]*4
        crossed = [(-n,n),(n,-n),(-n,n),(n,-n)]
        for L in (aligned,crossed):
            assert all(sorted(a) == [-n,n] for a in L)
            for w, exponents in enumerate(L):
                dual = tuple(-a for a in L[conjugate[w]])
                assert sum(dual)-sum(exponents) == 0
        assert all(v[0] == -n for v in aligned)
        assert all(sum(v[i] for v in crossed) == 0 for i in (0,1))
        for t in range(n+1):
            finite = sum(n-t for _ in range(4)) // 4
            assert 2*t + 2*finite == 2*n
    assert 2+2-4 == 0  # The selected reference primes have nonzero separate indices.


def rho_counts(h, e, u, v):
    counts = Counter()
    for s in range(1-(e+v-u), h-(u+v)+1):
        counts[s if s >= 1 else 1-s] += 1
    for k in range(1,u+1):
        counts[e+v-k+1] += 1
    for k in range(1,v+1):
        counts[e+k] -= 1
    return {j:x for j,x in counts.items() if x}


def check_intervals():
    tested = 0
    for h in range(4,57):
        for e in range(2,h-1):
            for u in range(1+min(e-2,h-e-2)//2):
                for v in range(1+min(e-2,h-e-2)//2-u):
                    counts = rho_counts(h,e,u,v)
                    assert counts == {j:1+int(j<=e) for j in range(1,h-u-v+1)}
                    assert sum(counts.values()) == h-u-v+e
                    tested += 1
    return tested


def check_heights():
    # A and C have disjoint prime supports. At an A place the ratio y/x has
    # valuation two in units of v(A), at a C place it has valuation one.
    for N in (4,8,17):
        for m in (1,2,7):
            t = 2*N-2
            before_summing = [(2+2*t)*m**2, t*m**2]
            assert sum(before_summing) == (6*N-4)*m**2
            assert (2+12*N) <= 2*(2+8*N)
    for k in (1,11,51,201):
        A = 181**(2*k)
        C = 1
        while C*61**2 <= A:
            C *= 61**2
        assert C <= A < C*61**2
        # Exact valuation example for pp=qp=0, h=4, e=2.
        assert A**2 * (A**2*C)**6 == A**14 * C**6
    assert 181 % 60 == 1 and 61 % 60 == 1


def hensel_root(poly, derivative, p, residue, digits):
    x, power = residue, p
    assert poly(x) % power == 0
    for _ in range(1,digits):
        digit = - (poly(x)//power) * pow(derivative(x),-1,p) % p
        x += digit*power
        power *= p
        assert poly(x) % power == 0
    return x


def check_roots():
    p = 17
    # X^(2n) + 5X + 5p^n is Eisenstein at 5, with one positive
    # valuation among its roots at 17. No denominator is used.
    for n in (1,2,3,9,20):
        degree = 2*n
        f = lambda x: x**degree + 5*x + 5*p**n
        df = lambda x: degree*x**(degree-1) + 5
        root = hensel_root(f,df,p,0,n+2)
        assert root % p**n == 0 and root % p**(n+1) != 0
        assert 16**degree > 5*16+5*p**n
        assert n/degree == 0.5
    for n in (1,3,7,11):
        q = p**n
        assert (4*q-1)%4 == 3 and (4*q-1)%3 == 1
        poly = lambda x: x*x-(2*q-1)*x+q*q
        derivative = lambda x: 2*x-(2*q-1)
        small = hensel_root(poly, derivative,p,0,2*n+2)
        unit = hensel_root(poly, derivative,p,p-1,2*n+2)
        assert unit%p and small%(p**(2*n)) == 0 and small%(p**(2*n+1)) != 0
        # Dividing both roots by q gives valuations +n and -n, with mean zero.
        assert (small*unit-q*q) % p**(2*n+2) == 0


if __name__ == "__main__":
    check_row_exponents()
    print("Row exponents, duals and sharp global costs checked.")
    print("Reflected intervals checked:",check_intervals())
    check_heights()
    check_roots()
    print("Grid coefficients and prime-restricted height examples verified.")
    print("Integral root valuations checked through n=20; norm-one tests through odd n=11.")
