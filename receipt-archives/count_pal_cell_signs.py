"""Classify the actual two-head price at every integer label by its quotient cell."""
import json
from math import isqrt


def sign(x):
    return (x > 0)-(x < 0)


def source_numerator(T,d):
    if d > T:
        return 0
    r = T%d
    u = r*(d-r)
    return T*u*(d-2*r)-u*u


def cell_numerator(X,d):
    """The result is 16 d X^3 times G(2X,d)-G(X,d)."""
    if d > 2*X:
        return 0
    if d > X:
        return (2*X-d)*(2*d-2*X)*(2*d*d-4*X*X)
    k,r = divmod(X,d)
    if 2*r < d:
        return 4*r*(2*r**3+k*d*(4*r*r-d*d))
    v = d-r
    return 4*v*(2*v**3+(k+1)*d*(d*d-4*v*v))


def census(X):
    D = isqrt(X)
    tally = {-1:0, 0:1, 1:0}       # d=2X is the outer endpoint.
    middle = isqrt(2*X*X)
    tally[-1] += middle-X
    tally[1] += 2*X-1-middle
    for d in range(1,D+1):
        tally[sign(cell_numerator(X,d))] += 1
    for k in range(1,X//(D+1)+1):
        first = max(D+1,X//(k+1)+1)
        last = X//k
        if first > last:
            continue
        if X%last == 0:
            tally[0] += 1
            last -= 1
        # As the label increases, its phase decreases across the unique interior root.
        lo,hi = first,last+1
        while lo < hi:
            mid = (lo+hi)//2
            if cell_numerator(X,mid) > 0:
                lo = mid+1
            else:
                hi = mid
        tally[1] += lo-first
        tally[-1] += last+1-lo
    assert sum(tally.values()) == 2*X
    return tally


def limiting_positive_density(K=1024):
    # rho is the limiting number of positive labels divided by X. The full support has 2X labels.
    grid = 2**50
    scale = 10**15
    root = isqrt(2*grid*grid)
    low, high = 2*grid-root-1, 2*grid-root
    lower, upper = low*scale//grid, -(-high*scale//grid)
    for k in range(1,K+1):
        lo,hi = 0,grid//2
        while hi-lo > 1:
            mid = (lo+hi)//2
            if 2*mid**3 + k*grid*(4*mid**2-grid**2) > 0:
                hi = mid
            else:
                lo = mid
        # The positive subinterval has length 1/(k+tau)-1/(k+1).
        den_lo, den_hi = (k*grid+hi)*(k+1), (k*grid+lo)*(k+1)
        lower += (grid-hi)*scale//den_lo
        upper += -(-(grid-lo)*scale//den_hi)
    tail_floor = scale//(2*(K+1))
    tail_error_ceiling = (scale + 8*K*K-1)//(8*K*K)
    lower += tail_floor-tail_error_ceiling
    upper += -(-scale//(2*(K+1)))
    assert lower > scale and upper < 2*scale
    return {"K":K,"unit_denominator":scale,"positive_per_X_lower":lower,
            "positive_per_X_upper":upper,"full_support_per_X":2}


def replay():
    pairs = 0
    for X in range(1,513):
        direct = {-1:0,0:0,1:0}
        for d in range(1,2*X+1):
            reference = source_numerator(2*X,d)-8*source_numerator(X,d)
            assert reference == cell_numerator(X,d)
            assert (reference == 0) == (X%d == 0 or d == 2*X)
            direct[sign(reference)] += 1
            pairs += 1
        assert direct == census(X)
    heads = {}
    for X in (577,2663,1100**4,10**12):
        rows = census(X)
        heads[str(X)] = {"negative":rows[-1],"zero":rows[0],"positive":rows[1]}
    assert heads[str(10**12)]["zero"] == 13**2+1
    return {"heads":heads,"limiting_positive_density":limiting_positive_density(),"direct_comparisons":pairs,"range_of_dense_heads":[1,512],
            "zero_rule":"On 1 <= d <= 2X the two-head price vanishes exactly at divisors of X and d = 2X."}


if __name__ == "__main__":
    print(json.dumps(replay(),indent=2))
