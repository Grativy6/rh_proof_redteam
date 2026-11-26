"""Enclose the two integer-quotient readings and the sign of each reconstructed jump."""
import argparse
from fractions import Fraction
from math import isqrt
import json

from check_pal_growth_windows import sieve
from check_pal_prime_transport import outward


SCALE = 2**74


def root_ratio(n, d):
    """Outward integer endpoints for SCALE*sqrt(n/d)."""
    square = n*SCALE*SCALE
    low = isqrt(square//d)
    return low, low + (low*low*d < square)


def show(interval, places=10):
    return [outward(Fraction(interval[0],SCALE),places,False),
            outward(Fraction(interval[1],SCALE),places,True)]


def add_signed(interval, sign, low, high):
    if sign > 0:
        return interval[0]+low, interval[1]+high
    if sign < 0:
        return interval[0]-high, interval[1]-low
    return interval


def explicit_remainders(head, mu, last=None):
    """Evaluate each original fractional cell as sqrt(q/d)-q/sqrt(head)."""
    il, ih = root_ratio(1,head)
    total = (0,0)
    early = (0,0)
    for d in range(1,(head if last is None else last)+1):
        if not mu[d] or head%d == 0:
            continue
        q = head//d
        a,b = root_ratio(q,d)
        total = add_signed(total,mu[d],a-q*ih,b-q*il)
        if d <= isqrt(head):
            early = add_signed(early,mu[d],a-q*ih,b-q*il)
    assert -SCALE//2 <= early[0] <= early[1] <= SCALE//2
    return total,early


def geometric_sign_certificate(head, mu, scale=10000):
    low = high = 0
    for d in range(1,head+1):
        q = head//d
        if not mu[d]:
            continue
        square = scale*scale*q
        a = isqrt(square//d)
        b = a + (a*a*d<square)
        low,high = add_signed((low,high),mu[d],a,b)
    return {"head":head,"denominator":scale,"numerators":[low,high]}


def compute(limit):
    mu,_,_ = sieve(limit)
    distinct = bytearray(limit+1)
    lower = [0]*(limit+1)
    width = [0]*(limit+1)
    weights = []
    for r in range(1,limit+1):
        root_l,root_h = root_ratio(r*(r-1),1)
        wl = r*SCALE-SCALE//2-root_h
        wh = r*SCALE-SCALE//2-root_l
        if r<=7:
            weights.append([r,show((wl,wh))])
        if r>1 and distinct[r]==0:
            for n in range(r,limit+1,r):
                distinct[n]+=1
        for d in range(1,limit//r+1):
            if not mu[d]:
                continue
            n = r*d
            lower[n] += wl if mu[d]>0 else -wh
            width[n] += wh-wl
    samples = sorted({n for n in [1,2,3,5,7,16,25,35,43,49,64,577,2663,10000,limit] if n<=limit})
    acc = (0,0)
    bsum = (0,0)
    rows = []
    first_below = None
    first_recovered = None
    square_below = None
    lowest = None
    highest = None
    selected = set(samples)
    last_square = (0,0)
    largest_square_gap = (0,0)
    square_low = square_high = None
    square_positive = square_negative = square_undecided = 0
    for n in range(1,limit+1):
        a, b = lower[n], lower[n]+width[n]
        assert -SCALE//2 <= a <= b <= SCALE//2
        if distinct[n]%2:
            assert b < 0, n
        else:
            assert a > 0, n
        sl, sh = root_ratio(1,n)
        products = [a*sl,a*sh,b*sl,b*sh]
        inc = min(products)//SCALE, -(-max(products)//SCALE)
        acc = acc[0]+inc[0], acc[1]+inc[1]
        bsum = add_signed(bsum,mu[n],sl,sh)
        if isqrt(n)**2 == n:
            last_square = acc
            early,_ = explicit_remainders(n,mu,last=isqrt(n))
            at_square = acc[0]+SCALE//2-sh-early[1], acc[1]+SCALE//2-sl-early[0]
            if square_low is None or at_square[1]<square_low[1][1]:
                square_low = n, at_square
            if square_high is None or at_square[0]>square_high[1][0]:
                square_high = n, at_square
            if at_square[0]>0:
                square_positive += 1
            elif at_square[1]<0:
                square_negative += 1
            else:
                square_undecided += 1
        gap = max(abs(acc[0]-last_square[1]),abs(acc[1]-last_square[0]))
        assert gap <= SCALE
        if gap > largest_square_gap[1]:
            largest_square_gap = (n,gap)
        shifted = acc[0]+SCALE//2, acc[1]+SCALE//2
        if lowest is None or shifted[1] < lowest[1][1]:
            lowest = (n,shifted)
        if highest is None or shifted[0] > highest[1][0]:
            highest = (n,shifted)
        if shifted[1] < 0 and first_below is None:
            first_below = (n,shifted)
            selected.add(n)
        if shifted[1] < 0 and isqrt(n)**2 == n and square_below is None:
            square_below = (n,shifted)
            selected.add(n)
        if first_below and first_recovered is None and shifted[0] > 0:
            first_recovered = (n,shifted)
            selected.add(n)
        if n in selected:
            corrected = acc[0]+SCALE//2-sh, acc[1]+SCALE//2-sl
            direct, early = explicit_remainders(n,mu)
            assert max(corrected[0],direct[0]) <= min(corrected[1],direct[1])
            rows.append({"head":n,"distinct_primes":distinct[n],"mobius":int(mu[n]),
                         "stable_step":show(inc),"stable_sum":show(acc),
                         "cell_residue":show(corrected),"direct_early_cells":show(early),
                         "weighted_mobius_sum":show(bsum)})
    def reading(point):
        return None if point is None else [point[0], show(point[1])]
    return {"through":limit,"scale":str(SCALE),"weights":weights,"samples":rows,
            "normalized_square_remainder":{"square_heads":isqrt(limit),"positive":square_positive,
                                           "negative":square_negative,"enclosed_zero":square_undecided,
                                           "low_witness":reading(square_low),"high_witness":reading(square_high)},
            "largest_observed_square_gap_upper":[largest_square_gap[0],outward(Fraction(largest_square_gap[1],SCALE),10,True)],
            "square_root_sign_certificates":[geometric_sign_certificate(n,mu) for n in (31,33,81) if n<=limit],
            "geometric_mean_sum":{"first_strict_negative_witness":reading(first_below),
                                  "next_strict_positive_witness":reading(first_recovered),
                                  "strict_negative_square_witness":reading(square_below),
                                  "low_witness":reading(lowest),"high_witness":reading(highest)}}


def row_budget(j, mu):
    """Sum the actual positive and negative prefix peaks in each late quotient row."""
    head = j*j
    a = j+1
    rises = falls = rows = 0
    upper = lower = 0
    while a<=head:
        q = head//a
        b = head//q
        mass = peak = trough = 0
        for d in range(a,b+1):
            mass += mu[d]
            peak = max(peak,mass)
            trough = min(trough,mass)
        # The total normalized weight in this row is sqrt(q/a)-q/j.
        _,sqrt_hi = root_ratio(q,a)
        weight_hi = sqrt_hi-(q*SCALE//j)
        assert weight_hi>=0
        upper += peak*weight_hi
        lower += trough*weight_hi
        rows += 1
        rises += peak
        falls -= trough
        a = b+1
    return {"rows":rows,"sum_positive_prefix_peaks":rises,"sum_negative_prefix_depths":falls,
            "directed_normalized_range":show((lower,upper))}


def additional_square(j):
    head = j*j
    mu,_,_ = sieve(head)
    total,early = explicit_remainders(head,mu)
    late = total[0]-early[1],total[1]-early[0]
    # Count the divisor rectangle independently on this same head.
    assert sum(mu[d]*(head//d) for d in range(1,head+1)) == 1
    budget = row_budget(j,mu)
    assert Fraction(budget["directed_normalized_range"][0]) <= Fraction(late[0],SCALE)
    assert Fraction(late[1],SCALE) <= Fraction(budget["directed_normalized_range"][1])
    return {"root":j,"head":head,"all_cells":show(total),"normalized_square_remainder":show(late),"row_budget":budget,
            "corner":[[d,head//d,head%d,int(mu[d])] for d in range(j,min(head,j+4)+1)]}


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head",type=int,default=200000)
    parser.add_argument("--square-root",type=int,default=2663)
    options=parser.parse_args()
    if options.head<1:
        parser.error("head must be positive")
    result=compute(options.head)
    if options.square_root>0:
        result["additional_square"]=additional_square(options.square_root)
    print(json.dumps(result,indent=2))
