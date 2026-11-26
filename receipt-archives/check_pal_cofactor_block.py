"""Factor all quotients in one fourth-power block and carry four specified cofactors."""
from fractions import Fraction as Q
import json
from math import isqrt, prod
from check_pal_prime_transport import outward, SCALE, transport_enclosure


def is_prime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n)+1))


def factor_tags(start, stop, minimum_prime):
    """Classify each quotient by all its factors. -1 means it is outside this family."""
    root = isqrt(stop)
    sieve = bytearray(b'\1')*(root+1)
    sieve[:2] = b'\0\0'
    for p in range(2, isqrt(root)+1):
        if sieve[p]:
            sieve[p*p::p] = b'\0'*len(sieve[p*p::p])
    rem = list(range(start, stop+1))
    tags = bytearray(len(rem))
    big = bytearray(len(rem))
    active = bytearray(b'\1')*len(rem)
    for p in range(2,root+1):
        if not sieve[p]:
            continue
        for n in range(((start+p-1)//p)*p,stop+1,p):
            i = n-start
            if not active[i]:
                continue
            rem[i] //= p
            if rem[i] % p == 0 or p <= 3 or 347 < p <= minimum_prime:
                active[i] = 0
            elif p <= 347:
                tags[i] += 1
            else:
                big[i] += 1
    for i, left in enumerate(rem):
        if active[i] and left > 1:
            if left <= 3 or 347 < left <= minimum_prime:
                active[i] = 0
            elif left <= 347:
                tags[i] += 1
            else:
                big[i] += 1
    return [k if active[i] and big[i] == 1 else -1 for i,k in enumerate(tags)]


def trial_tag(n, minimum_prime):
    """Reference trial division on selected labels."""
    factors = []
    p = 2
    while p*p <= n:
        while n % p == 0:
            factors.append(p)
            n //= p
        p += 1 if p == 2 else 2
    if n > 1:
        factors.append(n)
    if len(factors) != len(set(factors)) or min(factors) < 5:
        return -1
    large = [p for p in factors if p > 347]
    return len(factors)-1 if len(large) == 1 and large[0] > minimum_prime else -1


def carry_block(m, smooth, other_primes, ledgers=None):
    A, B = m**4, (m+1)**4
    assert len(set(other_primes)) == len(other_primes)
    assert all(p > 347 and is_prime(p) for p in other_primes)
    leftover = smooth
    for p in (2,3):
        while leftover % p == 0:
            leftover //= p
    assert smooth >= 1 and leftover == 1
    c = smooth**2*prod(other_primes)
    assert c**50 <= A**21                  # gamma = 21/50 < 11/26
    minimum = max([347, *other_primes])
    start, stop = A//c+1, B//c
    tags = factor_tags(start,stop,minimum)
    for i in list(range(0,len(tags),max(1,len(tags)//150)))+[len(tags)-1]:
        assert tags[i] == trial_tag(start+i, minimum)
    scale = 577*2663
    T = (100*A//(81*scale))*scale
    assert Q(4,5) <= Q(A,T) < Q(B,T) <= Q(5,6)
    size_max = max(tags)
    counts = [0]*(size_max+1)
    lo = [[0]*12 for _ in range(5)]
    hi = [[0]*12 for _ in range(5)]
    residual_lo = residual_hi = 0
    width = B-A
    binomial = [1,4,6,4,1]
    for i,k in enumerate(tags):
        if k < 0:
            continue
        d = c*(start+i)
        j = min(4, (5*(d-A)-1)//width)
        columns = [10] if k == 0 else ([j,11] if k == 1 else ([11] if k % 2 else [5+j]))
        counts[k] += 1
        a,b = d-A, B-d
        denom = d*width**4
        for line,choose in enumerate(binomial):
            num = SCALE*A*choose*a**line*b**(4-line)
            val, rem = divmod(num,denom)
            for col in columns:
                lo[line][col] += val
                hi[line][col] += val+bool(rem)
        num = SCALE*(T**4-3*T**3*d+6*T*d**3-4*d**4)
        denom = 2*d*T**3
        lb, rem = divmod(num, denom)
        ub = lb+bool(rem)
        if k % 2:
            residual_lo -= ub
            residual_hi -= lb
        else:
            residual_lo += lb
            residual_hi += ub
    w = transport_enclosure([r[:5]+[r[10]] for r in lo], [r[:5]+[r[10]] for r in hi])
    v = transport_enclosure([l[5:10]+[l[11]-h[10]] for l,h in zip(lo,hi)],
                            [h[5:10]+[h[11]-l[10]] for l,h in zip(lo,hi)])
    surviving_sign = -(-1)**len(other_primes)
    excess = sum(counts[::2])-sum(counts[1::2])
    assert excess > 0 and 0 < residual_lo <= residual_hi
    oriented = sorted([surviving_sign*smooth*Q(bound,SCALE) for bound in (residual_lo,residual_hi)])
    if ledgers is not None:
        offer_lo = [[smooth*x for x in row[5:10]] for row in lo]
        offer_hi = [[smooth*x for x in row[5:10]] for row in hi]
        balance_lo = [smooth*(sum(l[5:10])+l[10]-h[11]) for l,h in zip(lo,hi)]
        balance_hi = [smooth*(sum(h[5:10])+h[10]-l[11]) for l,h in zip(lo,hi)]
        ledgers[c] = offer_lo,offer_hi,balance_lo,balance_hi
    pair = None
    if len(other_primes) == 1:
        p = other_primes[0]
        assert T % p == 0
        pair = {"scale":p,"preimage_integer_head":T//p,
                "preimage_signed_price":[outward(-oriented[1],5,False),outward(-oriented[0],5,True)]}
    return {"cofactor":c,"same_labels_under_prime_dilation":pair,"smooth_root":smooth,"outside_palette_factors":list(other_primes),
            "large_prime_strictly_above":minimum,"counts_by_number_of_small_tags":counts,
            "sign_of_every_remaining_mark":surviving_sign,"unspent_magnitude_in_unit_marks":excess,
            "unspent_signed_constant_moment":surviving_sign*smooth*excess,
            "head":T,"unspent_signed_point_price":[outward(oriented[0],5,False),outward(oriented[1],5,True)],
            "first_fractions":w,"second_fractions":v}


def cover_across_cofactors(ledgers, cases, offer, targets):
    Mlo,Mhi,_,_ = ledgers[offer]
    b_lo,b_hi = [0]*5,[0]*5
    for c, orientation in targets:
        _,_,lo,hi = ledgers[c]
        for i in range(5):
            b_lo[i] += lo[i] if orientation > 0 else -hi[i]
            b_hi[i] += hi[i] if orientation > 0 else -lo[i]
    step = transport_enclosure([row+[b] for row,b in zip(Mlo,b_lo)],
                              [row+[b] for row,b in zip(Mhi,b_hi)])
    used = cases[offer]["second_fractions"]["actual_fraction_intervals"]
    extra = step["actual_fraction_intervals"]
    slack = min(1-Q(x[1])-Q(y[1]) for x,y in zip(used,extra))
    assert slack > 0
    return {"offered_cofactor":offer,"target_cofactors_and_orientations":targets,
            "extra_fractions_of_original_even_bins":step,
            "minimum_certified_unspent_fraction_after_both":outward(slack,7,False)}


def replay():
    m = 1100
    cases = [(108, ()), (4,(577,)), (2,(2663,)), (1,(349,353))]
    ledgers = {}
    result = [carry_block(m,v,primes,ledgers) for v,primes in cases]
    index = {row["cofactor"]:row for row in result}
    first = cover_across_cofactors(ledgers,index,9232,[(123197,1)])
    second = cover_across_cofactors(ledgers,index,11664,[(9232,1),(10652,1),(123197,-1)])
    left = sum(row["unspent_signed_constant_moment"] for row in result)
    lo = sum(Q(row["unspent_signed_point_price"][0]) for row in result)
    hi = sum(Q(row["unspent_signed_point_price"][1]) for row in result)
    assert left == -512206 and hi < 0
    return {"block_left_excluded":m**4,"block_right_included":(m+1)**4,
            "moment_method":"termwise integer enclosures at every actual physical label",
            "cofactor_exponent":"21/50","cases":result,"cross_cofactor_steps":[first,second],
            "final_residual_cofactor":11664,"final_signed_constant_moment":left,
            "final_signed_point_price":[outward(lo,5,False),outward(hi,5,True)]}


if __name__ == "__main__":
    print(json.dumps(replay(),indent=2))
