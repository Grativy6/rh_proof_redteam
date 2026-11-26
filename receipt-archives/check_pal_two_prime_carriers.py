"""Spend the whole ordinary PAL block except fractions of q and 5*q."""
from fractions import Fraction as Q
import json
from math import comb, isqrt
from check_pal_prime_transport import SCALE, inverse, outward, transport_enclosure


def small_primes(limit):
    prime = bytearray(b'\1')*(limit+1)
    prime[:2] = b'\0\0'
    for p in range(2,isqrt(limit)+1):
        if prime[p]:
            prime[p*p::p] = b'\0'*len(prime[p*p::p])
    return [p for p in range(2,limit+1) if prime[p]]


def rough_labels(lo,hi,primes):
    """Yield the squarefree rough integers, sign and number of prime factors."""
    if hi < lo:
        return
    rem = list(range(lo,hi+1))
    factors = bytearray(len(rem))
    active = bytearray(b'\1')*len(rem)
    for p in primes:
        if p*p > hi:
            break
        for n in range(((lo+p-1)//p)*p,hi+1,p):
            i = n-lo
            if not active[i]:
                continue
            if p <= 3 or n % (p*p) == 0:
                active[i] = 0
            else:
                rem[i] //= p
                factors[i] += 1
    for i,v in enumerate(rem):
        n = lo+i
        if active[i] and n%2 and n%3:
            k = factors[i]+(v>1)
            yield n,(-1 if k%2 else 1),k


def trial_mark(n):
    sign,root = 1,1
    for p in (2,3):
        while n%(p*p)==0:
            n //= p*p
            root *= p
        if n%p==0:
            return 0
    d = 5
    while d*d<=n:
        if n%d==0:
            n //= d
            if n%d==0:
                return 0
            sign = -sign
        d += 2
    return root*(-sign if n>1 else sign)


def uniform_fraction_obstruction(lo,hi):
    """Necessary bounds on delta from the five rows of the midpoint inverse."""
    def interval(z, low, high):
        return (sum(a*(x if a>=0 else y) for a,x,y in zip(z,low,high)),
                sum(a*(y if a>=0 else x) for a,x,y in zip(z,low,high)))
    P = [[Q(a+b,2) for a,b in zip(l[:5],h[:5])] for l,h in zip(lo,hi)]
    left,right = Q(0),Q(1)
    for z in inverse(P):
        cols = [interval(z,[r[k] for r in lo],[r[k] for r in hi]) for k in range(7)]
        minimum = sum(min(0,col[0]) for col in cols[:5])
        maximum = sum(max(0,col[1]) for col in cols[:5])
        u,b = cols[5:]
        # delta*u - b must lie between the two attainable prime-column bounds.
        for slope,cap in [(u[0],b[1]+maximum),(-u[1],-b[0]-minimum)]:
            if slope > 0:
                right = min(right,cap/slope)
            elif slope < 0:
                left = max(left,cap/slope)
            elif cap < 0:
                return {"empty":True,"constant_inequality_failed":True}
    return {"empty":left>right,"necessary_minimum_rounded_down":outward(left,7,False),
            "necessary_maximum_rounded_up":outward(right,7,True)}


def case(m):
    A,B = m**4,(m+1)**4
    width = B-A
    primes = small_primes(isqrt(B))
    lo,hi = [[0]*7 for _ in range(5)],[[0]*7 for _ in range(5)]
    counts = [0,0,0,0]
    direct = {} if m == 20 else None
    smooth = []
    a = 1
    while a*a<=B:
        v = a
        while v*v<=B:
            smooth.append(v)
            v *= 3
        a *= 2
    for v in smooth:
        for u,sign,k in rough_labels(A//(v*v)+1,B//(v*v),primes):
            n = v*v*u
            w = v*sign
            if direct is not None:
                assert n not in direct
                direct[n] = w
            counts[w<0] += abs(w)
            prime = v==1 and k==1
            five = v==1 and k==2 and u%5==0
            counts[2] += prime
            counts[3] += five
            group = (5*(n-A)-1)//width
            x,y = n-A,B-n
            den = n*width**4
            for i in range(5):
                num = SCALE*A*comb(4,i)*x**i*y**(4-i)
                lb,remainder = divmod(num,den)
                ub = lb+bool(remainder)
                if prime:
                    lo[i][group] += lb
                    hi[i][group] += ub
                if five:
                    lo[i][5] += lb
                    hi[i][5] += ub
                lo[i][6] += w*(lb if w>0 else ub)
                hi[i][6] += w*(ub if w>0 else lb)
    if direct is not None:
        assert all(direct.get(d,0)==trial_mark(d) for d in range(A+1,B+1))
    # b = delta*column(5q) - M(q)*x. Choose dyadic delta and prove strict capacity.
    attempts = []
    fractions = {Q(j,32) for j in range(33)} | {Q(1,2**n) for n in range(1,13)}
    for fraction in sorted(fractions):
        dl = [l[:5]+[fraction*l[5]-h[6]] for l,h in zip(lo,hi)]
        du = [h[:5]+[fraction*h[5]-l[6]] for l,h in zip(lo,hi)]
        try:
            solution = transport_enclosure(dl,du)
        except (ValueError,AssertionError,StopIteration):
            continue
        attempts.append((fraction,solution))
    if not attempts:
        obstruction = []
        for i in range(5):
            high = hi[i][5]
            low = -sum(hi[i][:5])
            if lo[i][6] > high or hi[i][6] < low:
                obstruction.append({"nonnegative_bernstein_index":i,"actual_moment_interval":[lo[i][6],hi[i][6]],
                                    "possible_range_using_either_support":[low,high],"denominator":SCALE})
        return {"m":m,"signed_mass":counts[0]-counts[1],"counts":counts,
                "bernstein_obstructions":obstruction,"uniform_fraction_necessary":uniform_fraction_obstruction(lo,hi), "tested_uniform_fractions":len(fractions),
                "status":"no_fraction_in_tested_uniform_grid_certified"}
    fraction,sol = attempts[0]
    # Since the constant is a tested moment, the total retained negative mass is
    # delta*#(5q) minus the full signed mass, without estimating any prime fraction.
    net = counts[0]-counts[1]
    plus = fraction*counts[3]
    minus = plus-net
    assert 0<minus<=counts[2] and 0<=plus<=counts[3]
    share = (plus+minus)/(counts[0]+counts[1])
    return {"m":m,"left_excluded":A,"right_included":B,"positive_marks":counts[0],
            "negative_marks":counts[1],"signed_mass":net,"primes":counts[2],"five_times_primes":counts[3],
            "uniform_positive_fraction":str(fraction),"negative_fraction_certificate":sol,
            "retained_absolute_mass":str(plus+minus),"whole_absolute_mass":counts[0]+counts[1],
            "retained_mass_fraction_interval":[outward(share,8,False),outward(share,8,True)],
            "direct_trial_all_labels":direct is not None,"tested_uniform_fractions":len(fractions),"tested_fractions_certified":len(attempts)}


if __name__ == "__main__":
    print(json.dumps({"cases":[case(m) for m in (20,40,64,100)]},indent=2))
