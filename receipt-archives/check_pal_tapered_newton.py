"""Rebuild the rational balanced Newton sides and enclose their true physical costs."""
from fractions import Fraction as Q
from math import gcd, lcm
import json
from check_pal_growth_windows import sieve


def taper(h,n):
    if n<=h:
        return Q(1)
    return Q(max(2*h-n,0),h)


def balance(h,f):
    assert h>0 and len(f)>=2*h+1
    price=sum(taper(h,n)*f[n]/n for n in range(1,2*h+1))
    a=[Q(0)]+[taper(h,n)*f[n]-(Q(n,h)*price if n>h else 0) for n in range(1,2*h+1)]
    assert a[1:h+1]==list(f[1:h+1])
    assert sum(a[n]/n for n in range(1,2*h+1))==0
    return a,price


def integer_side(a):
    den=lcm(*(v.denominator for v in a))
    return [int(v*den) for v in a],den


def update(left,right,stop):
    # All operations are exact integer convolutions, with common denominators.
    a,D=integer_side(left); b,E=integer_side(right)
    paired=[0]*(stop+1)
    for i in range(1,len(a)):
        if a[i]:
            for j in range(1,min(len(b)-1,stop//i)+1):
                paired[i*j]+=a[i]*b[j]
    observed=[0]*(stop+1)
    for d in range(1,stop+1):
        val=paired[d]
        if val:
            for r in (1,5):
                for n in range(r*d,stop+1,6*d):
                    observed[n]+=val
    for n in range(1,stop+1):
        observed[n]=(a[n]*E if n<len(a) else 0)+(b[n]*D if n<len(b) else 0)-observed[n]
    return observed,D*E


def prefix_and_tail(h,a):
    # Physical F is the sum of rough census readings. Exact zero reciprocal
    # slope permits the uniform envelope |1-F| <= 1+(2/3)*sum|a_d|.
    last=max(50000,4096*h)
    nums,den=integer_side(a)
    scale=10**13
    coordinate_scale=10**8
    chunk=32768
    read=lo=hi=0
    square_bounds=None
    for first in range(1,last+1,chunk):
        size=min(chunk,last-first+1)
        jumps=[0]*size
        for d in range(1,len(nums)):
            if nums[d]:
                step=6*d
                for residue in (d,5*d):
                    for offset in range((residue-first)%step,size,step):
                        jumps[offset]+=nums[d]
        for offset,val in enumerate(jumps):
            k=first+offset
            read+=val
            if k<=h:
                assert read==den
            if k in (h+1,2*h,last):
                direct=sum(nums[d]*(k//d-k//(2*d)-k//(3*d)+k//(6*d)) for d in range(1,len(nums)))
                assert read==direct
            lower=coordinate_scale*(den-read)//den
            upper=lower+1
            min_abs=min(abs(lower),abs(upper)) if lower*upper>0 else 0
            max_abs=max(abs(lower),abs(upper))
            divisor=coordinate_scale**2*k*(k+1)
            lo+=scale*min_abs**2//divisor
            hi+=-(-scale*max_abs**2//divisor)
            if k==h*h:
                square_bounds=(Q(lo,scale),Q(hi,scale))
    allowance=(1+Q(2,3)*sum(abs(v) for v in a))**2/(last+1)
    low=Q(lo,scale); high=Q(hi,scale)+allowance
    def rounded(x,up):
        t=x*100000
        return str(Q(-(-t//1) if up else t//1,100000))
    assert square_bounds is not None
    return {'side':h,'maximum_modulus':12*h,'rows_in_head_sum':last,
            'through_side_squared':[rounded(square_bounds[0],False),rounded(square_bounds[1],True)],
            'lower':rounded(low,False),
            'upper':rounded(high,True),'tail_allowance_upper':rounded(allowance,True)}


def negative_first_product():
    """Bound the true slope at one specified side using integer arithmetic."""
    h=6_600_000
    scale=10**17
    mu,_,_=sieve(2*h)
    lo=rounded_terms=0
    for r in (1,5):
        for n in range(r,2*h+1,6):
            if not mu[n]:
                continue
            numerator=scale*(h if n<=h else 2*h-n)*mu[n]
            q,rem=divmod(numerator,h*n)
            lo+=q
            rounded_terms+=bool(rem)
    slope_lo,slope_hi=Q(lo,scale),Q(lo+rounded_terms,scale)
    assert slope_hi < -Q(1,h+1)
    first=mu[h+1] if gcd(h+1,6)==1 else 0
    gap=lambda price:(first+(h+1)*price)/h
    # At the length-four side this difference is 43/56.
    small=Q(43,56)
    interval=[small*gap(slope_lo),small*gap(slope_hi)]
    assert interval[1]<0
    return {'large_side':h,'small_side':4,'scale':scale,'outward_roundings':rounded_terms,
            'slope_bounds':[str(slope_lo),str(slope_hi)],'mu6_at_first_unpaid':first,
            'small_side_first_gap':str(small),'first_mixed_product':5*(h+1),
            'first_mixed_gap_bounds':[str(x) for x in interval]}


def audit():
    sizes=(4,8,32,512)
    last=131072
    raw,_,_=sieve(2*last+2)
    true=[v if gcd(k,6)==1 else 0 for k,v in enumerate(raw)]
    sides={h:balance(h,true) for h in (4,5,7,8,10,13,32,512)}
    updates=[]
    for left,right,out in ((4,4,8),(8,8,32),(5,10,32),(4,13,32),(32,32,512),(512,512,last)):
        aa,_=sides[left];bb,_=sides[right]
        stop=2*out
        vec,den=update(aa,bb,stop)
        assert all(vec[k]==den*true[k] for k in range(1,stop+1))
        if out in sides:
            renewed,_=balance(out,[Q(v,den) for v in vec])
            assert renewed==sides[out][0]
        updates.append({'old_heads':[left,right],'renewed_head':out,'raw_coefficients_compared':stop})
    beyond=[]
    for h,j in ((4,4),(5,10),(8,8)):
        n=(h+1)*(j+1)
        a,_=sides[h];b,_=sides[j]
        vec,den=update(a,b,n)
        assert all(vec[k]==den*true[k] for k in range(1,n))
        gap=Q(true[n])-Q(vec[n],den)
        expected=(true[h+1]-a[h+1])*(true[j+1]-b[j+1])
        assert gap==expected
        beyond.append({'old_heads':[h,j],'first_possible_row':n,'unpaid':str(gap)})
    costs=[prefix_and_tail(h,sides[h][0]) for h in sizes]
    for prev,nxt in zip(costs,costs[1:]):
        assert Q(nxt['upper'])<Q(prev['lower'])
    assert Q(costs[1]['upper'])<1 and all(max(abs(x) for x in a)<=2 for a,_ in sides.values())
    return {'pure_integer_handoffs':updates,'first_possible_unpaid':beyond,'all_row_squared_errors':costs,
            'seed_slope':str(sides[4][1]),'opposite_directions':negative_first_product(),'physical_control':'each late row included through the explicit envelope'}


if __name__=='__main__':
    print(json.dumps(audit(),indent=2))
