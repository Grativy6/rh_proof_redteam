"""Enclose a critical-line zero and its actual response to several square clocks.

Only integer interval arithmetic is used. The zero is isolated by Rouche's theorem;
the functional equation puts the unique simple zero on the critical line.
"""
from fractions import Fraction as Q
from math import factorial, isqrt, prod
import json

from check_pal_single_parent import Box, Interval, SCALE, ZERO, log_integer, exponential


def real(x):
    return Interval.enclose(Q(x))


def point(a, b=0):
    return Box(real(a), real(b))


def minus(x):
    return x.times_real(real(-1))


def inflate(z, eps):
    delta=Interval.enclose(-eps,eps)
    return Box(z.real+delta,z.imag+delta)


def absolute(v):
    a,b=v.lower,v.upper
    return Interval(0 if a<=0<=b else min(abs(a),abs(b)),max(abs(a),abs(b)))


def magnitude(z):
    a,b=absolute(z.real),absolute(z.imag)
    lo=isqrt(a.lower**2+b.lower**2)
    square=a.upper**2+b.upper**2
    hi=isqrt(square)
    return Interval(lo,hi+(hi*hi!=square))


def positive_ratio(a,b):
    assert a.lower>=0 and b.lower>0
    return Interval.enclose(Q(a.lower,b.upper),Q(a.upper,b.lower))


def zeta_at(x,y):
    # Valid both near 1/2+14i and at 1/2 on the real axis for the indicated calls.
    s=point(x,y)
    n=64
    value=point(0)
    for j in range(1,n):
        value+=exponential(minus(s).times_real(log_integer(j)))
    denom=(x-1)**2+y*y
    inv=point((x-1)/denom,-y/denom)
    last=exponential(minus(s).times_real(log_integer(n)))
    value+=last*(inv.times_real(real(n))+point(Q(1,2)))
    bernoulli=(Q(1,6),Q(-1,30),Q(1,42),Q(-1,30),Q(5,66),Q(-691,2730))
    # Form the rising factor divided by n at every step, avoiding wide intermediate intervals.
    rising=point(1)
    for j in range(11):
        rising=rising*(s+point(j)).times_real(real(Q(1,n)))
        if j%2==0:
            k=j//2+1
            value+=last*rising.times_real(real(bernoulli[k-1]/factorial(2*k)))
    # |s+j|<15+j, sigma>0 and sup |B12|/12! <= 4/6^12.
    error=Q(4*prod(range(15,27)),6**12*11*n**11)
    return inflate(value,error)


def active_prime():
    from check_pal_growth_windows import sieve
    p=3727
    tick=p*p+1
    mu,_,_=sieve(tick)
    scale=10**20
    low=width=0
    for n in range(1,tick+1):
        if n%6 in (1,5) and mu[n]:
            value=scale*mu[n]*min(tick,2*(tick-n))
            d,r=divmod(value,tick*n)
            low+=d
            width+=bool(r)
    lower,upper=Q(low,scale),Q(low+width,scale)
    correction=Q(2,p*tick)
    assert upper+correction < -Q(5,10**7)
    return {"prime":p,"physical_side":tick//2,"direct_rough_rows":tick,
            "raw":[str(lower),str(upper)],"genuine_shifted_input":str(Q(tick,2*p*p)),
            "positive_shifted_contribution":str(correction),
            "single_clock":[str(lower+correction),str(upper+correction)]}


def audit():
    center=Q(1413472514,10**8)
    delta=Q(1,10**6)
    radius=Q(1,10**7)
    x=Q(1,2)
    value=zeta_at(x,center)
    # |zeta|<100 on the radius-1/4 disk. Each of the first 63 terms has norm <=1;
    # the endpoint costs <6. The six Bernoulli corrections and the remainder cost <1.
    assert sum(Q(4,6**(2*k))*Q(26,64)**(2*k-1) for k in range(1,7))+Q(4*prod(range(15,27)),6**12*11*64**11)<1
    second=Q(2*100)*8**2
    diff=(zeta_at(x+delta,center)+minus(zeta_at(x-delta,center))).times_real(real(1/(2*delta)))
    # Central difference error from the second derivative on the real segment.
    derivative=inflate(diff,second*delta/2)
    der=magnitude(derivative)
    size=magnitude(value)
    lower_der=Q(der.lower,SCALE)
    assert Q(size.upper,SCALE)+second*radius**2/2<lower_der*radius
    at_zero=Interval.enclose(max(0,lower_der-second*radius),Q(der.upper,SCALE)+second*radius)
    assert at_zero.lower>0

    s=Box(real(x),Interval.enclose(center-radius,center+radius))
    two=exponential(s.times_real(log_integer(2)))
    two_neg=exponential(minus(s).times_real(log_integer(2)))
    three_neg=exponential(minus(s).times_real(log_integer(3)))
    denominator=s*(s+point(-1))*(point(1)+minus(two_neg))*(point(1)+minus(three_neg))
    residue=positive_ratio(magnitude(two+point(-1)),magnitude(denominator)*at_zero)
    sqtwo=exponential(point(x).times_real(log_integer(2))).real
    p2=exponential(point(-x).times_real(log_integer(2))).real
    p3=exponential(point(-x).times_real(log_integer(3))).real
    half=zeta_at(x,Q(0)).real
    assert half.upper<0
    dc=positive_ratio(sqtwo-real(1),real(Q(1,4))*(real(1)-p2)*(real(1)-p3)*(-half))
    assert 9*SCALE<dc.lower and dc.upper<10*SCALE and residue.lower>0
    data=[]
    for p in (2,3,577,2663,3727,4657,22063):
        assert all(p%j for j in range(2,isqrt(p)+1))
        h=real(2)*log_integer(p)
        phase=exponential(Box(ZERO,-s.imag).times_real(h))
        distance=magnitude(point(1)+minus(phase))
        amp=positive_ratio(residue,distance)
        mean=positive_ratio(dc,h)
        lower_limit=mean-amp
        upper_limit=mean+amp
        data.append({"prime":p,"phase_chord":distance.endpoints(),"real_pole":mean.endpoints(),
                     "oscillatory_residue":amp.endpoints(),
                     "upper_bound_for_liminf":str(Q(lower_limit.upper,SCALE)),
                     "lower_bound_for_limsup":str(Q(upper_limit.lower,SCALE))})
    assert all(Q(d["upper_bound_for_liminf"]) < -Q(1,10) for d in data if d["prime"] in (3727,4657,22063))
    return {"zero_center_imaginary":str(center),"radius":str(radius),"zeta_at_center_norm_upper":str(Q(size.upper,SCALE)),
            "derivative_at_center_norm":der.endpoints(),"derivative_at_zero_norm":at_zero.endpoints(),
            "seed_residue_norm":residue.endpoints(),"seed_transform_at_zero":dc.endpoints(),"clocks":data,"physical_witness":active_prime()}


if __name__=="__main__":
    print(json.dumps(audit(),indent=2))
