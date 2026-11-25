"""Compare the hard matrix and the twice-averaged matrix on exactly the same inputs."""
from bisect import bisect_right
from fractions import Fraction as Q
from math import gcd
import json

from check_pal_growth_windows import sieve
from check_pal_boundary_packets import make_packets
from check_pal_single_parent import Interval, Box, ZERO, exponential


def period_sums(q):
    out=[0,0,0]
    for residue in (1,5):
        k=(q-residue)//6+1 if q>=residue else 0
        j=k*(k-1)//2
        jj=k*(k-1)*(2*k-1)//6
        out[0]+=k
        out[1]+=residue*k+6*j
        out[2]+=residue**2*k+12*residue*j+36*jj
    return out


def bernoulli_three(fract):
    return fract**3-Q(3,2)*fract**2+fract/2


def verify_entry(x, product):
    t=Q(x,product)
    n,s,ss=period_sums(x//product)
    c=Q(x*x*n-2*x*product*s+product**2*ss,x*x)
    cubic=sum(sign*d*d*bernoulli_three(t/d-(t/d)//1) for d,sign in ((1,1),(2,-1),(3,-1),(6,1)))
    assert c==t/9+1/(3*t)-cubic/(3*t*t)


def rough_form(side, x, active):
    value=0
    for i,a in active:
        for j,b in active:
            d=i*j
            n,s,ss=period_sums(x//d)
            value+=a*b*(x*x*n-2*x*d*s+d*d*ss)
    return value


def enclosed(v, scale=10**6):
    return [str(Q(v*scale//1,scale)),str(Q(-(-v*scale//1),scale))]


def genuine(side,mu):
    x=side*side
    active=[(i,mu[i]) for i in range(1,side+1) if gcd(i,6)==1 and mu[i]]
    raw=2*sum(a for _,a in active)-sum(mu[k] for k in range(1,x+1) if gcd(k,6)==1)
    soft=rough_form(side,x,active)
    plus=rough_form(side,x+1,active)
    minus=rough_form(side,x-1,active)
    assert plus-2*soft+minus==2*raw
    actual=sum(mu[k]*(x-k)**2 for k in range(1,x+1) if gcd(k,6)==1)
    side_read=sum(a*(x-i)**2 for i,a in active)
    assert actual==2*side_read-soft
    harmonic=sum((Q(a,i) for i,a in active),Q(0))
    centered=Q(soft,x*x)-Q(x,9)*harmonic**2
    jordan=Q(sum(i*a for i,a in active)**2,3*x)
    return {'side':side,'raw_integer_form':raw,'second_threshold_difference':plus-2*soft+minus,
            'smoothed_true_sum':enclosed(Q(actual,x*x)), 'smoothed_centered_form':enclosed(centered),
            'remaining_cubic_form':enclosed(centered-jordan)}


def alternative(side, mu):
    _,a,packets=make_packets(side,mu)
    x=side**2
    sites=sorted(a)
    assert x//sites[0]**2<7 and x//sites[-1]**2>=1
    sums=[[0] for _ in range(3)]
    for i in sites:
        for j in range(3):
            sums[j].append(sums[j][-1]+a[i]*i**j)
    total=0
    for i in sites:
        for rough in (1,5):
            d=i*rough
            stop=bisect_right(sites,x//d)
            total+=a[i]*(x*x*sums[0][stop]-2*x*d*sums[1][stop]+d*d*sums[2][stop])
    # Bound the rank-one reciprocal reading in exact integer units.
    scale=10**18
    lo=sum(scale*a[i]//i for i in sites)
    hi=lo+len(sites)
    min_abs=min(abs(lo),abs(hi)) if lo*hi>0 else 0
    max_abs=max(abs(lo),abs(hi))
    low=Q(total,x*x)-Q(x*max_abs**2,9*scale**2)
    high=Q(total,x*x)-Q(x*min_abs**2,9*scale**2)
    return {'side':side,'selected_sites':len(sites),'hard_uncentered':-2*sum(m*m for m in packets),
            'twice_averaged_uncentered':enclosed(Q(total,x*x)),
            'twice_averaged_centered':[enclosed(low)[0],enclosed(high)[1]]}


def pi_enclosure():
    def atan_inv(q):
        x=Q(1,q)
        partial=sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(24))
        next_term=x**49/49
        return Interval.enclose(partial,partial+next_term)
    return Interval.enclose(16)*atan_inv(5)-Interval.enclose(4)*atan_inv(239)


def gaussian_control(t):
    pi=pi_enclosure()
    def evaluate(q):
        if 3*q>=72:
            return Interval.enclose(0,Q(1,2**72))
        return exponential(Box((-pi)*Interval.enclose(q),ZERO)).real
    def cutoff(lower):
        n=0
        while lower*(n+1)**2<70 or lower*(2*n+3)<1:
            n+=1
        return n
    n=cutoff(3/t**2)
    m=cutoff(3*t**2/36)
    tail=Q(1,2**69)
    direct=Interval.enclose(0,tail)
    for i in range(1,n+1):
        if gcd(i,6)==1:
            direct=direct+evaluate(Q(i*i)/t**2)
    phases=(2,1,-1,-2,-1,1)
    dual=Interval.enclose(1-2*tail,1+2*tail)
    for k in range(1,m+1):
        dual=dual+Interval.enclose(phases[k%6])*evaluate(k*k*t*t/36)
    dual=Interval.enclose(t/6)*dual
    assert max(direct.lower,dual.lower)<=min(direct.upper,dual.upper)
    assert max(direct.upper-direct.lower,dual.upper-dual.lower)<10**5
    return {'t':str(t),'direct':direct.endpoints(),'dual':dual.endpoints(),
            'direct_max':n,'dual_max':m}


def audit():
    for x in (1,2,6,30,121,961,1085,1024**2):
        for d in (1,3,5,6,11,35,97,499,1048575):
            verify_entry(x,d)
    mu,_,_=sieve(4194304)
    return {'true_arithmetic':[genuine(h,mu) for h in (5,30,35,128,512,1024)],
            'alternative_same_inputs':[alternative(h,mu) for h in (262144,1048576,4194304)],
            'gaussian_residue_comparison':[gaussian_control(t) for t in (Q(1,2),Q(1),Q(2),Q(6),Q(24))]}


if __name__=='__main__':
    print(json.dumps(audit(),indent=2))
