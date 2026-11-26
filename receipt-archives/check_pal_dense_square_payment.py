"""Price the rough-square completion on the same integer labels at every head."""
import argparse
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, gcd, isqrt
from pathlib import Path
import json
from check_pal_reference_prices import physical
from check_pal_prime_transport import outward
from check_pal_rise_direction import box, mul, add, flip, divide, sqrt_box
from check_pal_single_parent import log_integer, SCALE


def sub(a,b):
    return add(a,flip(b))


def ln_int(n):
    v=log_integer(n)
    return Q(v.lower,SCALE),Q(v.upper,SCALE)


def ln(x):
    x=Q(x)
    return sub(ln_int(x.numerator),ln_int(x.denominator))


def display(a,places=8):
    return [outward(a[0],places,False),outward(a[1],places,True)]


@lru_cache(maxsize=1)
def c_limit():
    # Alternating eta at 1/2, using its Euler transform and positive differences.
    eta=box(0)
    for m in range(78):
        row=box(0)
        for h in range(m+1):
            row=add(row,mul(box((-1)**h*comb(m,h)),divide(box(1),sqrt_box(h+1))))
        eta=add(eta,mul(box(Q(1,2**(m+1))),row))
    eta=eta[0],eta[1]+Q(1,2**78)
    return divide(eta,mul(box(2),sub(sqrt_box(2),box(1))))


@lru_cache(maxsize=4096)
def integrated_reader(square):
    """F(sqrt(square)), from its finite sum of logs and inverse roots."""
    square=Q(square)
    if square<=1:
        return box(0)
    n=square.numerator//square.denominator
    total=box(0)
    for k in range(1,n+1):
        ratio=square/k
        total=add(total,mul(box(Q(1,2)),sub(add(ln(ratio),box(1)),sqrt_box(ratio))))
    return total


def continuous_count(square,p=3):
    return mul(divide(box(Q(2*p,3)),c_limit()),
               sub(integrated_reader(Q(square,p*p)),integrated_reader(Q(square,4*p*p))))


def count_squares(z):
    return z-z//2-z//3+z//6


def g_at_square(x):
    x=Q(x)
    return count_squares(isqrt(x.numerator//x.denominator))


def finite_profile():
    c=c_limit()
    assert Q(73,100)<c[0]<=c[1]<Q(731,1000)
    assert sqrt_box(2)[1]-Q(1,2)<1
    # k(5-) is a lower bound on k(v) for v >= 4 by the increasing cell infima.
    inv=sum_intervals(divide(box(1),sqrt_box(k)) for k in range(1,5))
    lower=sub(divide(box(4),sqrt_box(5)),mul(box(Q(1,2)),inv))
    assert lower[0]>Q(3,8)
    shift=divide(ln(2),c)
    # Beyond z=48 the integral remainder is no more than 36/(c*z^2).
    error=Q(36,48**2)/c[0]
    assert shift[0]-error-Q(2,3)>Q(1,4) and shift[1]+error+Q(2,3)<Q(5,3)
    ends=[]
    for z in [r for r in range(1,49) if gcd(r,6)==1]+[48]:
        g=g_at_square(z*z)
        cc=continuous_count(z*z)
        if gcd(z,6)==1:
            assert cc[1]<=g-1 and cc[0]>g-Q(5,3)
            if z>1:assert g-1-cc[1]>Q(1,4)
        else:
            assert g-Q(5,3)<cc[0]<=cc[1]<g-Q(1,4)
        ends.append({"root":z,"integer_count":g,"continuous_count":display(cc)})
    bad={}
    for p in [1,2]:
        # Right before the ordinary rough root 5 the offer is only label 1.
        cc=continuous_count(25,p)
        assert cc[0]>1
        bad[str(p)]=display(cc)
    return {"reader_limit":display(c,12),"lower_for_reader_on_v_ge_4":display(lower),
            "asymptotic_deficit":display(shift),"small_endpoints":ends,
            "failed_dilations_at_five_from_below":bad}


def sum_intervals(xs):
    s=box(0)
    for x in xs:
        s=add(s,x)
    return s


def D(t,physical=True):
    """Exact known source for a, evaluated as outward intervals."""
    t=Q(t)
    if t<1:
        return box(0)
    root=sqrt_box(t)
    # Only log(t) depends on the head. Every smooth log(q) is i*log(2)+j*log(3).
    logt=ln(t); log2=ln(2); log3=ln(3)
    sums=box(0)
    two,i=1,0
    while two<=t:
        q,j=two,0
        while q<=t:
            weight=(2**(i//2+1)-1)*(3**(j//2+1)-1)//2 if physical else 1
            logq=add(mul(box(i),log2),mul(box(j),log3))
            cost=sub(divide(add(box(1),sub(logt,logq)),root),divide(box(1),sqrt_box(q)))
            sums=add(sums,mul(box(weight),cost))
            q*=3
            j+=1
        two*=2
        i+=1
    return sums


def paid(T,physical=True):
    return mul(divide(sqrt_box(T),mul(box(3),c_limit())),
               sub(D(Q(T,9),physical),mul(box(Q(1,2)),D(Q(T,36),physical))))


def ordinary_controls():
    trials=[]
    # Convolution with all ordinary rough squares. Every physical sign is fixed
    # by the parity of the rough prime multiplicities.
    for T in [1,6,24,25,44,45,49,65,128,245,343,577,2663]:
        source=box(0);rem=box(0);whole=0;two=None
        for n in range(1,T+1):
            a=physical(n)
            if not a:
                continue
            square=Q(T,n)
            g=g_at_square(square)
            cc=continuous_count(square)
            source=add(source,mul(box(a),cc))
            residue=sub(box(g),cc)
            assert residue[0]>=0 and residue[1]<2
            rem=add(rem,mul(box(a),residue))
            whole+=a*g
            if residue[0]>1 and two is None:
                two=n
        analytic=paid(T)
        assert max(source[0],analytic[0])<=min(source[1],analytic[1])
        assert rem[0]<=whole-analytic[0] and whole-analytic[1]<=rem[1]
        trials.append({"head":T,"full_count":whole,"paid":display(analytic),
                       "unspent":display(sub(box(whole),analytic)),"two_roots_witness_label":two})
    return trials


def large_values(file):
    data=json.loads(file.read_bytes())
    if isinstance(data,dict):
        data=data["native_counts"]
    assert data and len(data)%2==0
    results={}
    for m,l in zip(data[::2],data[1::2]):
        assert m["rows"]==l["rows"] and m["mode"]=="mobius" and l["mode"]=="liouville"
        for _,t,old,new,raw,raw_filled,ordinary in m["rows"]:
            if str(t) in results:continue
            accounted=paid(t)
            R=sub(box(new),accounted)
            results[str(t)]={"old_physical":old,"completed_physical":new,"rough_mobius":raw,
                             "rough_liouville":raw_filled,"ordinary_liouville":ordinary,"paid":display(accounted,6),
                             "unspent":display(R,6)}
    return results


def sharpen():
    p=Q(17,8)
    z0=96
    shift=divide(mul(box(p/3),ln(2)),c_limit())
    error=Q(4,3)*p**3/(c_limit()[0]*z0**2)
    assert shift[0]-error>Q(2,3) and shift[1]+error+Q(2,3)<Q(27,20)
    least=Q(1)
    greatest=Q(0)
    for z in [r for r in range(1,z0+1) if gcd(r,6)==1]+[z0]:
        n=g_at_square(z*z)
        cc=continuous_count(z*z,p)
        if gcd(z,6)==1:
            assert cc[1]<=n-1
            if z>1:least=min(least,n-1-cc[1])
        else:
            assert cc[1]<=n
        greatest=max(greatest,n-cc[0])
    assert greatest<Q(27,20) and least>0
    return {"dilation":str(p),"tail_starts":z0,"limiting_deficit":display(shift),
            "largest_small_right_deficit_upper":outward(greatest,8,True),
            "small_left_deficit_lower_after_first":outward(least,8,False),
            "uniform_residual_upper":"27/20","universal_lower_for_uniform_upper":"4/3"}


def arctan_inverse(n):
    x=Q(1,n)
    s=sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(32))
    return s,s+x**65/65


def secondary_coefficient():
    pi=sub(mul(box(16),arctan_inverse(5)),mul(box(4),arctan_inverse(239)))
    N=10000
    unit=2**96
    h=sum(unit//j for j in range(1,N+1))
    gamma=sub(sub((Q(h,unit),Q(h+N,unit)),ln(N)),(Q(1,2*(N+1)),Q(1,2*N)))
    log8pi=ln_int(8)
    # log(pi) by scaling pi/2 into [1,2], and rounding its inputs out to 12 decimals.
    at=10**12
    pl=Q(pi[0]*at//1,at); ph=Q(-(-pi[1]*at//1),at)
    log8pi=add(log8pi,(ln(pl)[0],ln(ph)[1]))
    zeta_ratio=mul(box(Q(1,2)),add(add(log8pi,gamma),mul(box(Q(1,2)),pi)))
    J=add(mul(box(Q(1,3)),add(gamma,mul(box(Q(3,2)),ln(3)))),
          mul(box(Q(1,6)),sub(box(4),zeta_ratio)))
    smooth=mul(sub(box(1),divide(box(1),sqrt_box(2))),sub(box(1),divide(box(1),sqrt_box(3))))
    denom=mul(c_limit(),mul(smooth,mul(box(4),mul(ln(2),ln(3)))))
    return {"residual_mellin_mass":display(J,8),"leading_paid_per_root_log_squared":display(flip(divide(box(1),mul(box(12),denom))),8),
            "second_paid_per_root_log":display(flip(divide(J,denom)),8)}


def residual_row_prices(K,heads):
    from array import array
    # Liouville is completely multiplicative. Its sign changes at every prime power.
    li=array("b",[1])*(K+1); primes=bytearray(b'\1')*(K+1)
    for p in range(2,K+1):
        if not primes[p]:continue
        if p*p<=K:primes[p*p::p]=b'\0'*len(primes[p*p::p])
        power=p
        while power<=K:
            for n in range(power,K+1,power):li[n]=-li[n]
            power*=p
    mass=array("i",[0])
    root=[0];S=2**72
    for n in range(1,K+1):
        mass.append(mass[-1]+(li[n] if n%2 and n%3 else 0))
        root.append(root[-1]+isqrt(S*S//n))
    results=[]
    for T in heads:
        total=box(0);rows=0
        for v,v2 in scales_local(T):
            y=Q(T,v2)
            if y>K:continue
            subpaid=paid(y,physical=False)
            rho=sub(box(mass[int(y)]),subpaid)
            x=Q(K,y);n=int(x)
            read=sub(divide(box(n),sqrt_box(x)),(Q(root[n],2*S),Q(root[n]+n,2*S)))
            keep=divide(read,c_limit())
            keep=max(Q(0),keep[0]),min(Q(1),keep[1])
            assert keep[0]<=keep[1]
            total=add(total,mul(box(v),mul(rho,keep)));rows+=1
        results.append({"head":T,"cutoff":K,"smooth_rows":rows,"secondary_signed_price":display(total,6)})
    return results


def scales_local(T):
    two=1
    while two*two<=T:
        v=two
        while v*v<=T:
            yield v,v*v
            v*=3
        two*=2


def negative_prefix(high=500000):
    # Generate a by its unique smooth square and rough squarefree cofactor.
    from array import array
    from check_pal_growth_windows import sieve
    ordinary,_,_=sieve(high)
    orig=array("i",[0])*(high+1)
    for v,v2 in scales_local(high):
        for d in range(1,high//v2+1):
            if d%2 and d%3:
                orig[v2*d]=v*ordinary[d]
    extended=array("i",[0])*(high+1)
    for r in range(1,isqrt(high)+1):
        if gcd(r,6)!=1:continue
        r2=r*r
        for n in range(1,high//r2+1):
            extended[r2*n]+=orig[n]
    summed=0; last_pos=last_non=0
    for n in range(1,high+1):
        summed+=extended[n]
        if summed>=0:last_non=n
        if summed>0:last_pos=n
    a=b=0; reciprocal=box(0);cut=1000
    for n in range(1,cut+1):
        a+=orig[n]; b+=abs(orig[n])
        reciprocal=add(reciprocal,divide(box(orig[n]),sqrt_box(n)))
    coeff=mul(box(Q(1,3)),sub(reciprocal,divide(box(a),sqrt_box(cut+1))))
    error=Q(2,3)*(b+abs(a))
    assert coeff[1]<0 and add(mul(coeff,sqrt_box(high)),box(error))[1]<0
    assert last_pos==43 and last_non==44
    return {"direct_through":high,"last_positive":last_pos,"last_nonnegative":last_non,
            "terminal_rough_argument":cut,"terminal_coefficient":display(coeff),
            "terminal_rounding_allowance":str(error),"full_count_at_direct_limit":summed}


def direct_residual_integral(Z=72):
    # Integrate the original residual over [1,Z]. The interval for the tail uses
    # the proven pointwise capacity. This check uses no derivative of zeta.
    H=sum(Q(1,r) for r in range(1,Z+1) if gcd(r,6)==1)
    rem=sub(box(count_squares(Z)),continuous_count(Z*Z))
    def log_primitive(R):
        v=Q(R)**2
        if v<=1:return box(0)
        hi=v.numerator//v.denominator
        inv=divide(box(1),sqrt_box(v))
        total=box(0)
        for n in range(1,hi+1):
            term=sub(mul(box(2),sub(divide(box(1),sqrt_box(n)),inv)),
                     divide(ln(v/n),mul(box(2),sqrt_box(n))))
            total=add(total,term)
        return mul(box(Q(1,2)),total)
    derivative=divide(sub(mul(box(2),log_primitive(Q(Z,3))),log_primitive(Q(Z,6))),mul(box(3),c_limit()))
    first=sub(sub(box(H),mul(box(Q(1,Z)),rem)),derivative)
    total=add(first,(Q(1,4*Z),Q(5,3*Z)))
    precise=secondary_coefficient()["residual_mellin_mass"]
    assert max(total[0],Q(precise[0]))<=min(total[1],Q(precise[1]))
    return {"integrated_to":Z,"direct_integral_plus_bounded_tail":display(total)}


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--counts",type=Path,help="Paired quotient count outputs in the record format")
    args=cli.parse_args()
    out={"profile":finite_profile(),"small":ordinary_controls(),"sharper":sharpen(),"coefficients":secondary_coefficient(),
         "negative_prefix":negative_prefix(),"direct_integral":direct_residual_integral(),
         "secondary":[row for K in [10000,1000000] for row in residual_row_prices(K,[200000000,906150257,10**10,10**12,2*10**12,10**13])]}
    if args.counts:out["large"]=large_values(args.counts)
    print(json.dumps(out,indent=2))
