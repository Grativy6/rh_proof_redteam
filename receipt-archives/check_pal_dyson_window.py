"""Dyson's pair test, the doubling response and a finite prime-power calculation."""
import argparse
from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt
import json

from check_pal_dense_square_payment import arctan_inverse, display, ln, sub
from check_pal_prime_transport import outward
from check_pal_rise_direction import add, box, mul, divide, sqrt_box
from check_pal_single_parent import SCALE, log_ratio

ZERO=(0,0)


def ceil_div(a,b):
    return -(-a//b)


def plus(a,b):
    return a[0]+b[0],a[1]+b[1]


def minus(a,b):
    return a[0]-b[1],a[1]-b[0]


def times(a,b):
    vals=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]]
    return min(vals)//SCALE,ceil_div(max(vals),SCALE)


def natural(k,a):
    return k*a[0],k*a[1]


@lru_cache(maxsize=1025)
def table_bin(b):
    v=log_ratio(b,1024)
    return v.lower,v.upper


def log_int(n):
    """Binary reduction with a 1024-part table and alternating residual series."""
    e=n.bit_length()-1
    unit=1<<e
    b=1024*n//unit
    over=1024*n-b*unit
    den=b*unit
    r=(SCALE*over//den,ceil_div(SCALE*over,den))
    power=r
    result=r
    for k in range(2,6):
        power=times(power,r)
        term=power[0]//k,ceil_div(power[1],k)
        result=minus(result,term) if k%2==0 else plus(result,term)
    # The alternating remainder after the fifth term is negative, of size <= (1/1024)^6/6.
    result=result[0]-ceil_div(SCALE,6*1024**6),result[1]
    return plus(plus(natural(e,table_bin(2048)),table_bin(b)),result)


def inverse_root(n):
    a=isqrt(SCALE*SCALE//n)
    return a,a+(a*a*n<SCALE*SCALE)


def interval_text(a,places=8):
    return [outward(Q(a[0],SCALE),places,False),outward(Q(a[1],SCALE),places,True)]


def integer_box(a):
    return a[0]*SCALE//1,ceil_div(a[1].numerator*SCALE,a[1].denominator)


def prime_data(top):
    prime=bytearray(b"\1")*(top+1)
    prime[:2]=b"\0\0"
    for p in range(2,isqrt(top)+1):
        if prime[p]:
            prime[p*p::p]=b"\0"*len(prime[p*p::p])
    powers={}
    for p in range(2,isqrt(top)+1):
        if prime[p]:
            q=p*p;k=2
            while q<=top:
                powers[q]=(p,k)
                q*=p;k+=1
    return prime,powers


def direct_small(j):
    """Direct interval addition, with no prefix subtraction and a separate log calculation."""
    from check_pal_dense_square_payment import ln_int
    x=j*j
    prime,powers=prime_data(2*x)
    groups=[box(0),box(0),box(0)]
    for n in range(x//2+1,2*x):
        if not prime[n] and n not in powers:
            continue
        p,k=(n,1) if prime[n] else powers[n]
        w=ln(Q(2*n,x) if n<=x else Q(2*x,n))
        a=mul(divide(ln_int(p),sqrt_box(n)),w)
        group=min(k,3)-1
        groups[group]=add(groups[group],a)
    return [integer_box(g) for g in groups]


@lru_cache(maxsize=1)
def constants():
    from check_pal_dense_square_payment import ln_int
    pi=sub(mul(box(16),arctan_inverse(5)),mul(box(4),arctan_inverse(239)))
    den=2**96;n=10000
    harmonic=sum(den//k for k in range(1,n+1))
    gamma=sub(sub((Q(harmonic,den),Q(harmonic+n,den)),ln_int(n)),(Q(1,2*(n+1)),Q(1,2*n)))
    unit=10**11
    lo=Q(pi[0]*unit//1,unit)
    hi=Q(ceil_div(pi[1].numerator*unit,pi[1].denominator),unit)
    log4pi=ln(4*lo)[0],ln(4*hi)[1]
    zero_sum=sub(add(box(2),gamma),log4pi)
    L=ln_int(2)
    zero_allowance=mul(add(box(4),mul(box(Q(1,4)),mul(L,L))),zero_sum)
    # For x>=9 bound the positive trivial-zero correction by a geometric series.
    q=Q(2,9)
    tails=mul(box(q*q*Q(4,25)/(1-q*q)),sqrt_box(q))
    assert zero_allowance[1]+tails[1]<Q(1,5)
    main=mul(box(4),sub(add(sqrt_box(2),divide(box(1),sqrt_box(2))),box(2)))
    return integer_box(main),{"main_coefficient":display(main,12),
             "conditional_zero_allowance":display(zero_allowance,10),
             "trivial_zero_allowance_at_nine":display(tails,10),
             "limiting_square_contribution":display(mul(box(Q(1,2)),mul(L,L)),10)}


def scaled_div(a,b):
    if b[0]<=0:
        raise ValueError("positive denominator required")
    p=[Q(x*SCALE,y) for x in a for y in b]
    return min(p)//1,ceil_div(max(p).numerator,max(p).denominator)


def small_series(t,kind):
    """Exp, relative exponential, or sinh(t)/t on 0<=t<=1 with outward endpoints."""
    v=(SCALE,SCALE)
    total=v
    for k in range(1,25):
        v=times(v,t)
        denominator=k+1 if kind=="relative" else k
        v=v[0]//denominator,ceil_div(v[1],denominator)
        if kind!="sinh" or k%2==0:
            if kind=="sinh":
                term=v[0]//(k+1),ceil_div(v[1],k+1)
            else:
                term=v
            total=plus(total,term)
    # exp(1)/25! < one unit of the fixed-point scale.
    return total[0],total[1]+1


def diagonal(cells=32768):
    L=log_int(2);half=L[0]//2,ceil_div(L[1],2)
    coefficient,_=constants()
    n=10000;den=2**96
    harmonic=sum(den//k for k in range(1,n+1))
    from check_pal_dense_square_payment import ln_int
    gamma=sub(sub((Q(harmonic,den),Q(harmonic+n,den)),ln_int(n)),(Q(1,2*(n+1)),Q(1,2*n)))
    pi=sub(mul(box(16),arctan_inverse(5)),mul(box(4),arctan_inverse(239)))
    unit=10**11
    il=pi[0]*unit//1;ih=ceil_div(pi[1].numerator*unit,pi[1].denominator)
    param=integer_box(add(gamma,(ln(4*Q(il,unit))[0],ln(4*Q(ih,unit))[1])))
    constant=plus(minus(natural(2,coefficient),times(param,L)),times(L,log_int(3)))
    accumulated=ZERO
    before=None
    for i in range(cells+1):
        s=i*L[0]//cells,ceil_div(i*L[1],cells)
        sh=s[0]//2,ceil_div(s[1],2)
        # s/sinh(s) is decreasing. The bracket below is increasing.
        a=scaled_div((SCALE,SCALE),small_series(s,"sinh"))
        b=minus(small_series(sh,"exp"),times(half,small_series(sh,"relative")))
        if before is not None:
            pa,pb=before
            lower=times((a[0],a[0]),(pb[0],pb[0]))[0]
            upper=times((pa[1],pa[1]),(b[1],b[1]))[1]
            accumulated=plus(accumulated,(lower,upper))
        before=a,b
    area=times(L,(accumulated[0]//cells,ceil_div(accumulated[1],cells)))
    result=plus(constant,area)
    assert Q(result[0],SCALE)>Q(127,1000) and Q(result[1],SCALE)<Q(128,1000)
    return {"panels":cells,"spectral_diagonal":interval_text(result,9),
            "no_prime_terms_at_zero":True}


def prime_upper_calibration(last=99999):
    """Cover the finite part of the RH-implied prime-only sign using only small primes."""
    limit=isqrt(2*last*last)
    prime,_=prime_data(limit)
    # Prefix entries have a common directed integer scale.
    mass=[ZERO]; moment=[ZERO]
    for p in range(1,limit+1):
        x=mass[-1]; y=moment[-1]
        if prime[p]:
            lp=log_int(p)
            term=lp[0]//p,ceil_div(lp[1],p)
            x=plus(x,term)
            y=plus(y,times(term,lp))
        mass.append(x);moment.append(y)
    L=log_int(2); exceptional=[]; sharp=[]
    for j in range(2,last+1):
        lo=isqrt(j*j//2);hi=isqrt(2*j*j)
        center=natural(2,log_int(j))
        left=minus(natural(2,minus(moment[j],moment[lo])),times(minus(center,L),minus(mass[j],mass[lo])))
        right=minus(times(plus(center,L),minus(mass[hi],mass[j])),natural(2,minus(moment[hi],moment[j])))
        squares=plus(left,right)
        if 1000*squares[0]<=191*SCALE:
            # For every inconclusive square lower bound, evaluate the actual prime-only comparison.
            other=direct_small(j)[0]
            coefficient,_=constants()
            bare=minus(other,natural(j,coefficient))
            assert bare[1]<0
            exceptional.append([j,interval_text(squares),interval_text(bare)])
            if 1000*squares[0]<=128*SCALE and j<32768:
                sharp.append([j,interval_text(bare)])
    return {"last_root":last,"test_threshold":"191/1000","exceptional_squares_and_direct_prime_minus_main":exceptional,
            "diagonal_threshold":"128/1000","small_diagonal_exceptions_below_32768":sharp}


def narrow_aperture():
    # At the square 100 choose b=2 log(101/100). The only prime strictly inside is 101.
    q=Q(101,100)
    left,right=100/q**2,100*q**2
    assert left>98 and left<99 and right>102 and right<103
    primes,_=prime_data(102)
    assert [p for p in range(99,103) if primes[p]]==[101]
    from check_pal_dense_square_payment import ln_int
    reading=mul(divide(ln_int(101),sqrt_box(101)),ln(q))
    reference=Q(40)*(q+1/q-2)
    excess=sub(reading,box(reference))
    assert reference==Q(2,505) and excess[0]>0
    return {"head":100,"log_half_width":"2 ln(101/100)","only_prime":101,
            "reference":str(reference),"prime_only_minus_reference":display(excess,10)}


def count(jmax):
    top=2*jmax*jmax
    prime,powers=prime_data(top)
    cuts=sorted({k for j in range(2,jmax+1) for k in (j*j//2,j*j,2*j*j)})
    F=[ZERO]*3
    G=[ZERO]*3
    snapshots={}
    start=2
    for end in cuts:
        for n in range(start,end+1):
            if not prime[n] and n not in powers:
                continue
            p,k=(n,1) if prime[n] else powers[n]
            lp=log_int(p)
            a=times(lp,inverse_root(n))
            g=min(k,3)-1
            F[g]=plus(F[g],a)
            G[g]=plus(G[g],times(a,natural(k,lp)))
        snapshots[end]=(F.copy(),G.copy())
        start=end+1
    coefficient,analytic=constants()
    L=log_int(2)
    examples=[];worst_lower=worst_upper=None
    prime_failures=0;first_failure=None;direct_roots=[];highest_prime_only=None
    for j in range(2,jmax+1):
        x=j*j
        relative=natural(2,log_int(j))
        a,g=snapshots[x//2];b,h=snapshots[x];c,i=snapshots[2*x]
        groups=[]
        for s in range(3):
            left=minus(minus(h[s],g[s]),times(minus(relative,L),minus(b[s],a[s])))
            right=minus(times(plus(relative,L),minus(c[s],b[s])),minus(i[s],h[s]))
            groups.append(plus(left,right))
        whole=plus(plus(groups[0],groups[1]),groups[2])
        main=natural(j,coefficient)
        gap=minus(whole,main)
        bare=minus(groups[0],main)
        assert -SCALE <= 5*gap[0] and 5*gap[1] <= SCALE, j
        if worst_lower is None or gap[0]<worst_lower[1][0]:
            worst_lower=j,gap
        if worst_upper is None or gap[1]>worst_upper[1][1]:
            worst_upper=j,gap
        if highest_prime_only is None or bare[1]>highest_prime_only[1][1]:
            highest_prime_only=j,bare
        assert bare[1]<0, j
        if 5*bare[1] < -SCALE:
            prime_failures+=1
            if first_failure is None:
                first_failure=j
        if j in (2,3,5,7,11,23):
            other=direct_small(j)
            assert all(max(u[0],v[0])<=min(u[1],v[1]) for u,v in zip(groups,other))
            direct_roots.append(j)
        if j in (2,3,7,49,100,577,2663,jmax):
            examples.append({"root":j,"window":[x//2,2*x],"main":interval_text(main),
                             "all_powers":interval_text(whole),"prime_only":interval_text(groups[0]),
                             "squares":interval_text(groups[1]),"higher_powers":interval_text(groups[2]),
                             "full_minus_main":interval_text(gap),"prime_only_minus_main":interval_text(bare)})
    return {"last_root":jmax,"largest_sieve_index":top,"scale":SCALE,"constants":analytic,
            "full_lowest_enclosure":[worst_lower[0],interval_text(worst_lower[1])],
            "full_highest_enclosure":[worst_upper[0],interval_text(worst_upper[1])],
            "prime_only_proven_lower_failures":prime_failures,"first_prime_only_lower_failure":first_failure,
            "highest_prime_only_minus_main":[highest_prime_only[0],interval_text(highest_prime_only[1])],
            "direct_crosscheck_roots":direct_roots,"examples":examples}


def divisor_control(j):
    """Direct addition using exp(Lambda(n))=n/product(exp(Lambda(d)), d|n, d<n)."""
    from array import array
    from decimal import Context, Decimal
    ctx=Context(prec=32)
    x=j*j;limit=2*x
    product=array("Q",[1])*(limit+1)
    def scaled(v):
        a,b=v.as_integer_ratio()
        return a*SCALE//b,ceil_div(a*SCALE,b)
    def log_decimal(n):
        v=ctx.ln(Decimal(n))
        return scaled(ctx.next_minus(v))[0],scaled(ctx.next_plus(v))[1]
    def inv_decimal(n):
        v=ctx.sqrt(Decimal(n))
        lo_a,lo_b=ctx.next_minus(v).as_integer_ratio()
        hi_a,hi_b=ctx.next_plus(v).as_integer_ratio()
        return SCALE*hi_b//hi_a,ceil_div(SCALE*lo_b,lo_a)
    L=log_decimal(2);cx=log_decimal(x)
    left=minus(cx,L);right=plus(cx,L)
    money=[ZERO]*3
    labels=[0,0,0]
    for n in range(2,limit+1):
        assert n%product[n]==0
        base=n//product[n]
        if base==1:
            continue
        for m in range(2*n,limit+1,n):
            product[m]*=base
        if 2*n<=x or n>=2*x:
            continue
        lp=log_decimal(base);ln=lp if base==n else log_decimal(n)
        w=minus(ln,left) if n<=x else minus(right,ln)
        group=0 if n==base else 1 if base*base==n else 2
        money[group]=plus(money[group],times(times(lp,inv_decimal(n)),w))
        labels[group]+=1
    return {"root":j,"summand_counts":labels,"prime":interval_text(money[0],9),
            "squares":interval_text(money[1],9),"higher":interval_text(money[2],9),
            "full":interval_text(plus(plus(money[0],money[1]),money[2]),9)}


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--root",type=int,default=2663)
    cli.add_argument("--divisor-control",type=int,help="Independent divisor-product source and decimal-log control at one root")
    a=cli.parse_args()
    if a.root<2:
        cli.error("root must be at least two")
    result=count(a.root)
    result["prime_upper_calibration"]=prime_upper_calibration()
    result["exact_diagonal"]=diagonal()
    result["changed_aperture"]=narrow_aperture()
    result["four_point_model"]={"one_turn":"ln(2)","off_center_shift":"ln(9/8)/ln(2)","centered_return":"4",
                                "split_return":str(2*(Q(9,8)+Q(8,9))),
                                "split_quadratic_price":str(8-4*(Q(9,8)+Q(8,9))),
                                "split_gram_determinant":str(16-(2*(Q(9,8)+Q(8,9)))**2)}
    if a.divisor_control is not None:
        if a.divisor_control<2:cli.error("control root must be at least two")
        result["divisor_control"]=divisor_control(a.divisor_control)
    print(json.dumps(result,indent=2))
