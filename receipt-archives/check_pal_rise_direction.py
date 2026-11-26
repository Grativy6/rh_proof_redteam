"""Check the compact divisor signal and the signed, fractionally retained physical input."""
from fractions import Fraction as Q
from itertools import accumulate
from math import isqrt
import json
from check_pal_cubic_window import scales
from check_pal_fourth_primitive import leading_coefficient
from check_pal_prime_transport import outward


def box(x):
    return Q(x),Q(x)


def mul(a,b):
    p=[x*y for x in a for y in b]
    return min(p),max(p)


def add(a,b):
    return a[0]+b[0],a[1]+b[1]


def flip(a):
    return -a[1],-a[0]


def divide(a,b):
    assert b[0]>0
    return mul(a,(1/b[1],1/b[0]))


def sqrt_box(x):
    x=Q(x)
    z=isqrt((x.numerator << 192)//x.denominator)
    return Q(z,2**96),Q(z+1,2**96)


def decimal(a):
    return [outward(a[0],7,False),outward(a[1],7,True)]


def prove_signal():
    P={1:1}
    # Multipliers after the alternating sequence. a*h has coefficients 1,-3,2.
    for q,w in [(2,-1),(3,-1),(4,-2),(9,-3),(2,-1)]:
        old=P.copy()
        for k,v in old.items():
            P[q*k]=P.get(q*k,0)+w*v
    def h(n):
        return sum(v*(1 if (n//k)%2 else -1) for k,v in P.items() if n%k==0)
    from check_pal_reference_prices import physical
    N=300
    for n in range(1,N+1):
        val=sum(physical(d)*h(n//d) for d in range(1,n+1) if n%d==0)
        assert val=={1:1,2:-3,4:2}.get(n,0)
    def f(x):
        x=Q(x)
        return sum(Q(physical(n),n)*(1-Q(n)/x) for n in range(1,int(x)+1))
    for X in [Q(3,2),Q(2),Q(5,2),Q(4),Q(29,4),Q(36)]:
        target=max(Q(0),1-1/X)-Q(3,2)*max(Q(0),1-2/X)+Q(1,2)*max(Q(0),1-4/X)
        assert sum(Q(h(r),r)*f(X/r) for r in range(1,int(X)+1))==target
    return {"divisor_coefficients_checked_through":N,"finite_heads_checked":6}


def retained(K,heads):
    assert K>=2
    muvals=[1]*(K+1)
    flags=bytearray([1])*(K+1)
    for p in range(2,K+1):
        if not flags[p]:continue
        if p*p<=K:flags[p*p::p]=b'\0'*len(flags[p*p::p])
        for j in range(p,K+1,p):muvals[j]=-muvals[j]
        for j in range(p*p,K+1,p*p):muvals[j]=0
    M=[0]+list(accumulate(muvals[n] if n%2 and n%3 else 0 for n in range(1,K+1)))
    S=2**72
    harmonic=[0]
    for n in range(1,K+1):
        harmonic.append(harmonic[-1]+isqrt(S*S//n))
    true_c=divide(tuple(map(Q,leading_coefficient()["eta_half"])),
                  mul(box(2),add(sqrt_box(2),box(-1))))
    out=[]
    for T in heads:
        tally=box(0)
        rows=0
        for v,v2 in scales(T):
            if T>K*v2:continue
            y=Q(T,v2)
            reader=Q(K,y)
            n=int(reader)
            ref=divide(box(n),sqrt_box(reader))
            hs=Q(harmonic[n],2*S),Q(harmonic[n]+n,2*S)
            w=divide(add(ref,flip(hs)),true_c)
            # Clip enclosures using the proven capacity bounds.
            w=max(Q(0),w[0]),min(Q(1),w[1])
            assert w[0]<=w[1]
            tally=add(tally,mul(box(v*M[int(y)]),w))
            rows+=1
        out.append({"head":T,"rough_cofactor_cutoff":K,"smooth_terms":rows,
                    "paid_signed_mass":decimal(tally),"paid_in_root_units":decimal(divide(tally,sqrt_box(T)))})
    return out


def smooth_balance(K):
    def log_small(x):
        z=(x-1)/(x+1)
        lo=sum(2*z**(2*j+1)/(2*j+1) for j in range(52))
        return lo,lo+2*z**105/(105*(1-z*z))
    log2=log_small(Q(2))
    def logarithm(x):
        j=0
        while x>=2:
            x/=2
            j+=1
        return add(mul(box(j),log2),log_small(x))
    result=box(0)
    for q,_ in scales(K*K):
        # scales(K*K) yields every smooth q <= K in its first component.
        term=divide(add(box(1),logarithm(Q(K,q))),sqrt_box(K))
        result=add(result,add(term,flip(divide(box(1),sqrt_box(q)))))
    c=divide(tuple(map(Q,leading_coefficient()["eta_half"])),mul(box(2),add(sqrt_box(2),box(-1))))
    denom=mul(c,mul(mul(box(4),log2),logarithm(Q(3))))
    return {"K":K,"exact_balance_enclosure":decimal(result),
            "fixed_cut_coefficient":decimal(divide(result,denom))}


if __name__=="__main__":
    heads=[2*10**8,10**10,10**12,2*10**12,10**13]
    print(json.dumps({"compact_signal":prove_signal(),
                      "partial_mass":[row for K in (10000,1000000) for row in retained(K,heads)],
                      "signed_balances":[smooth_balance(k) for k in (200,10000,1000000)]},indent=2))
