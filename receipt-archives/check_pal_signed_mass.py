"""Recheck integer mass signs between quotient anchors and the smooth factorization."""
import argparse
from bisect import bisect_left, bisect_right
from fractions import Fraction as Q
from itertools import accumulate
from pathlib import Path
import json
import hashlib
import struct
from math import isqrt
from check_pal_cubic_window import scales
from check_pal_reference_prices import mu, physical
from check_pal_primitive_mesh import SQUARE_DIVISORS, rough_count


def coarse_counts(x):
    result=[]
    two=1
    i=0
    while two<=x:
        q=two
        j=0
        while q<=x:
            b=(2**(i//2+1)-1)*(3**(j//2+1)-1)//2
            result.append((q,b))
            q*=3
            j+=1
        two*=2
        i+=1
    return sorted(result)


def check_sources():
    hi=12000
    ordinary=[0]+list(accumulate(mu(n) for n in range(1,hi+1)))
    actual=[0]+list(accumulate(physical(n) for n in range(1,hi+1)))
    coeffs=coarse_counts(hi)
    for n in [*range(1,513),*range(577,hi+1,61),hi]:
        assert actual[n]==sum(b*ordinary[n//q] for q,b in coeffs if q<=n)
    assert [(n,actual[n]) for n in [43,44]]==[(43,1),(44,-1)]
    assert all(value<0 for value in actual[44:])
    return {"trial_factor_limit":hi,"at_43":actual[43],"at_44":actual[44]}


def mixing_replay():
    from math import factorial
    checks=0
    tightest=Q(0)
    for Y,m in [(3,2),(6,2),(8,3),(20,3),(32,4),(44,4),(100,5),(256,5)]:
        upper=Y+m*(Y-1)
        marks=[0]+[physical(n) for n in range(1,upper+1)]
        M=list(accumulate(marks))
        B=sum(Q(marks[n],n)*(Y-n) for n in range(1,Y+1))
        ways=[1]
        for _ in range(m):
            old=[0]+list(accumulate(ways))
            ways=[old[min(t+1,len(old)-1)]-old[max(0,t-Y+1)] for t in range(len(ways)+Y-1)]
        denominator=Y**m
        assert sum(ways)==denominator
        total=source=outer=0
        for z,multiplicity in enumerate(ways):
            x=Y+z
            late=sum(M[x//r] for r in range(1,x//Y+1))
            tail=sum(marks[k]*(x//k-x//Y) for k in range(1,Y+1))
            # The convolution of a with 1 has the following explicit nonnegative profile.
            positive=sum(b for q,b in coarse_counts(x))
            assert positive-late==tail
            total+=multiplicity*tail
            source+=multiplicity*positive
            outer+=multiplicity*late
        expected=Q(total,denominator)
        mean=Y+Q(m*(Y-1),2)
        error=expected-(mean+Q(1,2))*B/Y
        cap=Q(sum(abs(x) for x in marks[1:Y+1]),2**(m+1))
        assert abs(error)<=cap and expected==Q(source-outer,denominator)
        tightest=max(tightest,abs(error)/cap)
        checks+=1
    factorial_tests=0
    for Y in range(2,9):
        x=factorial(Y)
        actual=[0]+list(accumulate(physical(n) for n in range(1,x+1)))
        after=sum(actual[x//r] for r in range(x//Y+1,x+1))
        B=sum(physical(n)*(Q(Y,n)-1) for n in range(1,Y+1))
        assert after==Q(x,Y)*B
        factorial_tests+=1
    return {"finite_mixed_windows":checks,"finite_factorial_frames":factorial_tests,
            "largest_error_fraction_of_proved_bound":str(tightest)}


def certify_grid(path,direct_end=200000000):
    rows=[tuple(map(int,line.split())) for line in path.read_text(encoding="ascii").splitlines()][::-1]
    assert rows[0][1]<=direct_end<rows[-1][1]
    assert all(i==j+1 and a<b for (i,a,_),(j,b,_) in zip(rows,rows[1:]))
    roots=sorted(scales(rows[-1][1]))
    root_squares=[q for _,q in roots]
    pref=[0]+list(accumulate(v for v,_ in roots))
    last=direct_end
    first_gap=None
    cheap=exact=failed=0
    for (_,l,ml),(_,r,mr) in zip(rows,rows[1:]):
        count=bisect_right(root_squares,r)
        # Each reduced cofactor has density 1/3 with endpoint error at most 2/3.
        # The full reciprocal sum of the smooth roots is 3.
        upper=(r-l)+(4*pref[count]+2)//3
        if ml+mr+upper<0:
            cheap+=1
            ok=True
        else:
            # Exact upper capacity after excluding four more prime squares.
            ub=0
            for v,v2 in roots[:count]:
                a,b=l//v2,r//v2
                ub+=v*sum(s*(rough_count(b//q)-rough_count(a//q)) for q,s in SQUARE_DIVISORS)
            assert ub>=abs(ml-mr)
            ok=ml+mr+ub<0
            if ok:
                exact+=1
            else:
                failed+=1
                if first_gap is None:
                    first_gap=[l,r,ml,mr,ub]
        if first_gap is None and ok:
            last=max(last,r)
    return {"first_quotient":rows[-1][0],"last_quotient":rows[0][0],"total_anchors":len(rows),
            "proved_strict_negative_through":last,"first_unresolved_interval":first_gap,
            "cheap_panels":cheap,"sharper_panels":exact,"total_unresolved_panels":failed,
            "largest_examined_endpoint":rows[-1][1]}


def replay_lioen(maxima_file,D=200000000,T=10**13,resolution=2048):
    """Reprice the full high range from saved ordinary maxima and the published 571/1000."""
    maxima=[v[0] for v in struct.iter_unpack("<i",maxima_file.read_bytes())]
    ends=[0]
    while ends[-1]<D:
        a=ends[-1]+1
        ends.append(min(D,a+max(1,a//resolution)-1))
    assert len(ends)==len(maxima) and D>200 and T<=10**13
    # The very first ordinary bins contain one independently factored integer each.
    small=0
    for n in range(1,1000):
        small+=mu(n)
        assert ends[n]==n and maxima[n]==small
    coeffs=coarse_counts(T)
    panels=failed=0
    minimum=None
    a=D+1
    while a<=T:
        b=min(T,a+max(1,a//resolution)-1)
        bound=0
        for q,c in coeffs:
            if q>b:break
            lo,hi=a//q,b//q
            high=None
            if hi>D:
                high=isqrt(571**2*hi)//1000
            if lo<=D:
                first,last=bisect_left(ends,lo),bisect_left(ends,min(hi,D))
                local=max(maxima[first:last+1])
                upper=local if high is None else max(local,high)
            else:
                upper=high
            bound+=c*upper
        panels+=1
        failed+=bound>=0
        den=isqrt(b)
        if den*den<b:den+=1
        ratio=((-bound)*10**6)//den if bound<0 else -max(0,bound)*10**6
        minimum=ratio if minimum is None else min(minimum,ratio)
        a=b+1
    return {"ordinary_bins":len(ends),"panels":panels,"misses":failed,
            "uniform_negative_margin_per_million_sqrt":minimum,
            "maxima_sha256":hashlib.sha256(maxima_file.read_bytes()).hexdigest()}


def small_grid(path):
    from array import array
    from check_pal_growth_windows import sieve
    nodes=[tuple(map(int,line.split())) for line in path.read_text(encoding="ascii").splitlines()]
    top=nodes[0][1]
    if top>10**7:
        raise ValueError("Use an explicitly small grid for the independent Euler sieve")
    vals,_,_=sieve(top)
    rough=array("i",[0])
    for d in range(1,top+1):
        rough.append(rough[-1]+(vals[d] if d%2 and d%3 else 0))
    for _,n,m in nodes:
        assert sum(v*rough[n//v2] for v,v2 in scales(n))==m
    return {"direct_alternate_sieve":top,"matching_quotient_values":len(nodes)}


def terminal(binary,T):
    from check_pal_cubic_window import reciprocal_rows
    from check_pal_prime_transport import outward
    roots=list(scales(T))
    query=[v2 for _,v2 in roots]
    all_rows=reciprocal_rows([str(binary)],T,24000000,query,False)
    rough_rows=reciprocal_rows([str(binary)],T,20000000,query,True)
    M=0
    Wlo=Whi=Q(0)
    for v,v2 in roots:
        l,h,m=all_rows[v2]
        l2,h2,m2=rough_rows[v2]
        assert m==m2
        low,high=max(l,l2),min(h,h2)
        assert low<=high
        Wlo+=low/v
        Whi+=high/v
        M+=v*m
    return {"head":T,"physical_mass":M,"primitive":[outward(T*Wlo-M,3,False),outward(T*Whi-M,3,True)]}


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--grid",type=Path)
    ap.add_argument("--small-grid",type=Path)
    ap.add_argument("--terminal-binary",type=Path)
    ap.add_argument("--ten-trillion",action="store_true",help="Use the published ordinary Mertens bound above the direct region")
    a=ap.parse_args()
    out={"small":check_sources(),"finite_comparison":mixing_replay()}
    if a.grid:
        out["independent_grid"]=certify_grid(a.grid)
    if a.small_grid:
        out["small_grid"]=small_grid(a.small_grid)
    if a.terminal_binary:
        out["ten_trillion_terminal"]=terminal(a.terminal_binary.resolve(),10**13)
    if a.ten_trillion:
        out["published_input_replay"]=replay_lioen(Path(__file__).with_name("ordinary-mertens-maxima-200m.bin"))
    print(json.dumps(out,indent=2))
