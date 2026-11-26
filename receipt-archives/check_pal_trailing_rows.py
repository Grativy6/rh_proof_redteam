"""Price adaptive trailing rows on the original 2,3-square and rough Möbius labels."""
import argparse
from array import array
from bisect import bisect_left, bisect_right
from fractions import Fraction as Q
from itertools import accumulate
from math import gcd, isqrt
from pathlib import Path
import hashlib
import json
import struct

from check_pal_cubic_window import scales
from check_pal_dense_square_payment import c_limit, display, sub
from check_pal_growth_windows import sieve
from check_pal_primitive_mesh import SQUARE_DIVISORS, rough_count
from check_pal_reference_prices import physical
from check_pal_rise_direction import add, box, divide, mul, sqrt_box
from check_pal_signed_mass import coarse_counts


def brute_hull(record):
    small,big=record["hulls"]
    nmax=small["through"]
    a=[0]+[physical(d) for d in range(1,nmax+1)]
    mass=list(accumulate(a))
    area=[0]+list(accumulate(mass))
    bad=[]
    peak=Q(0)
    detail=[]
    for n in range(1,nmax+1):
        if a[n]<=0:
            continue
        prices=[]
        for h in range(1,n+1):
            bill=h*mass[n]-(area[n]-area[n-h])
            if bill<=0:
                break
            prices.append((Q(n*bill*bill,(h*(h+1))**2),h,bill))
        else:
            price,h,bill=min(prices)
            peak=max(peak,price)
            bad.append(n)
            detail.append([n,h,bill,str(price)])
    assert small["no_nonpositive_width"]==big["no_nonpositive_width"]==bad
    assert peak==Q(256,289)
    return {"independent_brute_through":nmax,"exceptions_on_native_prefix":detail,
            "best_squared_constant_on_native_prefix":str(peak),"smallest_integer_K":1}


def check_spikes(records):
    small=[]
    for row in records:
        n=row["head"];direction=-1 if row["direction"]=="past" else 1
        if n>26000:
            continue
        m=charge=gross=abs_charge=0
        first_free=first_unit=-1
        want={r[0]:r for r in row["samples"]}
        for h in range(1,row["through_width"]+1):
            a=physical(n+direction*(h-1))
            m+=a;gross+=abs(a);charge+=m;abs_charge+=gross
            if h in want:
                assert want[h]==[h,m,charge,abs_charge]
            oriented=charge if row["head_mark"]>0 else -charge
            if oriented<=0 and first_free<0:
                first_free=h
            if row["rough"]==1 and first_unit<0 and row["unit"]*oriented<=h*(h+1):
                first_unit=h
        assert (first_free,first_unit)==(row["first_nonpositive_oriented_price"],row["first_unit_cost_at_square"])
        small.append([n,row["direction"],first_free,first_unit])
    return small


def moment_table(records):
    result={}
    for a,b in zip(records[::2],records[1::2]):
        assert a["mode"]=="physical" and b["mode"]=="ordinary" and a["rows"]==b["rows"]
        r={d:(n,m,u) for d,n,m,u in a["rows"]}
        if a["top"]==5184:
            mass=first=0
            wanted={n:(m,u) for n,m,u in r.values()}
            for n in range(1,5185):
                v=physical(n);mass+=v;first+=n*v
                if n in wanted:
                    assert wanted[n]==(mass,first)
        result[a["top"]]=r
    return result


def portions(record,cutoff):
    tables=moment_table(record["moments"])
    mu,_,_=sieve(cutoff)
    mass=array("i",[0])
    first=array("q",[0])
    # Each summand in the harmonic prefix has a known rounding width of at most one unit.
    scale=2**74
    harmonic=[0]
    for d in range(1,cutoff+1):
        a=mu[d] if gcd(d,6)==1 else 0
        mass.append(mass[-1]+a)
        first.append(first[-1]+d*a)
        harmonic.append(harmonic[-1]+isqrt(scale*scale//d))
    result=[]
    for head,rows in tables.items():
        for q in [1,4,16,64,256,1000,10000]:
            if q not in rows or q+1 not in rows:
                continue
            n,mn,un=rows[q];m,mm,um=rows[q+1]
            h=n-m
            if not h:
                continue
            ramp=Q(un-um-m*(mn-mm),h)
            back=box(0);front=box(0)
            for v,v2 in scales(n):
                y=Q(n,v2)
                if y>cutoff:
                    continue
                lo,hi=m//v2,n//v2
                mass_delta=mass[hi]-mass[lo]
                price=Q(v2*(first[hi]-first[lo])-m*mass_delta,h)
                x=Q(cutoff,y);k=int(x)
                reader=sub(divide(box(k),sqrt_box(x)),(Q(harmonic[k],2*scale),Q(harmonic[k]+k,2*scale)))
                keep=divide(reader,c_limit())
                keep=max(Q(0),keep[0]),min(Q(1),keep[1])
                assert keep[0]<=keep[1]
                back=add(back,mul(box(v*price),keep))
                front=add(front,mul(box(v*(mass_delta-price)),keep))
            alpha=Q(m,n);sa=sqrt_box(alpha)
            gap=divide(mul(sub(box(1),sa),add(box(1),mul(box(2),sa))),mul(box(3),add(box(1),sa)))
            result.append({"head":n,"earlier":m,"quotient_index":q,"width":h,"cutoff":cutoff,
                           "mass_change":mn-mm,"reverse":display(box(ramp),6),"forward":display(box(mn-mm-ramp),6),
                           "reverse_selected":display(back,6),"forward_selected":display(front,6),
                           "reverse_unspent":display(sub(box(ramp),back),6),"root_barrier_gap":display(gap,10)})
    return result


def grid_bound(file,start=50000000):
    rows=[list(map(int,line.split())) for line in file.read_bytes().splitlines()][::-1]
    assert rows[0][1]<=start<rows[-1][1]
    assert all(a[0]==b[0]+1 and a[1]<b[1] for a,b in zip(rows,rows[1:]))
    smooth=sorted(scales(rows[-1][1]))
    squares=[w for _,w in smooth]
    sums=[0]+list(accumulate(v for v,_ in smooth))
    last=start
    first_unknown=None
    cheap=sharp=0
    for left,right in zip(rows,rows[1:]):
        _,l,_,ul=left;_,r,_,ur=right
        count=bisect_right(squares,r)
        # Upper variation in the first moment is r times the unsigned count on (l,r].
        bound=(r-l)+(4*sums[count]+2)//3
        if ul+ur+r*bound<0:
            cheap+=1
        else:
            bound=0
            for v,v2 in smooth[:count]:
                a,b=l//v2,r//v2
                bound+=v*sum(s*(rough_count(b//q)-rough_count(a//q)) for q,s in SQUARE_DIVISORS)
            assert r*bound>=abs(ul-ur)
            if ul+ur+r*bound>=0:
                first_unknown=[l,r,ul,ur,bound]
                break
            sharp+=1
        last=max(last,r)
    return {"negative_full_price_through":last,"first_unresolved":first_unknown,
            "cheap_intervals":cheap,"sharper_intervals":sharp,"grid_sha256":hashlib.sha256(file.read_bytes()).hexdigest()}


def envelope(file,stop=10**13,direct=200000000,start=50000001):
    maxima=[x[0] for x in struct.iter_unpack("<q",file.read_bytes())]
    ends=[0]
    while ends[-1]<direct:
        a=ends[-1]+1
        ends.append(min(direct,a+max(1,a//2048)-1))
    assert len(maxima)==len(ends)
    ordinary,_,_=sieve(2000)
    moment=0
    for n in range(1,2001):
        moment+=n*ordinary[n]
        assert ends[n]==n and maxima[n]==moment
    rows=coarse_counts(stop)
    first_unknown=None;panels=nonnegative=0
    peak=Q(0);example=None
    a=start
    while a<=stop:
        b=min(stop,a+max(1,a//2048)-1,direct if a<=direct else stop)
        price=0
        for q,w in rows:
            if q>b:
                break
            lo,hi=a//q,b//q
            if hi>direct:
                # U(k)=k M(k)-sum_{s<k}M(s). Account for s<=200 separately.
                h=min(hi,10**13-1)
                upper=isqrt(913**2*h**3)//1000+20100
            if lo<=direct:
                left=bisect_left(ends,lo)
                right=bisect_left(ends,min(hi,direct))
                direct_max=max(maxima[left:right+1])
                upper=direct_max if hi<=direct else max(upper,direct_max)
            price+=q*w*upper
        panels+=1
        if price>=0:
            nonnegative+=1
            if first_unknown is None:
                first_unknown=[a,b,price]
            ratio=Q(price*price,a*(a+1)**2)
            if ratio>peak:
                peak=ratio;example=[a,b,price]
        a=b+1
    return {"first":start,"last":stop,"panels":panels,"unresolved_sign_panels":nonnegative,
            "continuous_negative_through":stop if first_unknown is None else first_unknown[0]-1,
            "first_unresolved":first_unknown,"largest_squared_allowance":str(peak),"largest_panel":example,
            "integer_K_for_prefix_and_panels":max(1,-(-peak.numerator//peak.denominator)),
            "maxima_sha256":hashlib.sha256(file.read_bytes()).hexdigest()}


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--record",type=Path,default=Path(__file__).with_name("2026-11-26-pal-trailing-rows.json"))
    cli.add_argument("--grid",type=Path,help="Optional complete quotient grid from the native first-moment program")
    cli.add_argument("--maxima",type=Path,default=Path(__file__).with_name("ordinary-mertens-first-moment-maxima-200m.bin"))
    opts=cli.parse_args()
    data=json.loads(opts.record.read_bytes())["native"]
    out={"brute":brute_hull(data),"small_spikes":check_spikes(data["spikes"]),
         "portions":[row for k in (10000,1000000) for row in portions(data,k)],
         "outside_input_envelope":envelope(opts.maxima)}
    if opts.grid:
        out["direct_grid"]=grid_bound(opts.grid)
    print(json.dumps(out,indent=2))
