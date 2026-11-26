"""Check square-root shell exposures, individual jump heights and the fixed integer samples."""
import argparse
from fractions import Fraction as Q
from itertools import accumulate
from math import gcd, isqrt
from pathlib import Path
import hashlib
import json
import subprocess

from check_pal_cubic_window import scales
from check_pal_dense_square_payment import arctan_inverse, display, sub
from check_pal_growth_windows import sieve
from check_pal_reference_prices import physical
from check_pal_rise_direction import box, mul, divide, sqrt_box


def cutoff(n):
    q=n**7
    for _ in range(4):
        q=isqrt(q)
    return q


def cases():
    out=[]
    def add(a,b):
        key=[a,b,cutoff(b)]
        if key not in out:
            out.append(key)
    for v,d in [(12,1),(72,1),(72,5),(576,1),(62208,1),(62208,5),(62208,35),(62208,2663),
                (4478976,1),(2**20,5),(3**13,1)]:
        n=v*v*d
        y=isqrt(n)
        for w in sorted({1,max(1,isqrt(y)),max(1,y//10),y}):
            add(n-w,n)
            add(n,n+w)
    for n in [10**4,10**8,10**11,10**13]:
        y=isqrt(n)
        for k in [-2,0,3]:
            add(n+k*y,n+(k+1)*y)
    return out


def native_replay(binary,record):
    selected=cases()
    data="".join(" ".join(map(str,c))+"\n" for c in selected).encode()
    cap=max(b for _,b,_ in selected)
    for mode,key in [("rows","row_hash"),("labels","label_hash")]:
        res=subprocess.check_output([str(binary.resolve()),str(cap),mode],input=data)
        assert hashlib.sha256(res).hexdigest()==record[key]
        got=[list(map(int,k.split())) for k in res.splitlines()]
        assert [r[:-1] for r in got]==[r[:-1] for r in record["rows"]]
        if mode=="labels":
            assert got==record["rows"]


def giant_inventory(top=10**28):
    # For an occupied label n=v^2 d, v>n^(7/16) is exactly v^2>d^7.
    dmax=isqrt(isqrt(isqrt(top)))
    mu,_,_=sieve(dmax)
    rough=[(d,d**7) for d in range(1,dmax+1,2) if d%3 and mu[d]]
    events=[]
    for v,v2 in scales(top):
        for d,power in rough:
            if power>=v2 or d*v2>top:
                break
            events.append((d*v2,v,d))
    events.sort()
    first=0;highest=0;pair=None
    near=None
    for i,(n,v,d) in enumerate(events):
        while (n-events[first][0])**2>n:
            first+=1
        occupied=[e for e in events[first:i+1] if e[1]**16>n**7]
        if len(occupied)>highest:
            highest=len(occupied)
            if highest>1:
                pair=occupied
        if i:
            previous=events[i-1]
            gap2=Q((n-previous[0])**2,n)
            if near is None or gap2<near[0]:
                near=(gap2,previous,events[i])
    return {"through":top,"candidates":len(events),"largest_simultaneous_count":highest,
            "multiple_witness":pair,"closest_consecutive_gap_squared_per_later_head":
            [str(near[0]),near[1],near[2]]}


def check(record):
    rows=record["rows"]
    assert [r[:3] for r in rows]==cases()
    pi=sub(mul(box(16),arctan_inverse(5)),mul(box(4),arctan_inverse(239)))
    kappa=divide(box(9),mul(pi,pi))
    independent=0;examples=[]
    for a,b,t,weight,count,largest,hit,high,signed in rows:
        assert 0<=abs(signed)<=weight and 0<=largest<=weight
        assert t**16<=b**7<(t+1)**16
        if (b-a)**2<=b:
            assert hit<=3
        if b<=400000:
            actual=[physical(n) for n in range(a+1,b+1)]
            numbers=[abs(x) for x in actual]
            assert [sum(numbers),sum(x!=0 for x in numbers),max(numbers),sum(x>t for x in numbers),
                    sum(x for x in numbers if x>t),sum(actual)]==[weight,count,largest,hit,high,signed]
            independent+=1
        if b in [4478976**2,5*2**40] or a==10**13:
            examples.append({"left":a,"right":b,"width":b-a,"largest":largest,"signed_total":signed,
                             "absolute_total":weight,
                             "remaining_absolute_per_position":display(box(Q(weight-largest,b-a)),8),
                             "signed_per_root":display(divide(box(signed),sqrt_box(b)),8)})
    prev=Path(__file__).with_name("2026-11-25-pal-running-mass.json")
    assert hashlib.sha256(prev.read_bytes()).hexdigest()=="5d6e8139d46e64777433428d9d4cf68635556d04ab15bc7894bacd3b7bb513b9"
    mass=[0]+list(accumulate(physical(n) for n in range(1,65)))
    small=[]
    for j in range(1,8):
        price,n=min((mass[n],n) for n in range(j*j,(j+1)**2))
        small.append([j,mass[j*j],n,price])
    return {"independent_trial_division_windows":independent,"finite_inventory":giant_inventory(),
            "ordinary_density":display(kappa,10),"examples":examples,
            "finite_square_evidence":{"early_root_square_mass_contact_and_mass":small,
                                      "direct_through_root":isqrt(27373823781),"outside_bound_through_root":isqrt(10**13),
                                      "optimal_natural_K_on_square_heads":2,"optimal_natural_K_on_square_contacts":1}}


def shell_summary(path):
    raw=path.read_bytes()
    rows=[list(map(int,line.split())) for line in raw.splitlines()[1:]]
    assert all(r[0]==j for j,r in enumerate(rows,1))
    direct=[0]+list(accumulate(physical(n) for n in range(1,81**2)))
    for j,size,peak,peak_trimmed,mark,net,contact,first in rows[:80]:
        shell=direct[j*j:(j+1)**2]
        assert (size,peak,net,contact,first)==(len(shell),max(abs(x-first) for x in shell),shell[-1]-first,min(shell),shell[0])
    bands=[]
    for a,b in [(10,99),(100,999),(1000,9999)]:
        subset=[r for r in rows if a<=r[0]<=b]
        if subset:
            bands.append({"from":a,"through":subset[-1][0],"count":len(subset),
                          "peak_above_quarter_root":sum(4*r[2]>r[0] for r in subset),
                          "trimmed_peak_above_quarter_root":sum(4*r[3]>r[0] for r in subset),
                          "peak_above_one_root":sum(r[2]>r[0] for r in subset)})
    equal=[r for r in rows if r[5]==0 and r[2]>0]
    return {"sha256":hashlib.sha256(raw).hexdigest(),"shells":len(rows),"bands":bands,
            "equal_ends_interior_example":max(equal,key=lambda r:Q(r[2],r[0])) if equal else None,
            "last_positive_square":max([r[0] for r in rows if r[7]>0],default=None),
            "last_entirely_positive_shell":max([r[0] for r in rows if r[6]>0],default=None)}


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--record",type=Path,default=Path(__file__).with_name("2026-11-26-pal-square-exposure.json"))
    cli.add_argument("--native",type=Path,help="A compiled square_shell_mass executable")
    cli.add_argument("--slabs",type=Path,help="Optional table from square_shell_mass squares")
    args=cli.parse_args()
    doc=json.loads(args.record.read_bytes())
    data=doc["native"] if "native" in doc else doc
    if args.native:
        native_replay(args.native,data)
    result=check(data)
    if args.slabs:
        result["consecutive_shells"]=shell_summary(args.slabs)
    print(json.dumps(result,indent=2))
