"""Certify all points between primitive samples with a bound on the positive curvature."""
import argparse
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import hashlib
import json
import subprocess
from check_pal_cubic_window import scales
from check_pal_prime_transport import outward


def make_grid(top,base,limit):
    k = top//limit
    if k <= 0 or top//k != limit:
        raise ValueError("The requested limit must be a quotient-grid head")
    keys=[]
    while top//k>base:
        keys.append(k)
        k += max(1,k//32)
    return keys+[k]


def requirements(top,keys):
    return sorted({k*v2 for k in keys for v,v2 in scales(top//k)})


def raw_mesh(file):
    rows={}
    for line in file.read_text(encoding="ascii").splitlines():
        kind,k,l,h,m=line.split()
        assert kind=="reciprocal" and int(l)<=int(h) and int(k) not in rows
        rows[int(k)] = int(l),int(h),int(m)
    return rows


def rough_count(n):
    return n-n//2-n//3+n//6


# Exclude four small prime squares, in addition to all multiples of 2 and 3.
SQUARE_DIVISORS=[(1,1)]
for prime in (5,7,11,13):
    SQUARE_DIVISORS += [(q*prime**2,-sgn) for q,sgn in SQUARE_DIVISORS]


def curvature(left,right,Mleft,Mright):
    upper_abs = 0
    for v,v2 in scales(right):
        a,b = left//v2,right//v2
        allowed = sum(s*(rough_count(b//q)-rough_count(a//q)) for q,s in SQUARE_DIVISORS)
        upper_abs += v*allowed
    positive=(upper_abs+Mright-Mleft)//2
    assert positive>=0 and upper_abs>=abs(Mright-Mleft)
    return Q((right-left)*positive,left)


def bridge(left,right,amount):
    # At fraction h the lower curve is left*(1-h)+right*h-amount*h*(1-h).
    if amount == 0:
        return min(left,right)
    h = min(Q(1),max(Q(0),(amount+left-right)/(2*amount)))
    return (1-h)*left+h*right-amount*h*(1-h)


def endpoints(files,top,keys):
    queries = requirements(top,keys)
    tables = [raw_mesh(p) for p in files]
    assert all(set(t)==set(queries) for t in tables)
    result={}
    for k in keys:
        n=top//k
        mass=0
        lo=hi=Q(0)
        for v,v2 in scales(n):
            rows=[t[k*v2] for t in tables]
            assert all(r[2]==rows[0][2] for r in rows)
            l=max(r[0] for r in rows)
            u=min(r[1] for r in rows)
            assert l<=u
            mass+=v*rows[0][2]
            lo+=Q(l,2**57*v)
            hi+=Q(u,2**57*v)
        result[n] = mass,n*lo-mass,n*hi-mass
    return result,{"top":top,"keys":list(keys),"rough_queries":len(queries),
                   "input_sha256":[hashlib.sha256(p.read_bytes()).hexdigest() for p in files]}


def join(dst,other):
    for n,(m,l,u) in other.items():
        if n in dst:
            old,a,b = dst[n]
            assert m==old
            l,u=max(l,a),min(u,b)
        assert l<=u
        dst[n]=m,l,u


def certify_nodes(data):
    ns=sorted(data)
    panels=[]
    directions=[]
    for a,b in zip(ns,ns[1:]):
        ma,la,_=data[a]
        mb,lb,_=data[b]
        E=curvature(a,b,ma,mb)
        floor=bridge(la,lb,E)
        lower_root=floor/(isqrt(b)+1) if floor>=0 else floor/max(1,isqrt(a))
        panels.append((lower_root,a,b,floor,E))
        _,_,ha=data[a]
        _,_,hb=data[b]
        directions.append((Q(a*lb-b*ha,b-a),Q(a*hb-b*la,b-a)))
    worst=min(panels)
    return {"covered_from":ns[0],"covered_through":ns[-1],"mesh_nodes":len(ns),
            "all_panel_lower_bounds_positive":all(row[3]>0 for row in panels),
            "strictly_falling_normalized_panels":sum(right<0 for left,right in directions),
            "last_panel_weighted_mass":[outward(directions[-1][0],3,False),outward(directions[-1][1],3,True)],
            "failed_panels":[[a,b,outward(f,3,False)] for _,a,b,f,_ in panels if f<=0],
            "lowest_proved_multiple_of_sqrt_t":outward(worst[0],6,False),
            "weakest_panel":[worst[1],worst[2]],"weakest_panel_primitive_lower":outward(worst[3],3,False),
            "at_maximum":[outward(data[ns[-1]][1],4,False),outward(data[ns[-1]][2],4,True)]}


def specification():
    top=32*10**12
    low=make_grid(top,200000000,10**12)
    yield "lower",top,low
    for t in (32*10**12,31*10**12):
        yield f"upper-{t//10**12}",t,list(range((t+2*10**12-1)//(2*10**12),t//10**12+1))


def summarize(groups):
    nodes={}
    inputs=[]
    for files,top,keys in groups:
        t,meta=endpoints(files,top,keys)
        join(nodes,t)
        inputs.append(meta)
    report=certify_nodes(nodes)
    report["raw_unit"]=2**57
    report["quotient_inputs"]=inputs
    report["endpoint_receipts"]=[[n,m,str(l),str(h)] for n,(m,l,h) in sorted(nodes.items())]
    return report


def rebuild(binary,folder):
    folder.mkdir(parents=True,exist_ok=True)
    groups=[]
    for label,top,keys in specification():
        request="".join(f"{q}\n" for q in requirements(top,keys)).encode("ascii")
        files=[]
        for name,cutoff,mode in [("all",30000000,"--reciprocal"),("rough",26000000,"--rough-reciprocal")]:
            file=folder/(f"primitive-mesh-{label}-{name}.tsv")
            with file.open("wb") as out:
                subprocess.run([str(binary),str(top),str(cutoff),mode,"--stdin"],input=request,stdout=out,check=True)
            files.append(file)
        groups.append((files,top,keys))
    return summarize(groups)


if __name__ == "__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--moments-binary",type=Path)
    ap.add_argument("--work",type=Path)
    ap.add_argument("--replay-record",type=Path)
    args=ap.parse_args()
    if args.replay_record:
        mesh=json.loads(args.replay_record.read_text(encoding="utf8"))["continuum_mesh"]
        nodes={n:(m,Q(l),Q(h)) for n,m,l,h in mesh["endpoint_receipts"]}
        report=certify_nodes(nodes)
        assert all(mesh[k]==v for k,v in report.items()) and report["all_panel_lower_bounds_positive"]
    elif args.moments_binary and args.work:
        report=rebuild(args.moments_binary.resolve(),args.work)
    else:
        ap.error("Supply a result record, or the compiled moments binary and a working directory")
    print(json.dumps(report,indent=2))
