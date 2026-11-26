"""Evaluate the one-head primitive, and the two local corrections to a fourth-power prediction."""
import argparse
from fractions import Fraction as Q
from math import comb, isqrt
from pathlib import Path
import json
from check_pal_reference_prices import physical
from check_pal_prime_transport import outward


def point(x):
    return Q(x),Q(x)


def plus(a,b):
    return a[0]+b[0],a[1]+b[1]


def minus(a,b):
    return a[0]-b[1],a[1]-b[0]


def times(k,a):
    k = Q(k)
    return (k*a[0],k*a[1]) if k >= 0 else (k*a[1],k*a[0])


def bounds(a):
    return [outward(a[0],8,False),outward(a[1],8,True)]


def primitive(table,x):
    mass,wat = table[x]
    return minus(times(x,wat),point(mass))


def shares(table,a,b):
    """Mass a(n)/n goes to the two neighbors while preserving its first moment."""
    assert 0 <= a < b
    m = table[b][0]-table[a][0]
    w = minus(table[b][1],table[a][1])
    return times(Q(1,b-a),minus(times(b,w),point(m))),times(Q(1,b-a),minus(point(m),times(a,w)))


def prediction(table,j):
    prev,H,s = 2*(j-1)**4,2*j**4,(j+1)**4
    k = isqrt(isqrt(s//2))
    a,b = 2*k**4,2*(k+1)**4
    assert a < s < b <= H < 2*s
    t = Q(s-a,b-a)
    at = lambda n:primitive(table,n)
    extrap = plus(at(H),times(Q(2*s-H,H-prev),minus(at(H),at(prev))))
    old = minus(extrap,plus(times(1-t,at(a)),times(t,at(b))))
    true = minus(at(2*s),at(s))
    inside = plus(shares(table,a,s)[1],shares(table,s,b)[0])
    outside = plus(shares(table,prev,H)[1],shares(table,H,2*s)[0])
    correction = plus(times(Q((s-a)*(b-s),b-a),inside),times(2*s-H,outside))
    delta = minus(true,old)
    assert max(delta[0],correction[0])<=min(delta[1],correction[1])
    return old,true,correction,(a,s,b,prev,H,2*s)


def read_native(scan,which):
    S = int(scan["scale"])
    table={0:(0,point(0))}
    for row in scan["knots"]:
        n=row[0]
        m,absolute,center=map(int,row[which])
        table[n] = m,(Q(center-absolute,S),Q(center+absolute,S))
    return table


def leading_coefficient():
    # Euler-transform the alternating eta series. Each inner finite difference
    # of 1/sqrt(n) lies in [0,1], by its positive Laplace integral.
    S=2**160
    root=lambda n: (Q(isqrt(n*S*S),S),Q(isqrt(n*S*S)+1,S))
    inv=lambda x:(1/x[1],1/x[0])
    lo=hi=Q(0)
    terms=48
    for k in range(terms):
        for j in range(k+1):
            a,b=times(Q((-1)**j*comb(k,j),2**(k+1)),inv(root(j+1)))
            lo+=a
            hi+=b
    hi+=Q(1,2**terms)
    def logs(x):
        s=sum(2*x**(2*j+1)/(2*j+1) for j in range(64))
        return s,s+2*x**129/(129*(1-x*x))
    l2=logs(Q(1,3));l3=logs(Q(1,2))
    r2,r3=root(2),inv(root(3))
    low=4*r2[0]/(hi*(1-r3[0])*4*l2[1]*l3[1])
    high=4*r2[1]/(lo*(1-r3[1])*4*l2[0]*l3[0])
    return {"eta_half":bounds((lo,hi)),"primitive_positive_limsup_coefficient":bounds((low,high))}


def check_small():
    J = 8
    knots = sorted({0}|{d*j**4 for j in range(1,J+1) for d in (1,2)})
    assert len(knots)==2*J+1
    table = {}
    m,w = 0,Q(0)
    before = {}
    for n in range(knots[-1]+1):
        if n:
            a=physical(n)
            m+=a
            w+=Q(a,n)
            if a:
                before[n]=Q(a,n)
        if n in knots:
            table[n]=m,point(w)
    shares_at = {t:Q(0) for t in knots}
    for a,b in zip(knots,knots[1:]):
        l,r = shares(table,a,b)
        shares_at[a]+=l[0]
        shares_at[b]+=r[0]
    for j in range(1,J+1):
        H=j**4
        def taper(d):
            return min(Q(1),max(Q(0),2-Q(d,H)))
        raw = sum(y*taper(d) for d,y in before.items())
        assert raw == sum(y*taper(t) for t,y in shares_at.items())
        assert H*raw == primitive(table,2*H)[0]-primitive(table,H)[0]
    for j in [6,7]:
        old,true,corr,_=prediction(table,j)
        assert true[0]-old[0]==corr[0]==corr[1]
    atoms = [(83,Q(-83,190)),(95,Q(1)),(107,Q(-107,190))]
    assert sum(w/d for d,w in atoms)==sum(w for _,w in atoms)==0
    primitive_at = lambda x:sum(w*max(Q(0),Q(x,d)-1) for d,w in atoms)
    assert primitive_at(81)==primitive_at(162)==0 and primitive_at(95)==Q(-6,95)
    return {"leading_coefficient":leading_coefficient(),"three_label_interior_value":"-6/95","full_exact_root_limit":J,"knots_including_origin":len(knots),"old_head_predictions_checked":2}


def scan_summary(scan):
    J = scan["maximum_root"]
    tab = read_native(scan,1)
    results = []
    signs = {"positive":0,"negative":0,"undecided":0}
    for j in range(6,J):
        pred,observed,cor,ends = prediction(tab,j)
        scale = Q(1,(j+1)**2)
        signs["positive" if cor[0]>0 else "negative" if cor[1]<0 else "undecided"]+=1
        results.append({"from_root":j,"four_old_endpoints":[ends[3],ends[4],ends[0],ends[2]],
                        "old_forecast_in_root_units":bounds(times(scale,pred)),
                        "actual_in_root_units":bounds(times(scale,observed)),
                        "two_local_tents_in_root_units":bounds(times(scale,cor))})
    assert len(tab)==2*J+1
    rising,falling=[],[]
    for j in range(1,J):
        a,b=2*j**4,2*(j+1)**4
        la,ua=primitive(tab,a)
        lb,ub=primitive(tab,b)
        if lb/b>ua/a:
            rising.append(j)
        elif ub/b<la/a:
            falling.append(j)
    return {"endpoints":len(tab),"last_integer":2*J**4,
            "physical_minimum_harmonic_lower":outward(Q(int(scan["physical"]["minimum_harmonic_lower_over_S"]),int(scan["scale"])),8,False),
            "physical_minimum_location":scan["physical"]["harmonic_at"],
            "first_physical_nonpositive_candidate":scan["physical"]["first_possible_nonpositive_primitive_from_two"],
            "first_raw_negative_primitive":scan["raw"]["first_certified_negative_primitive"],
            "forecast_lower_always_positive":all(Q(x["old_forecast_in_root_units"][0])>0 for x in results),
            "local_correction_signs":signs,
            "normalized_primitive_rising_from_roots":rising,
            "normalized_primitive_falling_steps":len(falling),
            "maximum_absolute_local_correction_in_root_units":str(max(abs(Q(v)) for row in results for v in row["two_local_tents_in_root_units"])),
            "predictions":results}


def large(head,m,U):
    from check_pal_cubic_window import scales
    data={}
    for factor in [2,1]:
        x=2*head//factor
        W=point(0); M=0
        for v,v2 in scales(x):
            k=factor*v2
            W=plus(W,times(Q(1,v),U[k]))
            M+=v*m[k][0]
        data[x]={"primitive":bounds(minus(times(x,W),point(M))),"harmonic_prefix":bounds(W),
                 "unpassed_primitive":bounds(minus(times(x,U[factor]),point(m[factor][0])))}
    return data


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--scan",type=Path,help="JSON output of fourth_primitive")
    ap.add_argument("--moments-binary",type=Path)
    ap.add_argument("--large-head",type=int,nargs="+",default=[])
    args=ap.parse_args()
    report={"small":check_small()}
    if args.scan:
        report["dense"]=scan_summary(json.loads(args.scan.read_bytes()))
    if args.large_head:
        if not args.moments_binary:
            ap.error("A compiled cubic_window_moments binary is required for large quotient grids")
        from check_pal_reflected_cells import load_moments
        report["large"]={str(h):large(h,*load_moments(str(args.moments_binary),h)) for h in args.large_head}
    print(json.dumps(report,indent=2))
