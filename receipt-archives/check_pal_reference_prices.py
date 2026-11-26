"""Replay the divisor inverse, margin and smooth-source minimizations with exact rationals."""
import argparse
from fractions import Fraction as Q
import json
from math import gcd, isqrt
from pathlib import Path
import subprocess


def mu(n):
    p, sign = 2, 1
    while p*p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            sign = -sign
        p += 1 if p == 2 else 2
    return -sign if n > 1 else sign


def physical(n):
    v = 1
    for p in (2,3):
        while n % (p*p) == 0:
            n //= p*p
            v *= p
        if n % p == 0:
            return 0
    return v*mu(n)


def physical_sources(T):
    roots = []
    a = 1
    while a*a <= T:
        v = a
        while v*v <= T:
            roots.append(v)
            v *= 3
        a *= 2
    return roots


def operator(f, sequence):
    T = len(f)-1
    return [Q(0)]+[sum((sequence[k]*f[k*d] for k in range(1,T//d+1)),Q(0)) for d in range(1,T+1)]


def ramp(y):
    return (max(Q(0),y-1)-max(Q(0),y/2-1))/2


def finite_games():
    games = 0
    exact_negative_bills = 0
    for T in [5,12,36,61,120]:
        gate = [0]+[int(gcd(k,6)==1) for k in range(1,T+1)]
        marks = [0]+[gate[k]*mu(k) for k in range(1,T+1)]
        weights = [0]+[physical(d) for d in range(1,T+1)]
        roots = physical_sources(T)
        for target in [[Q(0)]+[ramp(Q(T,d)) for d in range(1,T+1)],
                       [Q(0)]+[Q((17*d+T)%29-14,7) for d in range(1,T+1)]]:
            ideal = operator(target,marks)
            assert operator(ideal,gate) == target
            total = sum(a*p for a,p in zip(weights,target))
            assert total == sum(v*ideal[v*v] for v in roots)
            ray_bill = sum(v*max(0,-ideal[v*v]) for v in roots)
            exact_negative_bills += ray_bill > 0
            sources_clipped = ideal[:]
            for v in roots:
                sources_clipped[v*v] = max(0,ideal[v*v])
            total_clipped = ideal[:]
            total_clipped[1] += max(0,-total)
            for mode,u in [("exact",ideal),("rays",sources_clipped),("total",total_clipped),
                           ("nonnegative",list(map(abs,ideal))),
                           ("changing",[Q(0)]+[Q((13*d)%11-4,3) for d in range(1,T+1)])]:
                ref = operator(u,gate)
                error = [x-y for x,y in zip(target,ref)]
                inv_error = operator(error,marks)
                assert inv_error[1:] == [ideal[d]-u[d] for d in range(1,T+1)]
                signed = [w*e for w,e in zip(weights,error)]
                source = sum(v*u[v*v] for v in roots)
                cost = sum(map(abs,signed))
                assert total == source+sum(signed)
                assert total-(source-cost) == 2*sum(max(0,x) for x in signed)
                if mode == "rays":
                    assert source >= 0 and cost == ray_bill and total == source-cost
                if mode == "total":
                    assert source >= 0 and cost == max(0,-total) and total == source-cost
                games += 1
    return {"finite_games":games,"targets_with_strict_individual_ray_debt":exact_negative_bills}


def mul(a,b):
    products = [x*y for x in a for y in b]
    return min(products),max(products)


def add(a,b):
    return a[0]+b[0],a[1]+b[1]


def directed(x,up):
    denom = 10**8
    n = -(-(x*denom).numerator//(x*denom).denominator) if up else (x*denom).numerator//(x*denom).denominator
    sign = "-" if n<0 else ""
    return f"{sign}{abs(n)//denom}.{abs(n)%denom:08d}"


def credit_integral(scan):
    N = scan["max_y"]
    h = N//2
    moments = scan["integral_moments"]
    S,V = int(scan["scale"]),int(moments["root_scale"])
    def approx(which,den,error):
        v = int(moments[which])
        return Q(v-error,den),Q(v+error,den)
    def sqrt_bounds(n):
        z = isqrt(n*2**160)
        return Q(z,2**80),Q(z+1,2**80)
    def log_bounds(x):
        # log((1+x)/(1-x)) for 0<x<1
        partial = sum(2*x**(2*j+1)/(2*j+1) for j in range(64))
        return partial,partial+2*x**129/(129*(1-x*x))
    s = approx("full_reciprocal_over_S",S,N)
    sh = approx("half_reciprocal_over_S",S,h)
    b = approx("full_inverse_root_over_root_scale",V,N)
    bh = approx("half_inverse_root_over_root_scale",V,h)
    root = sqrt_bounds(N)
    ans = mul(root,add(s,mul((Q(-1,2),Q(-1,2)),sh)))
    m = moments["full_mass"]-moments["half_mass"]
    ans = add(ans,mul((m,m),(1/root[1],1/root[0])))
    ans = add(ans,mul((-2,-2),b))
    ans = add(ans,mul(sqrt_bounds(2),bh))
    divisor = mul(mul((4,4),log_bounds(Q(1,3))),log_bounds(Q(1,2)))
    co = mul(ans,(1/divisor[1],1/divisor[0]))
    return {"integral_interval":[directed(ans[0],False),directed(ans[1],True)],
            "credit_per_sqrt_T_log_T":[directed(co[0],False),directed(co[1],True)]}


def analyze_scan(scan):
    S = int(scan["scale"])
    band = scan["fixed_band"]
    assert scan["max_y"] == 40000000 and (band["left"],band["right"]) == (33400000,35300000)
    assert Q(int(band["upper_direct_over_4S"]),4*S) < -16
    assert Q(int(band["upper_integrated_over_2S"]),2*S) < -16
    assert int(scan["early_floor_over_4S"]) > 0 and scan["early_floor_last"] == 12000000
    assert Q(int(scan["global_floor_over_4S"]),4*S) > -32
    multiplier = 2**8*3**2
    assert 2*multiplier**2 <= scan["early_floor_last"] and scan["max_y"] <= 8*multiplier**2
    assert Q(multiplier,2*36) == 32
    # The odd, rough gate has only 1, 5 and 7 up to this last donor coordinate.
    for y in [2,5,7,8]:
        value = sum(mu(k)*ramp(Q(y,k)) for k in range(1,y+1) if gcd(k,6)==1)
        assert value >= Q(1,2)
    density_lo = Q(int(band["small_prime_product_lower_over_S"]),S)*(1-Q(1,band["right"]))
    constant = 16*density_lo*(Q(1,band["left"])-Q(1,band["right"]))
    assert density_lo > Q(323,10000) and constant>Q(8,10**10)
    return {"cutoff_integral":credit_integral(scan),"density_strictly_above":"0.0323",
            "margin_loss_per_T_liminf_strictly_above":"0.0000000008",
            "certified_density_lower":str(density_lo),"certified_liminf_lower":str(constant),
            "payment_multiplier":multiplier,"positive_fraction_sufficient":"1/36",
            "donor_interval":[2,8],"all_inputs_through":scan["max_y"]}


def count_primes(exe, root, method=None):
    A,B = 33400000,35300000
    X = root**4
    T = 2*X
    lo,hi = (T+B-1)//B,T//A
    args = [str(exe),"-t2"]+([method] if method else [])
    def pi(x):
        return int(subprocess.check_output(args+[str(x)],text=True).strip())
    before,last = pi(lo-1),pi(hi)
    assert lo>B
    return {"fourth_root":root,"side":X,"head":T,"first_label":lo,"last_label":hi,
            "pi_before":before,"pi_at_end":last,"prime_witnesses":last-before,
            "forced_absolute_price":16*(last-before),"forced_margin_loss":32*(last-before)}


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--scan",type=Path,help="JSON output of reference_obstruction 40000000")
    ap.add_argument("--primecount",type=Path)
    ap.add_argument("--method",help="optional primecount algorithm switch")
    ap.add_argument("--root",type=int,nargs="+",default=[10000,100000,1000000])
    args = ap.parse_args()
    result = finite_games()
    if args.scan:
        result["inverse_and_payment"] = analyze_scan(json.loads(args.scan.read_text(encoding="utf8")))
    if args.primecount:
        result["prime_counts"] = [count_primes(args.primecount,j,args.method) for j in args.root]
    print(json.dumps(result,indent=2))
