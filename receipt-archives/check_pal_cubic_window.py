"""Replay the cubic averaging window, the omitted first label and its four-row inverse.

Compile cubic_window_moments.cpp with g++ -O3 -std=c++17, then pass the binary's
path as the sole argument. The standard-library direct test always runs.
"""
from fractions import Fraction as Q
from math import isqrt
import json
import subprocess
import sys

from check_pal_growth_windows import sieve

TOP = 864_000_000_000
MOD_SMALL = (1 << 61) - 1
MOD_LARGE = 1 << 128


def scales(top, start=1):
    two = 1
    while start*two**2 <= top:
        root = two
        while start*root**2 <= top:
            yield root, start*root**2
            root *= 3
        two *= 2


def requested(top):
    values = set()
    for shift in (1, 4, 9, 36):
        for _, scale in scales(top, shift):
            values.add(scale)
            if 2*scale <= top:
                values.add(2*scale)
    return sorted(values)


def direct(top, rows):
    raw, _, _ = sieve(top)
    sums = [0]*4
    result = {}
    at = {}
    for d in rows:
        at.setdefault(top//d, []).append(d)
    for n in range(1, top+1):
        if n%6 in (1, 5):
            for j in range(4):
                sums[j] += raw[n]*n**j
        for d in at.get(n, ()):
            result[d] = tuple(sums)
    return result


def compiled(command, top, cutoff, rows, rough=False):
    mode = ["--rough-multipliers"] if rough else []
    text = subprocess.check_output([*command, str(top), str(cutoff), *mode, *map(str, rows)], text=True)
    residues = {}
    for line in text.splitlines():
        name, d, *values = line.split()
        assert len(values) == 4 and name in ("2^128", "2^61-1")
        key = (name, int(d))
        assert key not in residues
        residues[key] = tuple(map(int, values))
    assert len(residues) == 2*len(rows)
    inverse = pow(MOD_LARGE, -1, MOD_SMALL)
    full = MOD_LARGE*MOD_SMALL
    result = {}
    for d in rows:
        entry = []
        left, right = residues["2^128", d], residues["2^61-1", d]
        for j, (a, b) in enumerate(zip(left, right)):
            v = a+MOD_LARGE*((b-a)*inverse % MOD_SMALL)
            if v > full//2:
                v -= full
            bound = (top//d)**(j+1)
            assert 2*bound < full and abs(v) <= bound
            entry.append(v)
        result[d] = tuple(entry)
    return result


def numerator(top, d, moments):
    if d > top:
        return 0
    a, b, c, e = moments[d]
    return top**3*a - 3*top**2*d*b + 3*top*d*d*c - d**3*e


def positive_labels(top, d):
    n = 1
    total = 0
    while d*n <= top:
        total += (top-d*n)**3
        n *= 3
    return total


def report(top, moments):
    denominator = top**3
    def raw(d):
        return positive_labels(top, d) - numerator(top, d, moments) + numerator(top, 2*d, moments)
    def passed(d):
        return sum(root*raw(q) for root, q in scales(top, d))
    sides = (1, 4, 9, 36)
    values = [passed(d) for d in sides]
    assert raw(1) == values[0] - 2*values[1] - 3*values[2] + 6*values[3]
    return {
        "physical_side": str(Q(top, 2)),
        "positive_full_average_times_sqrt_side": str(Q(positive_labels(top, 1), denominator)),
        "omitted_first_response_times_sqrt_side": str(Q(raw(1), denominator)),
        "change_from_first_label_times_sqrt_side":
            str(Q(numerator(top,1,moments)-numerator(top,2,moments), denominator)),
        "scaled_passed_rows": [str(Q(v, denominator)) for v in values],
        "scaled_inverse_coefficients": [1, -2, -3, 6],
        "physical_passed_rows": [str(Q(v*2*d, denominator*top)) for d,v in zip(sides,values)],
        "physical_inverse_coefficients": ["1", "-1/2", "-1/3", "1/6"],
        "two_largest_moment_rows": {str(top//d):list(moments[d]) for d in (1,2)}
    }


def half_row(tick, marks):
    return sum((Q(marks[d], d)*min(1, Q(2*(tick-d), tick))
                for d in range(1,tick+1) if marks[d]), Q(0))


def direct_grid(head):
    top = 2*head
    raw, _, _ = sieve(top)
    base = [v if n%6 in (1, 5) else 0 for n,v in enumerate(raw)]
    layer = base.copy()
    for root in (2,3):
        for j in range(1,top//root**2+1):
            layer[root**2*j] += root*layer[j]
    moments = direct(top,requested(top))
    def response(q, omitted):
        return Q(positive_labels(top,q) - omitted*(
            numerator(top,q,moments)-numerator(top,2*q,moments)),top**3)
    results = []
    for omitted in (0,1):
        def profile(n):
            return sum((Q(top-r*n,top)**3 for r in range(1+omitted,top//n+1)),Q(0))
        value = [Q(0)]+[profile(n) for n in range(1,top+2)]
        slope = [Q(0)]+[n*(n+1)*(value[n]-value[n+1])/2 for n in range(1,top+1)]
        weights = [slope[n-1]-slope[n] for n in range(2,top+1)]
        assert all(w>=0 for w in weights)
        old = sum((w*half_row(n,base) for n,w in enumerate(weights,2)),Q(0))
        new = sum((w*half_row(n,layer) for n,w in enumerate(weights,2)),Q(0))
        assert old == response(1,omitted)
        assert new == sum(root*response(q,omitted) for root,q in scales(top))
        results.append({"omitted_initial_labels":omitted,"tested_weights":len(weights),
                        "positive_weights":sum(w>0 for w in weights),
                        "old_weighted_sum":str(old),"passed_weighted_sum":str(new)})
    return {"head":head,"readings":results}


def reciprocal_rows(command, top, cutoff, rows, rough):
    mode = "--rough-reciprocal" if rough else "--reciprocal"
    text = subprocess.check_output([*command,str(top),str(cutoff),mode,"--stdin"],
                                   input="\n".join(map(str,rows))+"\n",text=True)
    out = {}
    for line in text.splitlines():
        name, divisor, lo, hi, count = line.split()
        key = int(divisor)
        assert name == "reciprocal" and key not in out
        a, b = Q(int(lo),1<<57), Q(int(hi),1<<57)
        assert a<=b
        out[key] = (a,b,int(count))
    assert set(out)==set(rows)
    return out


def finite_readings(top, moments, reciprocal):
    def seed(q):
        a,b = reciprocal.get(q,(Q(0),Q(0)))
        c,d = reciprocal.get(2*q,(Q(0),Q(0)))
        correction = Q(2*q,top)*(moments.get(q,(0,))[0]-moments.get(2*q,(0,))[0])
        return 2*a-d-correction, 2*b-c-correction
    def passed(q):
        lo=hi=Q(0)
        for root, d in scales(top,q):
            a,b=seed(d)
            lo+=a/root
            hi+=b/root
        return lo,hi
    at=[passed(q) for q in (1,4,9,36)]
    old=seed(1)
    lower=upper=Q(0)
    for (a,b),w in zip(at,(Q(1),Q(-1,2),Q(-1,3),Q(1,6))):
        lower+=min(w*a,w*b)
        upper+=max(w*a,w*b)
    assert max(lower,old[0]) <= min(upper,old[1])
    qstr=lambda pair:[str(v) for v in pair]
    return {"side":str(Q(top,2)),"original":qstr(old),"one_pass":[qstr(p) for p in at],
            "inverse_enclosure":qstr((lower,upper))}


def physical_audit(command, top, rows, moments, cut_a, cut_b):
    a=reciprocal_rows(command,top,cut_a,rows,False)
    b=reciprocal_rows(command,top,cut_b,rows,True)
    assert all(a[d][2] == b[d][2] == moments[d][0] for d in rows)
    common={d:(max(a[d][0],b[d][0]),min(a[d][1],b[d][1])) for d in rows}
    assert all(v<=w for v,w in common.values())
    if top <= 8192:
        raw,_,_=sieve(top)
        vals={top//d for d in rows}
        sums={}
        total=Q(0)
        for n in range(1,top+1):
            if n%6 in (1,5): total+=Q(raw[n],n)
            if n in vals: sums[n]=total
        for d,(lo,hi) in common.items(): assert lo <= sums[top//d] <= hi
    return finite_readings(top,moments,common)


def positive_integers_coprime_to_six(n):
    return n - n//2 - n//3 + n//6


def sign_block(top, moments, enclosure, passed):
    """Price the whole real interval by counting every possible change in its band sum."""
    head = top//2
    side_roots = list(scales(4*top)) if passed else [(1,1)]
    def m0(d):
        return moments.get(d,(0,))[0]
    band = sum(root*(m0(d)-m0(2*d)) for root,d in side_roots if d<=top)
    lower, upper = map(Q,enclosure)
    sign = 1 if lower>0 else -1
    margin = lower if sign==1 else -upper
    assert margin>0
    def absolute(a,b):
        return sum(root*(positive_integers_coprime_to_six(b//q)-
                         positive_integers_coprime_to_six(a//q))
                   for root,q in side_roots if q<=b)
    def worst(delta, direction):
        a,b=sorted((head,head+direction*delta))
        amount=absolute(a,b)+absolute(2*a,2*b)
        adverse=max(0,amount-direction*sign*band)
        return Q(delta*adverse,head*(head+direction*delta))
    def limit(direction):
        good, bad=0,head//2
        assert worst(bad,direction)>=margin
        while bad-good>1:
            mid=(bad+good)//2
            if worst(mid,direction)<margin: good=mid
            else: bad=mid
        assert worst(good,direction)<margin<=worst(bad,direction)
        return good
    left, right=limit(-1),limit(1)
    lo,hi=head-left,head+right
    fourth_lo=isqrt(isqrt(lo-1))+1
    fourth_hi=isqrt(isqrt(hi))
    return {"sign":sign,"exact_band_at_head":band,"left":lo,"right":hi,
            "half_rows_inclusive":2*(hi-lo)+1,"fourth_power_roots":list(range(fourth_lo,fourth_hi+1)),
            "remaining_left_margin":str(margin-worst(left,-1)),
            "remaining_right_margin":str(margin-worst(right,1))}


def elementary():
    def term(n, x):
        return 2*n*(x-n)*(2*n-x)
    tested = 0
    for n in range(1,45):
        for a in range(8):
            x = n+Q(a,8)
            v = [term(j,x) for j in range(1,n+1)]
            assert sum(v) == n*(n+1)*(x-n)*(n+1-x)
            assert all(sum(v[m:]) >= 0 for m in range(n+1))
            tested += 1
    # A quadratic ramp's second derivative is negative at this point.
    x = Q(7,4)
    quadratic = (6-4*x)/x**4
    assert quadratic < 0
    top = 8192
    rows = requested(top)
    moments = direct(top, rows)
    data = report(top, moments)
    raw, _, _ = sieve(top)
    for n in range(1,321):
        weights = [Q(max(0,n-j),n)**3 for j in range(n+1)]
        both = sum(raw[d]*weights[d*r] for d in range(1,n+1) if d%6 in (1,5)
                   for r in range(1,n//d+1,2))
        assert both == Q(positive_labels(n,1),n**3)
    return {"convexity_cells":tested,"quadratic_second_derivative_at_7_over_4":str(quadratic),
            "direct_odd_multiple_sums":320,"exact_half_row_quadratures":[direct_grid(h) for h in (3,12,45,128)],
            "direct_sample":data}


def fourth_power_grid(command, root=1680):
    """One quotient grid covers the fourth powers of every divisor of the chosen root."""
    top=2*root**4
    roots=[d for d in range(1,root+1) if root%d==0]
    divisors={d:(root//d)**4 for d in roots}
    requests=set()
    for start in divisors.values():
        for _,q in scales(top,start):
            requests.add(q)
            if 2*q<=top: requests.add(2*q)
    rows=sorted(requests)
    a=reciprocal_rows(command,top,12_000_000,rows,False)
    b=reciprocal_rows(command,top,10_000_000,rows,True)
    assert all(a[q][2]==b[q][2] for q in rows)
    meet={q:(max(a[q][0],b[q][0]), min(a[q][1],b[q][1])) for q in rows}
    assert all(lo<=hi for lo,hi in meet.values())
    def seed(q):
        lo,hi=meet[q]
        l2,h2=meet.get(2*q,(Q(0),Q(0)))
        step=Q(2*q,top)*(a[q][2]-a.get(2*q,(0,0,0))[2])
        return 2*lo-h2-step, 2*hi-l2-step
    data=[]
    for j,start in divisors.items():
        lo=hi=Q(0)
        for p,q in scales(top,start):
            low,high=seed(q);lo+=low/p;hi+=high/p
        data.append({"fourth_root":j,"physical_side":j**4,"lower":str(lo),"upper":str(hi),
                     "sign":1 if lo>0 else -1 if hi<0 else 0})
    return {"largest_root":root,"quotient_arguments":len(rows),"sampled_fourth_powers":data}


def direct_fourths(command, last=128):
    """Read every fourth power through last from a single forward Mobius sieve."""
    reversal_side=262_440
    heads=[j**4 for j in range(1,last+1)]
    points=set()
    for h in [*heads,reversal_side]:
        for _,q in scales(2*h):
            points.add(2*h//q)
            if h//q: points.add(h//q)
    top=max(points)
    text=subprocess.check_output([*command,str(top),"1","--direct","--stdin"],
                                 input="\n".join(map(str,sorted(points)))+"\n",text=True)
    table={0:(Q(0),Q(0),0)}
    for line in text.splitlines():
        label,n,lo,hi,count=line.split()
        assert label=="direct" and int(n) not in table
        table[int(n)]=(Q(int(lo),1<<57),Q(int(hi),1<<57),int(count))
    assert set(table)==points|{0}
    def read(h):
        lo=hi=Q(0)
        band=0
        for p,q in scales(2*h):
            a,b,count=table[2*h//q]
            c,d,earlier=table[h//q]
            difference=count-earlier
            adjustment=Q(q*difference,h)
            lo+=(2*a-d-adjustment)/p
            hi+=(2*b-c-adjustment)/p
            band+=p*difference
        return lo,hi,band
    entries=[]
    reversals=[]
    prev=None
    for j,h in enumerate(heads,1):
        lo,hi,_=read(h)
        entries.append({"fourth_root":j,"lower":str(lo),"upper":str(hi)})
        if prev is not None and hi*j*j < prev[0]*(j-1)**2: reversals.append([j-1,j])
        prev=(lo,hi)
    x=reversal_side
    a,b,band=read(x)
    drift=(a+Q(2*band,x),b+Q(2*band,x))
    assert drift[1]<0
    return {"largest_root":last,"direct_sieve_through":top,"prefix_nodes":len(points),"roots":entries,
            "declines_in_root_squared_times_reading":reversals,
            "right_derivative_times_twice_sqrt_side":{"side":x,"interval":[str(v) for v in drift],
                                                       "exact_band":band}}


def audit(command):
    checks = elementary()
    if not command:
        return checks
    small = 8192
    rows = requested(small)
    small_moments=direct(small,rows)
    assert compiled(command,small,128,rows) == small_moments
    checks["direct_reciprocal_calibration"]=physical_audit(command,small,rows,small_moments,128,113)
    rows = requested(TOP)
    all_multipliers = compiled(command, TOP, 8_000_000, rows)
    rough_multipliers = compiled(command, TOP, 6_000_000, rows, rough=True)
    assert all_multipliers == rough_multipliers
    data = report(TOP, all_multipliers)
    assert 23 < Q(data["positive_full_average_times_sqrt_side"]) < 24
    assert -119 < Q(data["omitted_first_response_times_sqrt_side"]) < -118
    assert all(Q(v) > 0 for v in data["physical_passed_rows"])
    baseline = Q(data["positive_full_average_times_sqrt_side"])
    first = Q(data["change_from_first_label_times_sqrt_side"])
    assert baseline-first/6>0>baseline-first/5
    data["physical_rows_from_reciprocal_moments"] = physical_audit(command,TOP,rows,all_multipliers,8_000_000,6_000_000)
    actual = data["physical_rows_from_reciprocal_moments"]
    data["physical_sign_blocks"] = {"original":sign_block(TOP,all_multipliers,actual["original"],False),
                                    "one_pass":sign_block(TOP,all_multipliers,actual["one_pass"][0],True)}
    data["critical_removed_fraction"] = str(baseline/first)
    data["one_sixth_removed_times_sqrt_side"] = str(baseline-first/6)
    data["one_fifth_removed_times_sqrt_side"] = str(baseline-first/5)
    dense=direct_fourths(command)
    sparse=fourth_power_grid(command)
    matched={r["fourth_root"]:r for r in dense["roots"]}
    for row in sparse["sampled_fourth_powers"]:
        if row["fourth_root"] in matched:
            prior=matched[row["fourth_root"]]
            assert max(Q(row["lower"]),Q(prior["lower"])) <= min(Q(row["upper"]),Q(prior["upper"]))
    return {**checks,"large_quotient_divisors":len(rows),
            "independent_divisor_identities":["all multipliers, source supported at 2^a 3^b",
                                              "multipliers coprime to six, source at one"],
            "large_sample":data,"fourth_power_grid":sparse,"consecutive_fourths":dense}


if __name__ == "__main__":
    print(json.dumps(audit(sys.argv[1:]), indent=2))
