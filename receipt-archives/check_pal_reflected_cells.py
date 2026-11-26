"""Check the signed remainder at a real arithmetic head and its reconstruction from moments.

Without a binary argument this runs the exact small grids and the larger direct
modulus scan. Passing the companion cubic_window_moments binary also runs the
independent quotient reconstructions at all twelve-power heads in the receipt.
"""
from fractions import Fraction as Q
from math import isqrt
import json
import sys

from check_pal_cubic_window import compiled, direct, reciprocal_rows, requested, scales
from check_pal_growth_windows import sieve
from check_pal_square_pass import coefficients


def interval(lo, hi):
    return (lo, hi)


def plus(a, b):
    return a[0]+b[0], a[1]+b[1]


def scale(c, a):
    return tuple(sorted((c*a[0], c*a[1])))


def wrapped(t, d):
    """Odd and even parts of the price of replacing a linear ramp by its discrete census."""
    if d > t:
        return Q(0), Q(0)
    r = t % d
    m = r*(d-r)
    return Q(m*(d-2*r), 2*d*t*t), -Q(m*m, 2*d*t**3)


def taper(z):
    return max(0, min(1, 2-z))


def step(z):
    return max(0, 1-z)**2*(1+2*z)


def profile(t, d):
    return sum((step(Q(r*d,t)) for r in range(1,t//d+1)),Q(0))


def ramp(t, d):
    return Q(max(0,t-d), 2*d)


def root_five_sixths(h):
    lo, hi = 0, h+1
    while hi-lo>1:
        m=(hi+lo)//2
        if m**6 <= h**5: lo=m
        else: hi=m
    return lo


def corner_checks():
    count = 0
    for t in range(1,129):
        for d in range(1,t+3):
            a,b=wrapped(t,d)
            assert ramp(t,d)-profile(t,d)==a+b
            if d<=t:
                s=t%d
                m=s*(d-s)
                reflected=Q(m*(d-2*(d-s)),2*d*t*t) - Q(m*m,2*d*t**3)
                assert reflected==-a+b and abs(a+b)<=Q(d*d,t*t)
            count+=1
    return count


def baseline(top, shift, passed):
    cubic=hermite=Q(0)
    for root,q in (scales(top,shift) if passed else [(1,shift)]):
        u=q
        while u<=top:
            t=Q(u,top)
            cubic+=root*(1-t)**3
            hermite+=root*step(t)
            u*=3
    return cubic, hermite


def from_moments(top, moments, recip, shift, passed):
    h=Q(top,2*shift)
    d0=m1delta=0
    reading=(Q(0),Q(0))
    for p,q in (scales(top,shift) if passed else [(1,shift)]):
        m=moments[q]
        l=moments.get(2*q,(0,0,0,0))
        upper=recip[q]
        lower=recip.get(2*q,(Q(0),Q(0)))
        band=m[0]-l[0]
        price=Q(2*q,top)*band
        reading=plus(reading, scale(Q(1,p),plus(plus(scale(2,upper),scale(-1,lower)),(-price,-price))))
        d0+=p*band
        m1delta+=p**3*(m[1]-2*l[1])
    p3,ps=baseline(top,shift,passed)
    actual=scale(h/2,reading)
    # The even part is minus twice the potential before its derivative is taken.
    const=Q(d0,2)-m1delta/(4*h)+2*p3
    even=plus(scale(-1,actual),(const,const))
    odd=plus(scale(2,actual),(-ps-const,-ps-const))
    folded=plus((ps,ps),even)
    # ps+even-odd = 2*(ps+const)-3*actual, with the shared reading kept.
    reflected=plus((2*(ps+const),2*(ps+const)),scale(-3,actual))
    return {"head":str(h),"base_cubic":str(p3),"funded_source":str(ps),"raw_reading":list(map(str,reading)),
            "half_head_times_reading":list(map(str,actual)),"odd_residue":list(map(str,odd)),
            "even_residue":list(map(str,even)),"after_turning_odd_part":list(map(str,reflected)),
            "after_dropping_odd_part":list(map(str,folded))}


def direct_cells(h, marks, passed):
    """Use integer-directed sums of the actual residue terms, with their true signs."""
    den=10**23
    low=[[0,0],[0,0]]
    widths=[[0,0],[0,0]]
    absolute=0
    cut=root_five_sixths(h)
    for d in range(1,2*h+1):
        mark=marks[d]
        if not mark:continue
        part=int(d>cut)
        for sign,t in ((1,2*h),(-1,h)):
            if d>t:continue
            r=t%d
            m=r*(d-r)
            numerator=mark*sign*m
            for i,(v,q) in enumerate(((numerator*(d-2*r),2*d*t*t),(-numerator*m,2*d*t**3))):
                floor,rem=divmod(den*v,q)
                low[part][i]+=floor
                widths[part][i]+=bool(rem)
        # Absolute bill of the high-shell difference, with no loss to cancellation at the same label.
        if part and 3*d>=4*h and 3*d<=5*h:
            assert d>h
            r=2*h%d
            m=r*(d-r)
            absolute+=den*abs(mark*m*((d-2*r)*2*h-m))//(2*d*(2*h)**3)
    out=[[interval(Q(low[k][i],den),Q(low[k][i]+widths[k][i],den)) for i in range(2)] for k in range(2)]
    total=[plus(out[0][i],out[1][i]) for i in range(2)]
    p3,ps=baseline(2*h,1,passed)
    ts=plus((ps,ps),plus(*total))
    retained=plus((ps,ps),plus(*out[1]))
    old=plus(*out[0])
    assert max(abs(old[0]),abs(old[1]))<=Q(15*cut**3,4*h*h)
    return {"head":h,"before_cut":cut,"retained_funded_value":list(map(str,retained)),
            "whole_funded_value":list(map(str,ts)),"discarded_signed_value":list(map(str,old)),
            "odd_residue":list(map(str,total[0])),"even_residue":list(map(str,total[1])),
            "outer_shell_unsigned_lower":str(Q(absolute,den)),"positive_source":str(ps)}


def direct_even_window(j, passed):
    h=j**4
    high=h+j*j
    s,t=2*h,2*high
    mu,_,_=sieve(t)
    marks=coefficients(mu,(2,3) if passed else ())
    def energy(end,n):
        if n>end: return Q(0)
        r=end%n
        return Q(r*r*(n-r)**2,4*n*end**2)
    def read(n):
        return sum((Q(marks[d],d)*min(1,Q(2*(n-d),n)) for d in range(1,n+1) if marks[d]),Q(0))
    integral=sum((Q(n,8 if n in (s,t) else 4)*read(n) for n in range(s,t+1)),Q(0))
    base=t*baseline(t,1,passed)[0]-s*baseline(s,1,passed)[0]
    cut=root_five_sixths(h)
    old=remaining=Q(0)
    for d in range(1,t+1):
        if marks[d]:
            amount=marks[d]*(energy(t,d)-energy(s,d)-energy(t,2*d)+energy(s,2*d))
            if d<=cut:old+=amount
            else:remaining+=amount
    assert integral==base+remaining+old
    cap=Q(15*(t-s)*cut**3,s*s)
    assert abs(old)<=cap
    return {"fourth_root":j,"passed":passed,"before_cut":cut,"physical_integral":str(integral),
            "known_source":str(base),"old_signed_change":str(old),"retained_with_source":str(base+remaining),
            "old_absolute_allowance":str(cap)}


def load_moments(binary, h):
    top=2*h
    rows=requested(top)
    if top<=1_000_000:
        m=direct(top,rows)
        raw,_,_=sieve(top)
        nodes={top//q for q in rows}
        keep={}
        unit=10**27
        low=error=0
        for d in range(1,top+1):
            if d%6 in (1,5) and raw[d]:
                div,rem=divmod(unit*raw[d],d)
                low+=div
                error+=bool(rem)
            if d in nodes: keep[d]=(Q(low,unit),Q(low+error,unit))
        U={q:keep[top//q] for q in rows}
        return m,U
    a=min(9_000_000,max(isqrt(top)+10,int(top**(2/3)/6)))
    b=min(7_000_000,max(isqrt(top)+17,int(top**(2/3)/8)))
    m=compiled(binary,top,a,rows)
    assert m==compiled(binary,top,b,rows,True)
    u=reciprocal_rows(binary,top,a,rows,False)
    v=reciprocal_rows(binary,top,b,rows,True)
    assert all(u[q][2]==v[q][2]==m[q][0] for q in rows)
    U={q:(max(u[q][0],v[q][0]),min(u[q][1],v[q][1])) for q in rows}
    assert all(l<=r for l,r in U.values())
    return m,U


def clock_votes(h, moments, U):
    top=2*h
    def seed(q):
        if q>top: return Q(0),Q(0)
        m=moments[q][0]
        before=moments.get(2*q,(0,))[0]
        a,b=U[q];c,d=U.get(2*q,(Q(0),Q(0)))
        price=Q(2*q,top)*(m-before)
        return 2*a-d-price,2*b-c-price
    single={}
    empty=(Q(0),Q(0))
    for _,q in sorted(scales(top),reverse=True):
        for p in (2,3):
            single[p,q]=plus(seed(q),scale(Q(1,p),single.get((p,q*p*p),empty)))
    sites=[q for _,q in scales(top) if q<=h]
    pairs=[(single[2,q],single[3,q]) for q in sites]
    return {"physical_sides_at_least_one":len(pairs),
            "both_positive":sum(a[0]>0 and b[0]>0 for a,b in pairs),
            "both_negative":sum(a[1]<0 and b[1]<0 for a,b in pairs),
            "sign_undecided_or_separate":sum(not(a[0]>0 and b[0]>0) and not(a[1]<0 and b[1]<0) for a,b in pairs),
            "single_four_at_head":list(map(str,single[2,1])),
            "single_nine_at_head":list(map(str,single[3,1]))}


def short_window(h, length, m, U, passed):
    """Price the integral on a short interval with the true band at its start."""
    top=2*h
    read=from_moments(top,m,U,1,passed)
    lo,hi=map(Q,read["raw_reading"])
    frames=list(scales(2*(h+length))) if passed else [(1,1)]
    def M(q):return m.get(q,(0,))[0]
    band=sum(p*(M(q)-M(2*q)) for p,q in frames if q<=top)
    def rough(n):return n-n//2-n//3+n//6
    def mass(a,b):return sum(p*(rough(b//q)-rough(a//q)) for p,q in frames if q<=b)
    change=mass(h,h+length)+mass(2*h,2*(h+length))
    right=Q(length,h*(h+length))
    lo+=min(0,(band-change)*right)
    hi+=max(0,(band+change)*right)
    area=scale(Q((h+length)**2-h*h,2),(lo,hi))
    p0=Q(read['base_cubic'])
    p1=baseline(2*(h+length),1,passed)[0]
    base=2*((h+length)*p1-h*p0)
    correction=plus(area,(-base,-base))
    return {"head":h,"length":length,"integral":list(map(str,area)),"funded_part":str(base),
            "change_of_even_residue":list(map(str,correction)),"exact_initial_band":band}


def shell_totals(top,m,U):
    rows=[0]*4
    low=high=Q(0)
    for p,q in scales(top):
        for j in range(4):rows[j]+=p**(2*j+1)*m[q][j]
        lo,hi=U[q];low+=lo/p;high+=hi/p
    return rows,(low,high)


def outer_sector(h,inputs):
    """The signed sum on one angular sector uses four aggregate moments."""
    a,b=8*h//5,5*h//3
    lm,lu=shell_totals(a,*inputs(a))
    rm,ru=shell_totals(b,*inputs(b))
    difference=[r-l for r,l in zip(rm,lm)]
    t=2*h
    constant=-Q(3,2)*difference[0]+Q(3,t*t)*difference[2]-Q(2,t**3)*difference[3]
    actual=plus((constant,constant),scale(Q(t,2),plus(ru,scale(-1,lu))))
    def rough(n):return n-n//2-n//3+n//6
    length=b-a
    # Beyond 3, the reciprocal prime squares total at most (1/25+1/36)*2.
    min_marks=rough(b)-rough(a)-((61*length+449)//450)-isqrt(b)
    price=Q(3,250)*max(0,min_marks)
    base=baseline(t,1,True)[1]
    assert price>base
    return {"head":h,"left_excluded":a,"right_included":b,"unsigned_minimum_marks":min_marks,
            "unsigned_cost_lower":str(price),"entire_positive_source":str(base),
            "signed_sector":list(map(str,actual)),"moments":list(map(str,difference))}


def finite_panel(h,m,U):
    unit=10**22
    U={q:(Q((lo*unit)//1,unit),Q(-((-hi*unit)//1),unit)) for q,(lo,hi) in U.items()}
    top=2*h
    stages={str(q):from_moments(top,m,U,q,True) for q in (1,4,9,36) if q<=top}
    raw=from_moments(top,m,U,1,False)
    hit=tuple(map(Q,stages['1']['half_head_times_reading']))
    source=Q(stages['1']['funded_source'])
    inverses={}
    for key in ("half_head_times_reading","odd_residue","even_residue","funded_source"):
        def value(row):
            item=row[key]
            return (Q(item),Q(item)) if isinstance(item,str) else tuple(map(Q,item))
        returned=(Q(0),Q(0))
        for q,c in ((1,1),(4,-2),(9,-3),(36,6)):
            if str(q) in stages: returned=plus(returned,scale(c,value(stages[str(q)])))
        own=value(raw)
        assert max(own[0],returned[0])<=min(own[1],returned[1])
        inverses[key]=list(map(str,returned))
    cut=root_five_sixths(h)
    allowance=Q(0) if h==1 else Q(15*cut**3,4*h*h)
    projected=hit[0]-allowance,hit[1]+allowance
    return {"head":h,"raw":raw,"passed":stages["1"],"single_clocks":clock_votes(h,m,U),"four_reading_inverses":inverses,"old_absolute_allowance":str(allowance),
            "retained_funded_value_enclosure":list(map(str,projected)),
            "auditable_paid_fraction_lower":str(projected[0]/source) if source else None}


def audit(binary=(), supplied=None):
    hlist=[8,13,5**4,13**4,25**4]
    raw,_,_=sieve(2*max(hlist))
    m0=coefficients(raw,())
    m1=coefficients(raw,(2,3))
    small=[]
    for h in hlist:
        m,U=load_moments((),h)
        for on,marks in ((False,m0),(True,m1)):
            result=direct_cells(h,marks,on)
            dual=from_moments(2*h,m,U,1,on)
            for k in ("odd_residue","even_residue"):
                a,b=map(Q,result[k]);c,d=map(Q,dual[k])
                assert max(a,c)<=min(b,d)
            small.append({"passed":on,**result})
    out={"cell_identities_checked":corner_checks(),"direct_cases":small,
         "direct_even_windows":[direct_even_window(j,passed) for j in (1,2,3,5) for passed in (False,True)]}
    if binary or supplied:
        panel=[]
        get=supplied if supplied else lambda h:load_moments(binary,h)
        for h in (432_000_000_000,*(j**12 for j in range(1,11))):
            m,U=get(h)
            panel.append(finite_panel(h,m,U))
            j=isqrt(isqrt(h))
            if j**4==h:
                win=short_window(h,j*j,m,U,True)
                cut=root_five_sixths(h)
                cap=Q(15*(2*j*j)*cut**3,4*h*h)
                if j==1:
                    assert direct_even_window(1,True)["retained_with_source"]=="3/2"
                    lower=Q(3,2)
                else:lower=Q(win["integral"][0])-cap
                assert lower>0
                panel[-1]["even_only_fourth_window"]={"root":j,"length":j*j,
                    "old_allowance":str(cap),"retained_funded_lower":str(lower)}
            if h==432_000_000_000:
                out["same_input_windows"]=[short_window(h,1_000_000,m,U,on) for on in (False,True)]
                assert Q(out["same_input_windows"][0]["integral"][1])<0<Q(out["same_input_windows"][1]["integral"][0])
                old=tuple(map(Q,panel[-1]["raw"]["raw_reading"]))
                other=[]
                for p in (929501,929507):
                    assert all(p%i for i in range(2,isqrt(p)+1))
                    assert h<p*p<2*h and p**4>2*h
                    increment=(2-Q(p*p,h))/p
                    result=plus(old,(increment,increment))
                    assert increment>0 and result[1]<0
                    other.append({"prime":p,"active_first_return":str(increment),
                                  "actual_single_clock":list(map(str,result))})
                out["both_other_directions_fail_here"]=other
        out["independent_large_panels"]=panel
        def endpoint(t):
            assert t%2==0
            return get(t//2)
        out["outer_sector"]=outer_sector(10**12,endpoint)
        assert all(Q(u["retained_funded_value_enclosure"][0])>0 for u in panel)
        contiguous=[]
        for a,b in zip(panel[1:],panel[2:]):
            def integral(row):
                s=row["passed"]
                return plus((2*row["head"]*Q(s["base_cubic"]),)*2,
                            scale(-row["head"],tuple(map(Q,s["even_residue"]))))
            bounds=plus(integral(b),scale(-1,integral(a)))
            contiguous.append({"left":a["head"],"right":b["head"],"paid_integral":list(map(str,bounds))})
        out["consecutive_twelfth_windows"]=contiguous
    return out


if __name__=="__main__":
    print(json.dumps(audit(sys.argv[1:]),indent=2))
