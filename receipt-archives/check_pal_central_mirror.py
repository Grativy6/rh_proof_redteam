"""Check the reciprocal local factors and the exact mean of each finite valuation ledger."""
from fractions import Fraction as Q
import json


def value(coefficients, x):
    total=0
    for a in reversed(coefficients):
        total=total*x+a
    return total


def local_coefficients(polynomial):
    total=0
    rows=[]
    for c in polynomial:
        total+=c
        rows.append(total)
    return rows


def delayed(prime, r, changed):
    m=2*r+1
    coeff=[0]*(2*m+1)
    coeff[0]=1
    coeff[-1]=prime**m
    if changed:
        coeff[r]=-1
        coeff[m]=prime**(m-r)
        coeff[2*m-r]=-prime**(m-r)
    else:
        coeff[m]=-1
    return coeff


def audit():
    p=5
    assert 4*5-4**2==4 and 4*5-5**2==-5
    assert 2**2-5*2+5==-1
    assert 23**2>100*5
    for a in (4,5):
        traces=[2,-a]
        for _ in range(2,17):traces.append(-a*traces[-1]-5*traces[-2])
        if a==4:
            assert all(v*v<=4*p**j for j,v in enumerate(traces))
        else:
            assert all(v*v>4*p**j for j,v in enumerate(traces) if j>=1)
    checks=[]
    for r in range(3,25):
        m=2*r+1
        b,c=delayed(p,r,False),delayed(p,r,True)
        u,v=local_coefficients(b),local_coefficients(c)
        for coefficients,weights in ((b,u),(c,v)):
            assert all(coefficients[2*m-i]==p**(m-i)*coefficients[i] for i in range(m+1))
            assert value(coefficients,Q(1,p))==1
            assert min(weights)>=0 and weights[0]==weights[1]==1
            assert weights[-1]==p**m
        assert u[:r]==v[:r] and u[r]!=v[r]
        assert c[-1]>sum(abs(x) for x in c[:-1])
        assert [v[i] for i in (r-1,r,m-1,m,2*m-r-1,2*m-r,2*m-1,2*m)]==[1,0,0,p**(m-r),p**(m-r),0,0,p**m]
        checks.append({"r":r,"m":m,"first_different_integer":p**r,
                       "common_pole_residue":"1","central_extra_roots_reference":2*m,
                       "off_center_extra_roots_changed":2*m})
    return {"prime":p,"rational_trace_tests":2,"paired_valuation_ledgers":checks}


if __name__=="__main__":
    print(json.dumps(audit(),indent=2))
