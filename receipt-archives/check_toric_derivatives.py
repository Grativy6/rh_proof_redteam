"""Exact checks of the raising operator, the CM correction, and cusp denominators."""

from fractions import Fraction as Q
from math import comb, prod


def rising(k, n):
    return prod(range(k,k+n))


# Elements a+b*tau, tau^2=tau-2, are represented by rational pairs.
def add(x,y):
    return (x[0]+y[0],x[1]+y[1])


def scale(x,m):
    return (x[0]*m,x[1]*m)


def mul(x,y):
    a,b=x
    c,d=y
    return (a*c-2*b*d, a*d+b*c+b*d)


def conj(x):
    return (x[0]+x[1],-x[1])


def inverse(x):
    star=conj(x)
    norm=mul(x,star)
    assert norm[1]==0 and norm[0]
    return scale(star,1/Q(norm[0]))


def power(x,n):
    if n < 0:
        return power(inverse(x),-n)
    y=(1,0)
    while n:
        if n%2:
            y=mul(y,x)
        x=mul(x,x)
        n//=2
    return y


def check_raising():
    tau=(0,1)
    delta=add(tau,scale(conj(tau),-1))
    lam=scale(power(tau,-2),2)
    c=inverse(add(lam,(-1,0)))
    assert c==scale(mul(tau,inverse(delta)),-1)
    assert mul(add(lam,(-1,0)),inverse(delta))==scale(inverse(tau),-1)
    e2_factor=mul(power(tau,2),inverse(add((2,0),scale(power(tau,2),-1))))
    assert e2_factor==(Q(-4,7),Q(1,7))  # (-7+sqrt(-7))/14
    assert mul(add(e2_factor,(2,0)),conj(add(e2_factor,(2,0))))==(Q(16,7),0)
    checked=0
    for k in (4,6,10):
        # Coefficients of t^(m-j) D^j after m raising operators.
        recurrence=[1]
        for m in range(11):
            direct=[comb(m,j)*rising(k+j,m-j) for j in range(m+1)]
            assert recurrence==direct
            for a,b in [(1,1),(-2,3),(4,-1)]:
                x=add((a,0),scale(tau,b))
                result=(0,0)
                for j,coef in enumerate(direct):
                    derivative=scale(power(x,-k-j),(-b)**j*rising(k,j))
                    result=add(result,scale(mul(power(delta,j),derivative),coef))
                assert result==scale(mul(power(conj(x),m),power(x,-k-m)),rising(k,m))
                checked+=1
            next_row=[0]*(m+2)
            for j,value in enumerate(recurrence):
                next_row[j]+=(k+m+j)*value
                next_row[j+1]+=value
            recurrence=next_row
    return checked


def theta_log(kind,limit=96):
    # Expansion variable x=q^(1/8); remove the leading coefficient and monomial.
    series=[0]*(limit+1)
    shift=1 if kind==2 else 0
    series[0]=1
    for n in range(1,limit+1):
        exponent=4*n*(n+1) if kind==2 else 4*n*n
        if exponent>limit:
            break
        series[exponent]=1 if kind==2 else 2*((-1)**n if kind==4 else 1)
    # x*d(log theta)/dx, computed by ordinary series division.
    deriv=[Q(0)]*(limit+1)
    for r in range(1,limit+1):
        deriv[r]=r*series[r]-sum(series[j]*deriv[r-j] for j in range(1,r+1))
    deriv[0]=shift
    return [v/ Q(4) for v in deriv]  # D log(theta^2) = (x/4) theta'/theta


def check_cusp_costs():
    for kind in (2,3,4):
        U=theta_log(kind)
        assert U[0] == (Q(1,4) if kind==2 else 0)
        assert all((4*z).denominator==1 for z in U)
        residual=[Q(r,8)*a-sum(U[j]*U[r-j] for j in range(r+1)) for r,a in enumerate(U)]
        assert all((16*z).denominator==1 for z in residual)
        assert all((8*Q(1,2)*z).denominator==1 for z in U)
    actual={2:(132,36),3:(12,0),7:(60,18),11:(12,0),137:(120,12)}
    release={2:(252,48),3:(12,0),7:(120,30),11:(12,0),137:(480,60)}
    for p,(constant,rate) in actual.items():
        assert constant<=release[p][0] and rate<=release[p][1]
    return actual


if __name__=="__main__":
    print("Termwise raising identities checked:",check_raising())
    print("Constant and per-derivative exponents for the normalized twelfth power:",check_cusp_costs())
