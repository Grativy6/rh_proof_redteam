"""Exact classwise Fourier coefficients in Q(sqrt(839)); FLINT is optional."""

import argparse
from fractions import Fraction
from functools import cache
from math import comb, gcd, isqrt

D = 839
DISCRIMINANT = 4*D
UNIT_UPPER = 1680  # 840+29*sqrt(839) is positive, norm one and <1680.


def divisors(n):
    return sorted({b for a in range(1,isqrt(n)+1) if n%a == 0 for b in (a,n//a)})


def equivalent(left,right):
    """Test (m,u+sqrt(D)) ~ (n,v+sqrt(D)) by a bounded norm equation."""
    m,u=left
    n,v=right
    index=m*n
    generators=[(index,0),(m*v,-m),(n*u,n),(u*v-D,v-u)]
    minors=[abs(x*z-y*w) for j,(x,y) in enumerate(generators)
            for w,z in generators[:j]]
    assert gcd(*minors)==index
    for y in range(isqrt(index*UNIT_UPPER//D)+1):
        for square in (D*y*y+index,D*y*y-index):
            if square < 0:
                continue
            x=isqrt(square)
            if x*x!=square:
                continue
            for signed in {x,-x}:
                if all((a*y-b*signed)%index==0 for a,b in generators):
                    return True
    return False


def representatives():
    reps=[]
    for m in range(1,isqrt(D)+1):
        for u in range(m):
            if (u*u-D)%m==0 and all(not equivalent((m,u),other) for other in reps):
                reps.append((m,u))
    return reps


def coefficients(reps, upto=3):
    @cache
    def class_of(m,t):
        matches=[i for i,other in enumerate(reps) if equivalent((m,t),other)]
        assert len(matches)==1
        return matches[0]

    rows={}
    for n in range(1,upto+1):
        rows[n]={k:[0]*len(reps) for k in (2,8)}
        bound=isqrt(D*n*n)
        for u in range(-bound,bound+1):
            for c in divisors(gcd(abs(u),n)):
                a,b=u//c,n//c
                for m in divisors(D*b*b-a*a):
                    if m==1:
                        roots=[0]
                    elif gcd(b,m)==1:
                        t=a*pow(b,-1,m)%m
                        roots=[t] if (t*t-D)%m==0 else []
                    else:
                        roots=[t for t in range(m) if (a-b*t)%m==0 and (t*t-D)%m==0]
                    for t in roots:
                        ix=class_of(m,t)
                        for k in (2,8):
                            rows[n][k][ix]+=(c*c*m)**(k-1)
    return rows


def total_zeta(k):
    bern=[Fraction(1)]
    for n in range(1,k+1):
        bern.append(-sum(comb(n+1,j)*bern[j] for j in range(n))/(n+1))
    total=Fraction(0)
    for a in range(1,DISCRIMINANT,2):
        if a%D==0:
            continue
        chi=(1 if a%4==1 else -1)*(1 if pow(a,(D-1)//2,D)==1 else -1)
        total+=chi*sum(comb(k,j)*bern[j]*a**(k-j)*DISCRIMINANT**j for j in range(k+1))
    return bern[k]*total/(4*DISCRIMINANT*k*k)


def quadratic_forms():
    out=[]
    for a in range(1,isqrt(D//3)+1):
        for b in range(-a,a+1):
            if (b*b+D)%(4*a):
                continue
            c=(b*b+D)//(4*a)
            if a<=c and not ((a==c or abs(b)==a) and b<0) and gcd(a,gcd(b,c))==1:
                out.append((a,b,c))
    return out


def check_cm_certificate():
    from flint import arb, acb, acb_poly, ctx, fmpz_poly
    ctx.prec=2304
    forms=quadratic_forms()
    integer=fmpz_poly.hilbert_class_poly(-D)
    interval=acb_poly([1])
    for a,b,_ in forms:
        tau=acb(-b,arb(D).sqrt())/(2*a)
        interval*=acb_poly([-tau.modular_j(),1])
    assert len(interval)==len(integer)==len(forms)+1
    assert [v.unique_fmpz() for v in interval]==list(integer)
    assert int(integer[0])%3==2
    print("CM class polynomial: degree 33, constant 2 modulo 3; all coefficients isolated by balls.")


def check():
    assert all(D%i for i in range(2,isqrt(D)+1))
    assert 840**2-29**2*D==1 and 29**2-D==2
    assert D%16==7 and (-D)%3==1 and D%37==25 and 6**2%37==36
    reps=representatives()
    assert reps==[(1,0),(5,2),(5,3)]
    rows=coefficients(reps)
    k2=[Fraction(a,240) for a in rows[1][2]]
    assert rows[2][2]==[9*a for a in rows[1][2]] and rows[3][2]==[28*a for a in rows[1][2]]
    k8=[Fraction(b-216*a,354240-216*960) for a,b in zip(rows[1][8],rows[2][8])]
    for a,c,third in zip(rows[1][8],k8,rows[3][8]):
        cusp=a-960*c
        assert 61543680*c-3348*cusp==third
    for k,partials,residue in [(2,k2,1),(8,k8,2)]:
        assert sum(partials)==total_zeta(k)
        assert all(a.denominator%3==0 and a.denominator%9 for a in partials)
        assert sum(partials).denominator%3
        for a in partials:
            value=3*a/DISCRIMINANT**(k//2)
            assert value.numerator*pow(value.denominator,-1,3)%3==residue
        print(f"k={k}, partial zeta / 4:",", ".join(map(str,partials)),"sum:",sum(partials))
    assert len(quadratic_forms())==33
    base_classes=3*33
    ring_classes=(37-1)//4*base_classes
    assert ring_classes==891 and ring_classes==3**4*11
    print("CM class number 99; ring-class group size 891; residual Fourier rank 11.")


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cm-certificate",action="store_true",
                        help="also recompute the class polynomial using python-flint")
    args=parser.parse_args()
    check()
    if args.cm_certificate:
        check_cm_certificate()
