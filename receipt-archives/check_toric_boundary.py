"""Integer and rational checks for the conductor-137 Hecke boundary."""

from fractions import Fraction as Q
from math import comb, factorial, gcd, isqrt


def atan_interval(reciprocal, even_order=16):
    """Alternating expansion through two consecutive indices."""
    x = Q(1, reciprocal)
    upper = sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(even_order+1))
    lower = upper - x**(2*even_order+3)/(2*even_order+3)
    return lower, upper


def exp_minus_interval(lo, hi, digits=24):
    """Bounds exp(-u) for lo <= u <= hi, then rounds endpoints outwards."""
    def partial(x,n):
        return sum((-x)**j/factorial(j) for j in range(n+1))
    a, b = partial(hi,27), partial(lo,26)
    scale = 10**digits
    return Q((scale*a).__floor__(),scale), Q((scale*b).__ceil__(),scale)


def base_interval():
    a,b = atan_interval(5)
    c,d = atan_interval(239)
    lo,hi = 16*a-4*d,16*b-4*c
    scale = 10**24
    root = isqrt(7*scale**2)
    return exp_minus_interval(lo/Q(root+1,scale),hi/Q(root,scale))


def factor(n):
    factors = {}
    p = 2
    while p*p <= n:
        while n%p == 0:
            factors[p] = factors.get(p,0)+1
            n //= p
        p += 1 if p == 2 else 2
    if n>1:
        factors[n] = 1
    return factors


def ideal_divisor_sum(u,v):
    """Sum of norms of divisors of (u+v*sqrt(7)) for a totally positive input."""
    norm = u*u-7*v*v
    assert norm>0 and u>0
    common = factor(gcd(u,v))
    total = 1
    for p,e in factor(norm).items():
        if p in (2,7):
            parts = [(p,e)]
        elif pow(7,(p-1)//2,p)==p-1:
            assert e%2==0
            parts = [(p*p,e//2)]
        else:
            a = common.get(p,0)
            parts = [(p,a),(p,e-a)]
        for prime_norm,exponent in parts:
            total *= (prime_norm**(exponent+1)-1)//(prime_norm-1)
    return total


def principal_value_interval(cut=4):
    qlo,qhi = base_interval()
    lo=hi=Q(1,168)
    for u in range(1,cut+1):
        for v in range(-u,u+1):
            if 7*v*v >= u*u:
                continue
            exponent = 12*u+7*v
            coefficient = Q(ideal_divisor_sum(u,v),28)
            least,greatest = coefficient*qlo**exponent,coefficient*qhi**exponent
            if v%2:
                lo,hi=lo-greatest,hi-least
            else:
                lo,hi=lo+least,hi+greatest
    # For u>cut use |coefficient sum| <= u^5/14 and exp(-9)<1/4096.
    assert sum(Q(9**j,factorial(j)) for j in range(13))>4096
    first=cut+1
    ratio=Q((first+1)**5,first**5*4096)
    tail=Q(first**5,14*4096**first)/(1-ratio)
    return lo-tail,hi+tail


def check_kernel():
    # Constant-frequency integral / int sin(theta)^(2t) dtheta. Compare the
    # finite cosine expansion at integer t to the gamma-function recurrence.
    for m in range(12):
        num_derivative=Q((-1)**(m+1))
        for j in range(m+1):
            num_derivative *= Q(-j if j else 1,j+1)
        assert num_derivative==-Q(1,m+1)
        for t in range(1,16):
            ratio=Q((-1)**(m+1))
            for j in range(m+1):
                ratio*=Q(t-j,t+j+1)
            direct=Q((-1)**(m+1)*comb(2*t,t+m+1),comb(2*t,t))
            assert ratio==direct
    assert Q(1,28)*Q(7,137)*Q(4,7)==Q(1,959)


def check_arithmetic():
    b=Q(1,168)
    v=Q(1,137**2)
    def val17(x):
        def exponent(n):
            assert n
            a=0
            while n%17==0:
                n//=17
                a+=1
            return a
        return exponent(x.numerator)-exponent(x.denominator)
    assert [val17(x) for x in [b,b*v,b*(1+33*v),b*(1-v)]]==[0,0,1,1]
    assert 5**2+7*4**2==137
    trace=Q(2*(5**2-7*4**2),137)
    assert 1-trace/137+Q(1,137)==Q(19080,18769)


if __name__=="__main__":
    check_kernel()
    check_arithmetic()
    lo,hi=principal_value_interval()
    # Endpoints are decimal rationals. The enclosure above uses no floating point.
    a,b=Q(595240410576,10**14),Q(595240410577,10**14)
    assert a<lo<=hi<b,(float(lo),float(hi))
    print("Principal normalized continued value is between 0.00595240410576 and 0.00595240410577.")
    print("Zero-mode slope factor: pi^2*log(8+3*sqrt(7))/959 before the derivative weights.")
    print("Class and character cusp valuations at 17: (0,0,1,1) for the two types of each.")
