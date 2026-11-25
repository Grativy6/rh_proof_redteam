"""Integer experiments for the finite head, Möbius octave and rough-product account."""
from array import array
from collections import defaultdict
from fractions import Fraction
from math import gcd, lcm, prod
import json

SCALE = 10**12


def sieve(limit):
    mu = array('b', [0]) * (limit+1)
    depth = bytearray(limit+1)
    composite = bytearray(limit+1)
    primes = []
    mu[1] = 1
    for n in range(2, limit+1):
        if not composite[n]:
            primes.append(n)
            mu[n], depth[n] = -1, 1
        for p in primes:
            k = p*n
            if k > limit:
                break
            composite[k] = 1
            if n % p == 0:
                break
            mu[k], depth[k] = -mu[n], depth[n]+1
    return mu, depth, primes


def direct_profile(mu, h, tick):
    nu = [mu[n]-(mu[n//2] if tick and n % 2 == 0 else 0) for n in range(h+1)]
    t = int(not tick)
    slope = sum(Fraction(nu[d], d) for d in range(1,h+1))
    mass = 2*t+sum(nu[1:])
    b = (mass-Fraction(5*h+1, 2)*slope)/h
    a = slope-b
    c = {d:Fraction(-nu[d]) for d in range(1,h+1)}
    for j,rate in ((2,a), (3,b)):
        for d in range(j*h+1,(j+1)*h+1):
            c[d] = rate*Fraction(d,h)
    assert sum(c.values()) == 2*t and sum(v/d for d,v in c.items()) == 0
    assert max(abs(v) for v in c.values()) <= 40
    def reading(k):
        return sum(v*Fraction(k%d, d) for d,v in c.items())
    def true(k):
        return int(k == 1 if tick else k >= 1)
    assert all(reading(k)==true(k) for k in range(h+1))
    for k in range(h+1,2*h+1):
        count = sum(mu[n]-(mu[n//2] if tick and n%2==0 else 0) for n in range(h+1,k+1))
        assert true(k)-reading(k)==count
    if h <= 3:
        period=lcm(*c)
        assert sum(reading(k) for k in range(period))==period*t
    return c


def upper_depth(head, primes):
    primorial=1
    count=0
    for p in primes:
        if p < 5:
            continue
        if (p*primorial)**2 > head:
            break
        primorial *= p
        count += 1
    return count,primorial


def price_interval(value, terms):
    return [value, value+terms]


def prices(mu, depth, primes, h):
    max_depth,primorial=upper_depth(h,primes)
    running={key:0 for key in ('all','rough','rough_diagonal','absolute','depth_one','kept','deep','deep_absolute')}
    costs=dict.fromkeys(running, 0)
    for k in range(h+1,2*h+1):
        v=mu[k] if gcd(k,6)==1 else 0
        running['all']+=mu[k]
        running['rough']+=v
        running['rough_diagonal']+=v*v
        running['absolute']+=abs(v)
        running['depth_one']+=v if depth[k] <= 1 else 0
        if depth[k] <= max_depth:
            running['kept']+=v
        else:
            running['deep']+=v
            running['deep_absolute']+=abs(v)
        den=k*(k+1)
        for key,partial in running.items():
            energy=partial if key=='rough_diagonal' else partial**2
            costs[key]+=SCALE*energy//den
    assert running['rough']==running['kept']+running['deep']
    return {'H':h, 'depth':max_depth, 'primorial':primorial,
            'rough_signed_increment':running['rough'], 'rough_squarefree_count':running['absolute'],
            'omitted_squarefree_count':running['deep_absolute'],
            'scaled_cost_intervals':{key:price_interval(v,h) for key,v in costs.items()}}


def check_products(mu,h):
    # Group off-diagonal pairs by the product remaining after the common square is removed.
    buckets=defaultdict(Fraction)
    walk=count=0
    exact=diagonal=Fraction(0)
    for b in range(h+1,2*h+1):
        mb=mu[b] if gcd(b,6)==1 else 0
        walk+=mb
        count+=mb*mb
        exact+=Fraction(walk*walk,b*(b+1))
        diagonal+=Fraction(count,b*(b+1))
        if not mb:
            continue
        for a in range(h+1,b):
            if not mu[a] or gcd(a,6)!=1:
                continue
            g=gcd(a,b)
            left,right=a//g,b//g
            label=left*right
            assert mu[a]*mb==mu[label] and gcd(left,right)==1
            buckets[label]+=2*(Fraction(1,b)-Fraction(1,2*h+1))
    assert exact==diagonal+sum(mu[m]*v for m,v in buckets.items())
    return {'H':h,'signed_cost':str(exact),'diagonal':str(diagonal),
            'positive_products':sum(mu[m]==1 for m in buckets),
            'negative_products':sum(mu[m]==-1 for m in buckets)}


def audit():
    heads=[2**e for e in range(4,21,2)]+[3*2**(e-1) for e in range(4,21,2)]
    mu,depth,primes=sieve(max(2*max(heads),4*96**2))
    for h in (1,2,3,6,18,32,64):
        for tick in (False,True):
            direct_profile(mu,h,tick)
    assert mu[5]*mu[7]==mu[55]*mu[77]==mu[35]==1
    assert mu[19]*mu[35]==mu[665]==-1
    return {'scale':SCALE,'interval_convention':'both rational endpoints divided by scale',
            'physical_profile_controls':'both targets at heads 1,2,3,6,18,32,64; complete periods at heads through 3',
            'product_controls':[check_products(mu,h) for h in (4,18,44,96)],
            'windows':[prices(mu,depth,primes,h) for h in sorted(heads)]}


if __name__=='__main__':
    print(json.dumps(audit(),indent=2))
