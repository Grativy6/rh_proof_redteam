"""Exact rough-core square matrices, integer cutoffs and distinct-prime omission caps."""
from array import array
from bisect import bisect_right
from fractions import Fraction as Q
from itertools import combinations
from math import comb, gcd, prod
import json


def tables(limit):
    mu=array('b',[0])*(limit+1)
    depth=bytearray(limit+1)
    largest=array('I',[0])*(limit+1)
    primes=[]
    mu[1]=1
    for n in range(2,limit+1):
        if not largest[n]:
            primes.append(n)
            largest[n]=n
            mu[n]=-1
            depth[n]=int(n>3)
        for p in primes:
            k=n*p
            if k>limit:
                break
            largest[k]=largest[n]
            depth[k]=depth[n]+int(p>3 and n%p!=0)
            if n%p==0:
                break
            mu[k]=-mu[n]
    return mu,depth,largest,primes


def free_count(v):
    return v-v//2-v//3+v//6


def matrix(mu, primes, side):
    X=side*side
    active=[(i,mu[i]) for i in range(1,side+1) if gcd(i,6)==1 and mu[i]]
    mass=sum(v for _,v in active)
    harmonic=sum((Q(v,i) for i,v in active),Q(0))
    out=hits=hit_mass=0
    for i,a in active:
        for j,b in active:
            den=i*j
            q,r=divmod(X,den)
            out+=a*b*free_count(q)
            if r==0 and gcd(q,6)==1:
                hits+=1
                hit_mass+=a*b
    true_sum=sum(mu[n] for n in range(1,X+1) if gcd(n,6)==1)
    assert 2*mass-out==true_sum and (side==1 or hit_mass==0)
    rank_one=Q(X,3)*harmonic**2
    centered=out-rank_one
    low=(100*centered)//1
    assert Q(low,100)<=centered<Q(low+1,100)
    I=[(i,v) for i,v in active if 47*side<=100*i<=49*side]
    J=[(i,v) for i,v in active if 39*side<=100*i<=40*side]
    prime_set=set(primes[:bisect_right(primes,side)])
    same_primes=[i for i,_ in I if i in prime_set]
    prime_form=len(same_primes)**2 - Q(X,3)*sum((Q(1,i) for i in same_primes),Q(0))**2
    real_I=sum(v for _,v in I)**2-Q(X,3)*sum((Q(v,i) for i,v in I),Q(0))**2
    assert (not same_primes or prime_form < -Q(1,3)*len(same_primes)**2)
    if side==1024:
        assert same_primes==[487,491,499] and prime_form < -3 and -Q(1,40000)<real_I<0
    short=[0]*(5*side+6)
    for k in range(1,len(short)):
        short[k]=short[k-1]+(mu[k] if gcd(k,6)==1 else 0)
    assert sum(a*free_count(side//i) for i,a in active)==1
    for j in range(1,side+1):
        u=X//j
        if u<5*(side+1):
            assert sum(a*(free_count(u//i)-1) for i,a in active)==1-short[u]
    union=I+J
    direct=sum(a*b*free_count(X//(i*j)) for i,a in union for j,b in union)
    U,V=sum(v for _,v in I),sum(v for _,v in J)
    assert direct==(U+2*V)**2-2*V**2
    # Change only the signs on the very same active indices of these two blocks.
    unsigned_test=len(I)**2 - 4*len(I)*len(J) + 2*len(J)**2
    def restricted(threshold):
        return sum(a*b*free_count(threshold//(i*j)) for i,a in active for j,b in active)
    if side>1:
        for shift in (-side+1,-1,1,side):
            m=X+shift
            left=restricted(m)-out
            lower,upper=sorted((m,X))
            new=sum(mu[k] for k in range(lower+1,upper+1) if gcd(k,6)==1)
            assert left==(-new if m>X else new) and abs(left)<=abs(shift)
    return {'side':side,'core_walk':true_sum,'known_side_walk':mass,'integer_form':out,
            'centered_form_hundredths_enclosure':[low,low+1],
            'exact_boundary_pairs':hits,'signed_boundary':hit_mass,
            'actual_prime_subblock':{'primes':same_primes, 'form_hundredths_upper':int(-(-100*prime_form//1)),
                                     'whole_I_millionths_floor':int(1000000*real_I//1)},
            'two_blocks':{'sizes':[len(I),len(J)],'actual_sums':[U,V],
                          'actual_form':direct,'changed_signs_form':unsigned_test}}


def depth_and_fresh(mu,depth,largest,primes,side):
    X=side*side
    hist=[0]*(1+max(depth[1:X+1]))
    for k in range(1,X+1):
        hist[depth[k]]+=1
    def cap(d):
        return sum(num*comb(i,d) for i,num in enumerate(hist) if i>=d)
    d=1
    while cap(d)>side:
        d+=1
    # Compute the action both by prime-depth histogram and, at small sides,
    # by the literal sum of floors over distinct sets of prime divisors.
    if side<=8:
        pool=[p for p in primes if 3<p<=X]
        for order in range(1,min(d+2,len(pool)+1)):
            assert cap(order)==sum(X//prod(group) for group in combinations(pool,order))
    retained=omitted_signed=omitted_absolute=old=new=0
    after_five=after_five_divided=0
    for n in range(1,X+1):
        if gcd(n,6)!=1 or not mu[n]:
            continue
        if n%5:
            after_five+=mu[n]
            if n<=X//5:
                after_five_divided+=mu[n]
        if depth[n]<d:
            retained+=mu[n]
        else:
            omitted_signed+=mu[n]
            omitted_absolute+=1
        if largest[n]>side:
            new+=mu[n]
        else:
            old+=mu[n]
    assert abs(omitted_signed)<=omitted_absolute<=cap(d)<=side
    assert retained+omitted_signed==old+new==after_five-after_five_divided
    prime_count=bisect_right(primes,side)
    if side>=3:
        independent=-sum(mu[a]*(bisect_right(primes,X//a)-prime_count)
                         for a in range(1,side+1) if gcd(a,6)==1)
        assert independent==new
    return {'side':side,'square':X,'first_omitted_depth':d,'tuple_cap':cap(d),
            'previous_cap':cap(d-1),'actual_omitted_count':omitted_absolute,
            'actual_omitted_signed':omitted_signed,'retained_signed':retained,
            'small_primes_only_signed':old,'one_new_prime_signed':new,
            'true_signed':old+new, 'opening_five':{'R30_at_square':after_five,'R30_at_divided_argument':after_five_divided}}


def signed_unpaid(mu):
    side=30
    source=[n for n in range(1,side+1) if gcd(n,6)==1 and mu[n]]
    old=sum(mu[n] for n in source)
    rows=[]
    for edge in (900,960,961,1084,1085,1147):
        form=sum(mu[i]*mu[j]*free_count(edge//(i*j)) for i in source for j in source)
        real=sum(mu[n] for n in range(1,edge+1) if gcd(n,6)==1)
        missing=[(i,j) for i in range(side+1,edge//(side+1)+1) for j in range(side+1,edge//i+1)
                 if gcd(i*j,6)==1 and mu[i] and mu[j]]
        unpaid=sum(mu[i]*mu[j]*free_count(edge//(i*j)) for i,j in missing)
        assert real-(2*old-form)==unpaid
        rows.append({'threshold':edge,'true':real,'inherited':2*old-form,'unpaid':unpaid,'pairs':missing})
    assert [r['unpaid'] for r in rows]==[0,0,1,1,-1,1]
    return rows


def variance_control(modulus):
    phi=sum(gcd(k,modulus)==1 for k in range(1,modulus+1))
    total=count=0
    for k in range(modulus):
        if k and gcd(k,modulus)==1:
            count+=1
        v=modulus*count-phi*k
        total+=3*v*v-3*phi*v+phi*phi
    moment=Q(total,3*modulus**3)
    primes=[p for p in (2,3,5,7,11,13) if modulus%p==0]
    assert prod(primes)==modulus
    assert moment==Q(2**len(primes)*phi,12*modulus)
    return str(moment)


def audit():
    sides=(3,5,8,16,35,64,127,128,256,512,1024,1536)
    mu,depth,largest,ps=tables(max(sides)**2 + max(sides))
    squares=[depth_and_fresh(mu,depth,largest,ps,j) for j in sides]
    matrices=[matrix(mu,ps,j) for j in (3,5,35,64,127,128,256,512,1024,1536)]
    assert any(v['exact_boundary_pairs']>0 and v['signed_boundary']==0 for v in matrices)
    assert any(v['two_blocks']['changed_signs_form']<0 for v in matrices)
    moments={str(P):variance_control(P) for P in (2,6,30,210,2310,30030)}
    assert Q(moments['30'])/Q(moments['6'])==Q(8,5)
    return {'squares':squares,'matrices':matrices,'continuous_period_variance':moments,'first_unpaid_products':signed_unpaid(mu)}


if __name__=='__main__':
    print(json.dumps(audit(),indent=2))
