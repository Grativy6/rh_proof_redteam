"""Build disjoint reciprocal-boundary sign packets on genuine rough squarefree labels."""
from bisect import bisect_right
from fractions import Fraction as Q
from math import gcd, isqrt
import json

from check_pal_growth_windows import sieve


def make_packets(H, mu):
    L=isqrt(H)
    X=H*H
    begin=(38*H+99)//100
    end=44*H//100
    def labels(first,last):
        return [n for n in range(first+1,last+1) if mu[n] and gcd(n,30)==1]
    support={}
    packets=[]
    for u in range(begin, end-8*L+1, 9*L):
        left_plus=labels(u+L,u+2*L)
        left_minus=labels(u+5*L,u+6*L)
        right_plus=labels(X//(5*(u+8*L)),X//(5*(u+7*L)))
        right_minus=labels(X//(5*(u+4*L)),X//(5*(u+3*L)))
        count=min(len(left_plus),len(left_minus),len(right_plus),len(right_minus))
        if not count:
            continue
        for group,sign in ((left_plus,1),(left_minus,-1),(right_plus,1),(right_minus,-1)):
            for n in group[:count]:
                assert n not in support
                support[n]=sign
        packets.append(count)
    return L, support, packets


def test_side(H, mu):
    L, support, packets=make_packets(H,mu)
    X=H*H
    sites=sorted(support)
    assert sites
    prefix=[0]
    for n in sites:
        prefix.append(prefix[-1]+support[n])
    assert prefix[-1]==0 and min(prefix)==0 and max(prefix)==max(packets)
    assert 1<=X//(sites[-1]**2) and X//(sites[0]**2)<7
    # On the whole chosen support the rough kernel is exactly 1 + [5ij <= H^2].
    direct=prefix[-1]**2+sum(support[i]*prefix[bisect_right(sites,X//(5*i))] for i in sites)
    # Opening prime 5 makes the uncentered matrix equal one across this entire support.
    # The same chosen labels already avoid 5, so the compared coefficient vector is identical.
    assert all(gcd(n,30)==1 for n in sites)
    opened=prefix[-1]**2
    assert opened==0
    expected=-2*sum(m*m for m in packets)
    assert direct==expected
    # Directed reciprocal sum bounds avoid gigantic least common denominators.
    scale=10**17
    lo=sum(scale*support[i]//i for i in sites)
    hi=lo+len(sites)
    mag=max(abs(lo),abs(hi))
    tail=Q(H**2*mag**2,3*scale**2)
    # Every doubling window meeting these labels has h >= ceil(min(sites)/2).
    # The budget is bounded by the largest prefix difference squared times 1/(h+1).
    first_possible=(min(sites)+1)//2
    budget=Q(max(packets)**2,first_possible+1)
    return {'side':H,'packet_width':L,'number_of_packets':len(packets),'selected_sites':len(sites),
            'largest_saved_increment':max(packets),'all_doubling_window_cost_upper':str(budget),
            'actual_integer_form_of_assigned_signs':direct,
            'centered_lower':str((Q(direct)-tail)//1), 'centered_upper':direct,
            'opening_five_uncentered':opened,
            'opening_five_centered_lower':str((-Q(4,5)*tail)//1),
            'opening_five_centered_upper':0,
            'assignment':'balanced alternative signs on selected genuine squarefree labels coprime to 30'}


if __name__=='__main__':
    sides=[262144,1048576,4194304]
    mu,_,_=sieve(max(sides))
    out=[test_side(H,mu) for H in sides]
    print(json.dumps(out,indent=2))
