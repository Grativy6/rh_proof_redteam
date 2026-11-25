"""Check the exact two-clock boundary witnesses and a bound over every later row."""
from collections import defaultdict
from fractions import Fraction as Q
from math import gcd, lcm
from pathlib import Path
import json

from check_pal_two_clock_flow import coordinates, mobius_table


def boundary_tree(cut, sources, exits):
    # Delta is outgoing flow minus incoming. Each tree edge is oriented upwards.
    divergence = {n:Q(sources[n], n) for n in range(1, cut+1)}
    divergence.update({v:-mass for v, mass in exits.items()})
    sent, x, y = defaultdict(Q), defaultdict(Q), defaultdict(Q)
    for v in sorted(divergence, reverse=True):
        if gcd(v, 6) == 1:
            assert sent[v] == divergence[v]
            continue
        d = next(d for d in (2, 3) if v % d == 0 and v//d <= cut)
        parent = v//d
        edge = sent[v] - divergence[v]
        (x if d == 2 else y)[parent] = edge
        sent[parent] += edge
    return x, y


def tail_data(c, target):
    # For uniform k over a common period, covariance of b_i,b_j is
    # (gcd(i,j)^2-1)/(12*i*j). Jordan's divisor identity sums that form exactly.
    size = max(c)
    jordan = [n*n for n in range(size+1)]
    for d in range(1, size+1):
        for n in range(2*d, size+1, d):
            jordan[n] -= jordan[d]
    mean_reading = sum(v*Q(d-1, 2*d) for d, v in c.items())
    variance = Q(0)
    for d in range(2, size+1):
        column = sum((c.get(n, Q(0))/n for n in range(d, size+1, d)), Q(0))
        variance += jordan[d]*column**2/12
    average = (target-mean_reading)**2 + variance
    assert average >= 0
    # Bounded discrepancy of the partial sums of each centered periodic product.
    den = lcm(*(v.denominator for v in c.values()))
    scaled = [(d, int(abs(v)*den)) for d, v in c.items() if v]
    noise = sum(v*w*lcm(d,e) for d, v in scaled for e, w in scaled)
    noise += 2*abs(target)*den*sum(v*d for d,v in scaled)
    return average, Q(noise, den*den)


def policy_lower(cut, head, den, plan, rnumer, exits):
    # Test all exit assignments, with real coefficients. The largest exit in
    # each core is the balancing anchor. Every other column's first live row
    # is its own endpoint v, where its integer reading is exactly -v.
    groups = defaultdict(list)
    for v in exits:
        groups[coordinates(v)[0]].append(v)
    columns = {v:max(group) for group in groups.values() for v in group if v != max(group)}
    scale = 10**16
    z = [0]*(head+1)
    for k in range(cut+1, head+1):
        z[k] = (scale*rnumer[k]) // (den*k*(k+1))
    scores = {v:sum(z[k]*((k%v)-(k%anchor)) for k in range(v, head+1))
              for v, anchor in columns.items()}
    corrections = {}
    for v in sorted(columns, reverse=True):
        anchor = columns[v]
        mismatch = scores[v] + sum(tv*((w%v)-(w%anchor)) for w,tv in corrections.items())
        corrections[v] = Q(mismatch, v)
    for v, anchor in columns.items():
        assert scores[v] + sum(tv*((w%v)-(w%anchor)) for w,tv in corrections.items() if w >= v) == 0
    dot = Q(sum(z[k]*rnumer[k] for k in range(cut+1, head+1)), den)
    norm = Q(sum(z[k]*z[k]*k*(k+1) for k in range(cut+1, head+1)))
    for k, correction in corrections.items():
        dot += correction*Q(rnumer[k], den)
        norm += (2*z[k]*correction + correction**2)*k*(k+1)
    assert norm > 0
    lower = dot**2/norm
    threshold = Q(4,25) if plan['target']=='constant' else Q(3,40)
    assert lower > threshold, (plan['target'],float(lower))
    return str(Q((lower*100000)//1,100000))


def check(plan, wider=False):
    last = 10_000_000 if wider else 2_000_000
    cut, den, name = plan['cutoff'], plan['D'], plan['target']
    mu = mobius_table(cut)
    src = [mu[n]-(mu[n//2] if name == 'tick' and n%2 == 0 else 0) for n in range(cut+1)]
    shape = plan['wider'] if wider else plan
    vcoef = {int(k):v for k,v in shape['exit_coef'].items()}
    allowed = {d*k for k in range(1,cut+1) for d in (2,3) if d*k>cut}
    assert set(vcoef) == allowed
    by_core = defaultdict(Q)
    for n in range(1, cut+1):
        by_core[coordinates(n)[0]] += Q(src[n], n)
    exits = {v:Q(n,den*v) for v,n in vcoef.items()}
    for v, mass in exits.items():
        by_core[coordinates(v)[0]] -= mass
    assert all(v==0 for v in by_core.values())
    x, y = boundary_tree(cut, src, exits)
    coeffs = {n:-Q(src[n]) for n in range(2, cut+1) if src[n]}
    coeffs.update({v:Q(n,den) for v,n in vcoef.items() if n})

    # F(k) is given by its finite sum of floors. Its jumps land on multiples.
    impulses = {n:den*src[n] for n in range(1,cut+1) if src[n]}
    impulses.update({v:-n for v,n in vcoef.items() if n})
    extra = []
    if wider:
        start = shape['first_extra_scale']
        assert start > cut
        for d, label in ((2,'binary_numerators'), (3,'ternary_numerators')):
            nums = shape[label]
            assert len(nums) == shape['width'] - start + 1
            for m, value in enumerate(nums, start):
                coeffs[m] = coeffs.get(m, Q(0)) - Q(value, den)
                coeffs[d*m] = coeffs.get(d*m, Q(0)) + Q(d*value, den)
                impulses[m] = impulses.get(m, 0) + value
                impulses[d*m] = impulses.get(d*m, 0) - d*value
                extra.append((m, value, d))

    sample = set(range(1,cut+2)) | {3*cut, 1000, last}
    scale = 10**16
    read = lower = 0
    fit_head = plan['fit_head']
    residual = [0]*(fit_head+1)
    chunk = 131072
    for first in range(1, last+1, chunk):
        size = min(chunk, last-first+1)
        deltas = [0]*size
        for d, val in impulses.items():
            if val:
                for i in range((-first) % d, size, d):
                    deltas[i] += val
        for i, jump in enumerate(deltas):
            k = first+i
            read += jump
            ideal = den if name == 'constant' or k == 1 else 0
            if k<=fit_head:
                residual[k] = ideal-read
            if k<=cut:
                assert read==ideal
            if k in sample:
                raw = sum(m*a*((k//m)%2) for m,a in x.items()) + sum(m*b*((k//m)%3) for m,b in y.items())
                additional = sum(value*((k//m)%d) for m,value,d in extra)
                assert raw*den + additional == read
            lower += scale*(read-ideal)**2 // (den**2*k*(k+1))
    average, discrepancy = tail_data(coeffs, int(name=='constant'))
    allowance = average/(last+1) + discrepancy/((last+1)*(last+2))
    upper = Q(lower+last, scale) + allowance
    threshold = ((Q(16939,100000) if name=='constant' else Q(387,5000)) if wider else
                 (Q(1,4) if name=='constant' else Q(1,8)))
    assert upper < threshold, (name,float(upper))
    # The displayed decimal endpoints are rounded away from the true interval.
    display_scale=100000
    return {'target':name, 'first_rows_exact':cut, 'copy_width':shape['width'] if wider else cut,
            'original_free_exit_coordinates':len(exits)-len(by_core),
            'rows_in_direct_sum':last,
            **({} if wider else {'lower_for_every_width_256_fit_with_exact_prefix':policy_lower(cut, fit_head, den, plan, residual, exits)}),
            'true_loss_lower':str(Q((Q(lower,scale)*display_scale)//1,display_scale)),
            'true_loss_upper':str(Q(-(-upper*display_scale//1),display_scale)),
            'tail_allowance_upper':str(Q(-(-allowance*display_scale//1),display_scale)),
            'mean_square_tail_upper':str(Q(-(-average*display_scale//1),display_scale))}


def audit():
    path=Path(__file__).with_name('2026-11-25-pal-two-clock-exits.json')
    return [check(p, wider) for p in json.loads(path.read_text(encoding='utf8'))['witnesses']
            for wider in (False, True)]


if __name__=='__main__':
    print(json.dumps(audit(),indent=2))
