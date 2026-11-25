"""Recreate the candidate boundary coefficients. The independent checker uses the saved rationals."""
import json
import os
from fractions import Fraction as Q
from pathlib import Path

os.environ.setdefault('OPENBLAS_NUM_THREADS', '2')
os.environ.setdefault('OMP_NUM_THREADS', '2')
import numpy as np

from check_pal_two_clock_flow import coordinates, mobius_table


HEIGHT = 256
DEN = 1200000


def frame(target):
    mu = mobius_table(HEIGHT)
    src = [mu[n]-(mu[n//2] if target == 'tick' and n % 2 == 0 else 0) for n in range(HEIGHT+1)]
    groups, totals = {}, {}
    for n in range(1, HEIGHT+1):
        r = coordinates(n)[0]
        groups.setdefault(r, set()).update(v for v in (2*n, 3*n) if v > HEIGHT)
        totals[r] = totals.get(r, Q(0)) + Q(r*src[n], n)
    return src, {r:sorted(g) for r,g in groups.items()}, totals


def base_witness(target):
    src, groups, totals = frame(target)
    k = np.arange(HEIGHT+1, 32769, dtype=np.int64)
    w = 1/np.sqrt(k*(k+1))
    base = np.zeros(len(k))
    labels = []
    for n in range(1, HEIGHT+1):
        if src[n]:
            base -= src[n]*(k%n)/n
    for r, group in groups.items():
        base += float(totals[r])*(k%group[0])/r
        labels.extend((r,v,group[0]) for v in group[1:])
    matrix = np.column_stack([((k%v-k%anchor)/r)*w for r,v,anchor in labels])
    coeff, _, rank, _ = np.linalg.lstsq(matrix, (int(target=='constant')-base)*w, rcond=None)
    assert rank == len(labels)
    scaled = {r:{} for r in groups}
    for (r,v,_), a in zip(labels, coeff):
        scaled[r][v] = round(float(a)*DEN)
    for r, group in groups.items():
        total = totals[r]*DEN
        assert total.denominator == 1
        scaled[r][group[0]] = int(total)-sum(scaled[r].values())
    return {v:a*(v//r) for r,g in scaled.items() for v,a in g.items()}


def training_rows():
    rng = np.random.default_rng(256)
    rows, masses = [], []
    for lo, hi, step in ((257,8704,1), (8705,50000,6), (50001,200000,31),
                         (200001,800000,149), (800001,4000000,541)):
        a = np.arange(lo,hi+1,step,dtype=np.int64)
        b = np.minimum(a+step,hi+1)
        rows.extend(a+np.floor(rng.random(a.size)*(b-a)).astype(np.int64))
        masses.extend((b-a)/(a*b))
    return np.asarray(rows),np.sqrt(masses)


def wide_witness(target, base, k, w):
    src, groups, _ = frame(target)
    new = range(HEIGHT+1, 2*HEIGHT+1)
    labels = [(r,v,g[-1]) for r,g in groups.items() for v in g[:-1]]
    directions = [((k%v-k%anchor)/r)*w for r,v,anchor in labels]
    directions.extend(((k//n)%d)*w for d in (2,3) for n in new)
    matrix = np.column_stack(directions)
    gram = matrix.T@matrix
    base_reading = -sum(src[n]*(k%n)/n for n in range(2,HEIGHT+1) if src[n])
    for v,num in sorted(base.items()):
        base_reading += num/DEN*(k%v)/v
    y = (float(target=='constant')-base_reading)*w
    rhs = matrix.T@y
    candidates = []
    for ridge in (1e-7, 5e-7, 2e-6):
        z = np.linalg.solve(gram+ridge*np.eye(len(gram)),rhs)
        score = float(np.sum((matrix@z-y)**2))+1e-6*sum(abs(z))
        candidates.append((score,z))
    _, z = min(candidates,key=lambda x:x[0])
    revised = dict(base)
    for (r,v,anchor), value in zip(labels,z):
        a = round(float(value)*DEN)
        revised[v] += (v//r)*a
        revised[anchor] -= (anchor//r)*a
    nums = [round(float(a)*DEN) for a in z[len(labels):]]
    return revised, nums[:HEIGHT], nums[HEIGHT:]


if __name__ == '__main__':
    path=Path(__file__).with_name('2026-11-25-pal-two-clock-exits.json')
    k,w=training_rows()
    for p in json.loads(path.read_text(encoding='utf8'))['witnesses']:
        base=base_witness(p['target'])
        assert base=={int(v):a for v,a in p['exit_coef'].items()}
        revised,binary,ternary=wide_witness(p['target'],base,k,w)
        wide=p['wider']
        assert revised=={int(v):a for v,a in wide['exit_coef'].items()}
        assert binary==wide['binary_numerators'] and ternary==wide['ternary_numerators']
        print(p['target'], 'both rounded candidate tables reproduced')
