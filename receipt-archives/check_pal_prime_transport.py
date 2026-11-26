"""Enclose the five actual rational transport fractions from integer prime counts."""
import argparse
from array import array
import csv
from fractions import Fraction as Q
import hashlib
import json
from math import ceil, comb, floor, isqrt, prod
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCALE = 10**15
SIZE = 5


def bernstein(i, t):
    return comb(4, i)*t**i*(1-t)**(4-i)


def bounds(i, lo, hi, A, B):
    u, v = Q(lo-A, B-A), Q(hi-A, B-A)
    endpoints = (bernstein(i, u), bernstein(i, v))
    peak = Q(i, 4)
    maximum = bernstein(i, peak) if u <= peak <= v else max(endpoints)
    return floor(SCALE*Q(A, hi)*min(endpoints)), ceil(SCALE*Q(A, lo)*maximum)


def inverse(matrix):
    aug = [row[:] + [Q(i == j) for j in range(SIZE)] for i, row in enumerate(matrix)]
    for j in range(SIZE):
        k = next(i for i in range(j, SIZE) if aug[i][j])
        aug[j], aug[k] = aug[k], aug[j]
        aug[j] = [v/aug[j][j] for v in aug[j]]
        for i in range(SIZE):
            if i != j:
                factor = aug[i][j]
                aug[i] = [x - factor*y for x, y in zip(aug[i], aug[j])]
    return [row[SIZE:] for row in aug]


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def outward(q, places, up):
    unit = 10**places
    value = (ceil if up else floor)(q*unit)
    sign = '-' if value < 0 else ''
    n = abs(value)
    return f"{sign}{n//unit}.{n%unit:0{places}d}"


def price(T, d):
    z = Q(d, T)
    return 1/(2*z) - Q(3, 2) + 3*z*z - 2*z**3


def read_counts(path):
    with path.open(encoding="ascii", newline="") as stream:
        reader = csv.DictReader(stream)
        assert reader.fieldnames == ["left", "right", "primes", "donors", "triples"]
        return [tuple(int(row[k]) for k in reader.fieldnames) for row in reader]


def transport_enclosure(lower, upper):
    # Columns 0..4 are offered groups. Column 5 is the amount to cover.
    midpoint = [[Q(l+u, 2) for l, u in zip(lr, ur)] for lr, ur in zip(lower, upper)]
    radii = [[Q(u-l, 2) for l, u in zip(lr, ur)] for lr, ur in zip(lower, upper)]
    pre = inverse([row[:5] for row in midpoint])
    for i in range(SIZE):
        for j in range(SIZE):
            assert dot(pre[i], [row[j] for row in midpoint]) == (i == j)
    center = [dot(row, [m[5] for m in midpoint]) for row in pre]
    absolute = [[abs(v) for v in row] for row in pre]
    contraction = max(dot(row, [sum(r[:5]) for r in radii]) for row in absolute)
    if contraction >= 1:
        raise ValueError("Refine the count subdivisions to get a strict contraction")
    errors = [r[5] + dot(r[:5], [abs(v) for v in center]) for r in radii]
    radius = max(dot(row, errors) for row in absolute)/(1-contraction)
    assert all(0 < w-radius <= w+radius < 1 for w in center)
    return {"contraction_upper": outward(contraction, 8, True),
            "uniform_fraction_radius_upper": outward(radius, 8, True),
            "actual_fraction_intervals": [[outward(w-radius, 7, False), outward(w+radius, 7, True)] for w in center]}


def enclose(rows, head):
    A, B = rows[0][0], rows[-1][1]
    N = len(rows)
    assert N >= 5 and N % 5 == 0 and Q(4, 5) <= Q(A, head) <= Q(B, head) <= Q(5, 6)
    # The 11 columns hold five semiprime bins, five three-prime bins and all primes.
    lower = [[0]*11 for _ in range(SIZE)]
    upper = [[0]*11 for _ in range(SIZE)]
    cost_lo, cost_hi = [0,0], [0,0]
    populations = [0]*11
    for j, (lo, hi, primes, donors, triples) in enumerate(rows):
        assert lo == A + ((B-A)*j)//N and hi == A + ((B-A)*(j+1))//N
        assert lo < hi and min(primes, donors, triples) >= 0 and primes+donors+triples <= hi-lo
        group = j//(N//SIZE)
        columns = [(group, donors), (group+5, triples), (10, primes)]
        for col, count in columns:
            populations[col] += count
        for i in range(SIZE):
            lb, ub = bounds(i, lo, hi, A, B)
            for col, count in columns:
                lower[i][col] += lb*count
                upper[i][col] += ub*count
        # The price increases on [4/5, 5/6]. Round out before adding contributions.
        lb, ub = floor(SCALE*price(head, lo)), ceil(SCALE*price(head, hi))
        for i, count in enumerate([primes, donors]):
            cost_lo[i] += count*lb
            cost_hi[i] += count*ub
    def interval(lo, hi):
        return [outward(Q(lo, SCALE), 3, False), outward(Q(hi, SCALE), 3, True)]
    # A common positive scaling of matrix and right-hand side leaves the solution unchanged.
    first = transport_enclosure([r[:5]+[r[10]] for r in lower], [r[:5]+[r[10]] for r in upper])
    # After covering all primes, the remaining positive moments are the full difference.
    lo = [l[5:10]+[sum(l[:5])-u[10]] for l,u in zip(lower,upper)]
    hi = [u[5:10]+[sum(u[:5])-l[10]] for l,u in zip(lower,upper)]
    second = transport_enclosure(lo, hi)
    return {"sector": [A, B], "head": head, "subdivisions": N, "primes": populations[10],
            "donors": sum(populations[:5]), "donors_by_group": populations[:5],
            "triples": sum(populations[5:10]), "triples_by_group": populations[5:10],
            "prime_to_semiprime": first, "remaining_semiprime_to_triple": second,
            "total_prime_price_interval": interval(cost_lo[0],cost_hi[0]),
            "total_semiprime_price_interval": interval(cost_lo[1],cost_hi[1]),
            "second_stage_price_interval": interval(cost_lo[1]-cost_hi[0],cost_hi[1]-cost_lo[0]),
            "total_absolute_price_removed_interval": interval(2*cost_lo[1],2*cost_hi[1])}


def hand_example():
    labels = [83, 95, 107, 119, 131, 143]
    signed = [(-1)**(j+1)*d*comb(5, j) for j, d in enumerate(labels)]
    assert all(all(p % d for d in range(2, isqrt(p)+1)) for p in [83,107,131,5,19,7,17,11,13])
    assert labels[1::2] == [5*19, 7*17, 11*13]
    assert all(sum(w*Q(d)**power for w, d in zip(signed, labels)) == 0 for power in [-1,0,1,2,3])
    for T in range(144,166):
        assert sum(w*price(T, d) for w, d in zip(signed, labels)) == 0
    return {"labels": labels, "signed_numerators": signed, "capacity_denominator": max(map(abs, signed)),
            "integer_heads_checked": [144,165]}


def elementary_counts(rows, limit):
    """An ordinary byte sieve independently reproduces every small calibration count."""
    B = rows[-1][1]
    if B > 10**7:
        raise ValueError("Use the elementary replay on a calibration interval below ten million")
    primes = bytearray(b'\1')*(B+1)
    primes[:2] = b'\0\0'
    for n in range(2, isqrt(B)+1):
        if primes[n]:
            primes[n*n::n] = b'\0'*len(primes[n*n::n])
    palette = [p for p in range(5, limit+1) if primes[p]]
    start, end = rows[0][0]+1, rows[-1][1]
    assert start > limit*limit
    # Strip small factors directly from each integer for an independent classification.
    remainder = list(range(start, end+1))
    tags = [0]*len(remainder)
    for p in palette:
        for n in range(((start+p-1)//p)*p, end+1, p):
            idx = n-start
            remainder[idx] //= p
            tags[idx] += 1
            if remainder[idx] % p == 0:
                tags[idx] = 3
    for lo, hi, targets, donors, triples in rows:
        counts = [0,0,0]
        for n in range(lo+1,hi+1):
            i = n-start
            if tags[i] <= 2 and remainder[i] > limit and primes[remainder[i]]:
                counts[tags[i]] += 1
        assert counts == [targets, donors, triples]


def square_prefixes(limit):
    """Summatory coefficients for the square-divisor formula of |a| and |m|."""
    least = array("i", [0])*(limit+1)
    lifted = array("i", [0])*(limit+1)
    rough = array("i", [0])*(limit+1)
    lifted[1] = rough[1] = 1
    primes = []
    for n in range(2, limit+1):
        if least[n] == 0:
            primes.append(n)
            least[n] = n
            lifted[n] = n if n <= 3 else -1
            rough[n] = 0 if n <= 3 else -1
        for p in primes:
            m = n*p
            if m > limit:
                break
            least[m] = p
            if p <= 3:
                lifted[m] = p*lifted[n]
            elif p != least[n]:
                lifted[m] = -lifted[n]
                rough[m] = -rough[n]
            if p == least[n]:
                break
    a, b = array("q", [0]), array("q", [0])
    for i in range(1, limit+1):
        a.append(a[-1]+lifted[i])
        b.append(b[-1]+rough[i])
    return a, b


def absolute_counts(x, pref):
    m = 1
    a = b = 0
    maximum = isqrt(x)
    while m <= maximum:
        q = x//(m*m)
        last = isqrt(x//q)
        coprime_six = q-q//2-q//3+q//6
        a += (pref[0][last]-pref[0][m-1])*coprime_six
        b += (pref[1][last]-pref[1][m-1])*coprime_six
        m = last+1
    return a,b


def audit_absolute():
    pref = square_prefixes(isqrt(5000))
    totals = [0,0]
    for n in range(1,5001):
        rem, smooth, held = n, 1, True
        for p in (2,3):
            e = 0
            while rem % p == 0:
                rem //= p
                e += 1
            held &= e % 2 == 0
            smooth *= p**(e//2)
        squarefree = all(rem % (r*r) for r in range(5,isqrt(rem)+1))
        if held and squarefree:
            totals[0] += smooth
            totals[1] += smooth == 1
        if n <= 128 or n % 37 == 0 or n == 5000:
            assert absolute_counts(n,pref) == tuple(totals)


def full_sector(A, B, T, removed):
    pref = square_prefixes(isqrt(B))
    start = prev = absolute_counts(A, pref)
    lower, upper = [0,0], [0,0]
    groups = 100
    for j in range(groups):
        lo, hi = A+(B-A)*j//groups, A+(B-A)*(j+1)//groups
        cur = absolute_counts(hi, pref)
        low, high = floor(SCALE*price(T, lo)), ceil(SCALE*price(T, hi))
        for k in range(2):
            count = cur[k]-prev[k]
            assert count >= 0
            lower[k] += count*low
            upper[k] += count*high
        prev = cur
    result = {}
    for k, name in enumerate(["first_pass", "rough_only"]):
        lo, hi = Q(lower[k],SCALE), Q(upper[k],SCALE)
        result[name] = {"absolute_mark_count": cur[k]-start[k],
                        "absolute_price": [outward(lo,3,False),outward(hi,3,True)],
                        "fraction_removed": [outward(Q(removed[0])/hi,7,False),
                                             outward(Q(removed[1])/lo,7,True)]}
    return result


def palette_replay():
    R = [p for p in range(5,348) if all(p%d for d in range(2,isqrt(p)+1))]
    reciprocal = sum(Q(1,r) for r in R)
    pairs = sum(Q(1,r*s) for i,r in enumerate(R) for s in R[i+1:])
    survivor = prod(1-Q(1,r) for r in R)
    assert 1 < reciprocal and 0 < reciprocal-1 < pairs
    def bracket(q):
        return [outward(q,8,False),outward(q,8,True)]
    return {"palette_primes":len(R), "palette_pairs":comb(len(R),2),
            "sum_prime_reciprocals":bracket(reciprocal), "sum_pair_reciprocals":bracket(pairs),
            "all_subset_signed_density_factor":bracket(survivor)}


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("counts", nargs="?", type=Path, default=HERE/"prime-transport-trillion-counts.csv")
    ap.add_argument("--head", type=int, default=2*10**12)
    ap.add_argument("--check-small-counts", type=Path)
    args = ap.parse_args()
    if args.check_small_counts:
        elementary_counts(read_counts(args.check_small_counts), 347)
    result = enclose(read_counts(args.counts), args.head)
    result["counts_sha256"] = hashlib.sha256(args.counts.read_bytes()).hexdigest()
    result["hand_example"] = hand_example()
    audit_absolute()
    result["full_sector"] = full_sector(*result["sector"], args.head, result["total_absolute_price_removed_interval"])
    result["palette"] = palette_replay()
    print(json.dumps(result, indent=2))
