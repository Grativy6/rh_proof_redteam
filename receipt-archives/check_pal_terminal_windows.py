"""Reprice the two terminal differences using the ordinary Mertens function."""
import argparse
from bisect import bisect_left
from fractions import Fraction
import hashlib
import json
from math import isqrt
from pathlib import Path
import struct

from check_pal_reference_prices import mu, physical

MAXIMA = Path(__file__).with_name("ordinary-mertens-maxima-200m.bin")


def weights(top):
    """The positive coefficients of the half-window and mixed-window sources."""
    rows = []
    two = 1
    while two * two <= top:
        q = two * two
        j = 0
        while q <= top:
            half = two * (3**(j//2+1)-1)//2
            mixed = two * 3**(j//2) if j % 2 == 0 else 0
            rows.append((q, half, mixed))
            q *= 3
            j += 1
        two *= 2
    return sorted(rows)


def small_check(top=3072):
    m = [0]
    original = [0]
    for n in range(1, top+1):
        m.append(m[-1] + mu(n))
        original.append(original[-1] + physical(n))
    rows = weights(top)
    for n in range(1, top+1):
        h = original[n] - original[n//2]
        d = h - original[n//3] + original[n//6]
        assert h == sum(a*m[n//q] for q,a,_ in rows if q<=n)
        assert d == sum(b*m[n//q] for q,_,b in rows if q<=n)
    return {"all_heads":top,"half_at_16":original[16]-original[8]}


def bounds(top, first=50000001):
    direct = 200000000
    if not first <= top <= 10**13:
        raise ValueError("head outside the stated arithmetic range")
    data = MAXIMA.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    old = json.loads(MAXIMA.with_name("2026-11-25-pal-running-mass.json").read_bytes())
    assert digest == old["externally_supported_extension"]["python"]["maxima_sha256"]
    maxima = [v for (v,) in struct.iter_unpack("<i", data)]
    ends = [0]
    while ends[-1] < direct:
        a = ends[-1]+1
        ends.append(min(direct, a+max(1, a//2048)-1))
    assert len(ends) == len(maxima)
    rows = weights(top)
    windows = [{"name":name,"first_unresolved":None,"panels_ge_zero":0,
                "largest_upper_per_root_squared":None} for name in ["half","mixed"]]
    largest = [Fraction(0), Fraction(0)]
    panels = 0
    a = first
    while a <= top:
        # Split at the end of the directly sieved ordinary Mertens data.
        b = min(top, a+max(1,a//2048)-1, direct if a<=direct else top)
        totals = [0,0]
        for q, half, mixed in rows:
            if q > b:
                break
            lo, hi = a//q, b//q
            if hi > direct:
                # The paper covers 200 < n < 10^13. At 10^13, mu(n)=0.
                u = isqrt(571**2*min(hi,10**13-1))//1000
            if lo <= direct:
                left = bisect_left(ends,lo)
                right = bisect_left(ends,min(hi,direct))
                small = max(maxima[left:right+1])
                u = small if hi<=direct else max(small,u)
            totals[0] += half*u
            totals[1] += mixed*u
        for i,(w,s) in enumerate(zip(windows,totals)):
            if s >= 0:
                w["panels_ge_zero"] += 1
                if w["first_unresolved"] is None:
                    w["first_unresolved"] = [a,b,s]
                candidate = Fraction(s*s,a)
                if candidate > largest[i]:
                    largest[i] = candidate
                    w["largest_upper_per_root_squared"] = [a,b,s]
        panels += 1
        a = b+1
    for w,peak in zip(windows,largest):
        first_gap = w["first_unresolved"]
        w["contiguous_strict_negative_through"] = top if first_gap is None else first_gap[0]-1
        w["upper_positive_ratio_squared"] = str(peak)
    if first == 50000001 and top == 10**13:
        assert largest[0] < 26 and largest[1] < 36
    return {"first":first,"last":top,"panels":panels,"maxima_sha256":digest,
            "ordinary_direct_limit":direct,"windows":windows}


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--head",type=int,default=10**13)
    args = cli.parse_args()
    print(json.dumps({"ordinary_source_check":small_check(),"envelope":bounds(args.head)},indent=2))
