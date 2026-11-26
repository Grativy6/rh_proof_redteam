"""Check the actual signed family n=c*q in a block and its available prime carriers."""
import argparse
import csv
from fractions import Fraction as Q
import hashlib
import json
from math import ceil, floor
from pathlib import Path
from check_pal_prime_transport import bounds, outward, price, SCALE, transport_enclosure


def factor(n):
    result = []
    p = 2
    while p*p <= n:
        while n % p == 0:
            result.append(p)
            n //= p
        p += 1 if p == 2 else 2
    if n > 1:
        result.append(n)
    return result


def direct_calibration(rows, C):
    A, B = rows[0][0], rows[-1][1]
    if B-A > 100000:
        raise ValueError("Direct trial division is intended for a small calibration block")
    for lo,hi,positive,negative,offered,five in rows:
        counts = [0]*4
        for n in range(lo+1,hi+1):
            factors = factor(n)
            c = n//factors[-1]
            if c > C or factors[-1] <= C:
                continue
            a,b = factors.count(2),factors.count(3)
            rough = [p for p in factors if p > 3]
            if a % 2 or b % 2 or len(set(rough)) != len(rough):
                continue
            magnitude = 2**(a//2)*3**(b//2)
            counts[len(rough)%2] += magnitude
            if len(factors) == 2 and 5 <= factors[0] <= 347:
                counts[2] += 1
                counts[3] += factors[0] == 5
        assert counts == [positive,negative,offered,five]


def fit(lower, upper, column, net, available):
    if net < 0 or net > available:
        return {"status":"impossible_by_constant_moment","signed_marks":net,"supply":available}
    lo = [row[column:column+5]+[row[10]] for row in lower]
    hi = [row[column:column+5]+[row[10]] for row in upper]
    try:
        solution = transport_enclosure(lo, hi)
    except (AssertionError,ValueError,StopIteration):
        return {"status":"capacity_unresolved_at_this_subdivision"}
    return {"status":"strict_capacity_proved",**solution}


def evaluate(file, C, head=None, calibration=False):
    with file.open(encoding="ascii",newline="") as f:
        reader = csv.DictReader(f)
        assert reader.fieldnames == ["left","right","positive","negative","offered","five"]
        rows = [tuple(int(r[k]) for k in reader.fieldnames) for r in reader]
    A,B,N = rows[0][0],rows[-1][1],len(rows)
    assert C*C < A and N > 0 and N % 5 == 0
    if calibration:
        direct_calibration(rows,C)
    lower = [[0]*11 for _ in range(5)]
    upper = [[0]*11 for _ in range(5)]
    totals = [0]*4
    cost_lower = cost_upper = 0
    if head is not None:
        assert Q(4,5) <= Q(A,head) < Q(B,head) <= Q(5,6)
    for j,(lo,hi,pos,neg,all_offered,five) in enumerate(rows):
        assert lo == A+(B-A)*j//N and hi == A+(B-A)*(j+1)//N
        assert 0 <= five <= all_offered <= pos and neg >= 0
        group = j//(N//5)
        for k,v in enumerate((pos,neg,all_offered,five)):
            totals[k] += v
        for i in range(5):
            l,h = bounds(i,lo,hi,A,B)
            for col,amount in [(group,all_offered),(group+5,five)]:
                lower[i][col] += l*amount
                upper[i][col] += h*amount
            lower[i][10] += l*pos-h*neg
            upper[i][10] += h*pos-l*neg
        if head is not None:
            l,h = floor(SCALE*price(head,lo)),ceil(SCALE*price(head,hi))
            cost_lower += pos*l-neg*h
            cost_upper += pos*h-neg*l
    pos,neg,offered,five = totals
    net = pos-neg
    result = {"left_excluded":A,"right_included":B,"cofactor_limit":C,"subdivisions":N,
              "positive_magnitude":pos,"negative_magnitude":neg,"signed_marks":net,
              "grouped_semiprime_supply":offered,"five_times_prime_supply":five,
              "grouped_carrier":fit(lower,upper,0,net,offered),
              "five_carrier":fit(lower,upper,5,net,five),
              "counts_sha256":hashlib.sha256(file.read_bytes()).hexdigest()}
    result["moment_bounds_times_10_to_15"] = {
        "columns":["five grouped-semiprime bins","five 5q bins","signed target"],
        "lower":lower,"upper":upper}
    if head is not None:
        result["head"] = head
        result["signed_point_price_interval"] = [outward(Q(cost_lower,SCALE),3,False),
                                               outward(Q(cost_upper,SCALE),3,True)]
    return result


def replay_record(record):
    data = json.loads(record.read_text(encoding="utf8"))
    for name,row in data["finite_cases"].items():
        moments = row["moment_bounds_times_10_to_15"]
        for key,offset,available in [("grouped_carrier",0,"grouped_semiprime_supply"),
                                     ("five_carrier",5,"five_times_prime_supply")]:
            recomputed = fit(moments["lower"],moments["upper"],offset,row["signed_marks"],row[available])
            assert recomputed == row[key]
        print(name,row["signed_marks"],row["five_carrier"]["status"])


if __name__ == "__main__":
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("csv",type=Path,nargs="?")
    args.add_argument("cofactor_limit",type=int,nargs="?")
    args.add_argument("--head",type=int)
    args.add_argument("--trial-division",action="store_true")
    args.add_argument("--replay-record",type=Path)
    v = args.parse_args()
    if v.replay_record:
        replay_record(v.replay_record)
    elif v.csv is not None and v.cofactor_limit is not None:
        print(json.dumps(evaluate(v.csv,v.cofactor_limit,v.head,v.trial_division),indent=2))
    else:
        args.error("Supply a CSV and cofactor limit, or use --replay-record")
