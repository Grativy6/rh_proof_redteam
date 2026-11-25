"""Check square rescaling on exact rational samples and every half-row of a fixed head."""
from array import array
from fractions import Fraction as Q
from math import comb
import json

from check_pal_growth_windows import sieve


def coefficients(raw, clocks):
    out = array("q", (v if n % 6 in (1, 5) else 0 for n, v in enumerate(raw)))
    for p in clocks:
        square = p * p
        for d in range(1, (len(out) - 1) // square + 1):
            out[square * d] += p * out[d]
    return out


def exact_edge(x, marks):
    x = Q(x)
    return sum((Q(marks[d], d) * min(1, 2 - d / x)
                for d in range(1, int(2 * x) + 1)), Q(0))


def lifted(x, k, base):
    x = Q(x)
    total = Q(0)
    four = 1
    a = 0
    while four <= 2*x:
        nine = 1
        b = 0
        while four*nine <= 2*x:
            ca = int(a == 0) if not k else comb(k+a-1, a)
            cb = int(b == 0) if not k else comb(k+b-1, b)
            total += Q(ca*cb, 2**a * 3**b) * exact_edge(x/(four*nine), base)
            nine *= 9
            b += 1
        four *= 4
        a += 1
    return total


def finite_inverses():
    h = 160
    raw, _, _ = sieve(2*h)
    base = coefficients(raw, ())
    tested = []
    for k in (1, 2, 3):
        current = coefficients(raw, (2, 3)*k)
        prior = coefficients(raw, (2, 3)*(k-1))
        for n in range(1, 2*h+1):
            v = Q(n, 2)
            assert exact_edge(v, current) == lifted(v, k, base)
            assert exact_edge(v, prior) == (exact_edge(v, current) - exact_edge(v/4, current)/2
                                            - exact_edge(v/9, current)/3 + exact_edge(v/36, current)/6)
        tested.append({"passes": k, "half_rows": 2*h})
    return tested


def direct_half(tick, marks, scale, divisor=1):
    """Bound the coefficient sum at x = tick / (2*divisor) with directed rounding."""
    low = inexact = 0
    for n in range(1, tick//divisor+1):
        if marks[n]:
            qr, rem = divmod(scale*min(tick, 2*(tick-divisor*n))*marks[n], tick*n)
            low += qr
            inexact += bool(rem)
    return low, low+inexact


def all_rows(limit, marks, direct=False):
    scale = 10**23
    lo, error, band = scale, 0, marks[2]
    worst = (lo, 2)
    positive = negative = ambiguous = 0
    first = None
    selected = {}
    first_crossing_tick = 13_027_865
    specials = {first_crossing_tick-1, first_crossing_tick, first_crossing_tick+1, 2*51**4, 2*limit}
    for h in range(1, limit+1):
        middle, rem = divmod(scale*band, h*(2*h+1))
        points = [(2*h, lo, lo+error)]
        if h < limit:
            points.append((2*h+1, lo+middle, lo+error+middle+bool(rem)))
        for n, lower, upper in points:
            if lower > 0:
                positive += 1
            elif upper < 0:
                negative += 1
                if first is None:
                    first = n
            else:
                ambiguous += 1
            if lower < worst[0]:
                worst = lower, n
            if n <= 320:
                exact = exact_edge(Q(n, 2), marks)*scale
                assert lower <= exact <= upper
            if n in specials:
                selected[str(n)] = [str(Q(lower, scale)), str(Q(upper, scale))]
        if h < limit:
            admitted = marks[2*h+1]
            step, rem = divmod(scale*(band*(2*h+1)+h*admitted), h*(h+1)*(2*h+1))
            lo += step
            error += bool(rem)
            band += admitted + marks[2*h+2] - marks[h+1]
    if direct:
        # Sum the original coefficients directly at the first crossing and at the last row.
        for tick in (first_crossing_tick, 2*limit):
            low, high = direct_half(tick, marks, scale)
            earlier_low, earlier_high = (Q(bound) for bound in selected[str(tick)])
            assert max(Q(low, scale), earlier_low) <= min(Q(high, scale), earlier_high)
    return {"half_rows_from_one": positive+negative+ambiguous, "strictly_positive": positive,
            "strictly_negative": negative, "unresolved_intervals": ambiguous,
            "first_negative_twice_side": first, "minimum_lower": str(Q(worst[0], scale)),
            "twice_side_of_minimum_lower": worst[1], "selected_twice_sides": selected}


def undo_at_crossing(marks, original):
    tick = 13_027_865
    scale = 10**23
    total_low = total_high = Q(0)
    terms = []
    for divisor, coefficient in ((1, Q(1)), (4, Q(-1, 2)), (9, Q(-1, 3)), (36, Q(1, 6))):
        lower, upper = direct_half(tick, marks, scale, divisor)
        lower, upper = Q(lower, scale), Q(upper, scale)
        assert lower > 0
        values = (coefficient*lower, coefficient*upper)
        total_low += min(values)
        total_high += max(values)
        terms.append({"side": str(Q(tick, 2*divisor)), "coefficient": str(coefficient),
                      "lower": str(lower), "upper": str(upper)})
    raw_low, raw_high = (Q(a) for a in original["selected_twice_sides"][str(tick)])
    assert total_high < 0 and max(total_low, raw_low) <= min(total_high, raw_high)
    return {"twice_side": tick, "four_positive_readings": terms,
            "recovered_lower": str(total_low), "recovered_upper": str(total_high)}


def audit():
    limit = 2**23
    raw, _, _ = sieve(2*limit)
    results = {}
    for name, clocks in (("original", ()), ("four_only", (2,)), ("nine_only", (3,)),
                         ("one_complete_pass", (2, 3))):
        marks = coefficients(raw, clocks)
        results[name] = all_rows(limit, marks, direct=name in ("original", "one_complete_pass"))
        if name == "one_complete_pass":
            recovery = undo_at_crossing(marks, results["original"])
        del marks
    assert results["original"]["first_negative_twice_side"] == 13_027_865
    assert results["original"]["unresolved_intervals"] == 0
    for name in ("four_only", "nine_only", "one_complete_pass"):
        assert results[name]["strictly_positive"] == 2*limit-1
    return {"head": limit, "rounding_denominator": 10**23, "independent_inverse_checks": finite_inverses(),
            "first_crossing_recovery": recovery, "actual_readouts": results}


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
