"""Exact divisor optimization and signed full-error comparisons for adjacent clocks."""
import json
from fractions import Fraction as Q
from math import gcd, lcm


def moebius(n):
    if n == 1:
        return 1
    return -sum(moebius(d) for d in range(1, n) if n % d == 0)


def totient(n):
    return sum(gcd(d, n) == 1 for d in range(1, n + 1))


def best_columns(height):
    moduli = range(2, height + 1)
    g = sum(Q(moebius(d)**2, totient(d)) for d in moduli)
    z = {d: -Q(moebius(d), totient(d)) / g for d in moduli}
    x = {}
    for d in reversed(moduli):
        x[d] = z[d] - sum(x[k] for k in range(2*d, height + 1, d))
    mean = sum(x[a]*x[b]*(gcd(a, b)-1) for a in moduli for b in moduli)
    assert sum(x.values()) == 1 and mean == 1/g
    # Normal equations independently test optimality in every physical input channel.
    assert all(sum((gcd(d, e)-1)*x[e] for e in moduli) == mean for d in moduli)
    if height <= 8:
        period = lcm(*moduli)
        changes = [1 - sum(d*x[d] for d in moduli if t % d == 0) for t in range(1, period+1)]
        assert sum(v*v for v in changes)/period == mean
    return str(mean)


def base(k):
    return Q(k % 2)


def target(name, k):
    return Q(name == 'constant' or k == 1)


def successive_repairs(name, parent):
    turns = [Q(0), Q(1)] if parent == 'binary' else [Q(0), Q(1), Q(1, 2), Q(0), Q(-1, 2), Q(1, 2)]
    period, values = 2, [base(0), base(1)]
    result = []
    for _ in range(2):
        m = next(k for k in range(1, period+3) if target(name, k) != values[k % period])
        assert m >= 2
        a = target(name, m) - values[m % period]
        new_period = lcm(period, len(turns)*m, len(turns)*(m+1))
        before = [values[k % period] for k in range(new_period)]
        after = [v + a*(turns[k//m % len(turns)] - turns[k//(m+1) % len(turns)])
                 for k, v in enumerate(before)]
        assert before[:m] == after[:m] and after[m] == target(name, m)
        result.append(whole_gain(name, before, after, m, a))
        period, values = new_period, after
    return result


def whole_gain(name, before, after, pivot, change, cut=50_000):
    # Beyond row one both targets repeat a constant. Each squared-loss difference
    # then has the common period of the two fits, including every row after cut.
    remote = Q(name == 'constant')
    numerators = [(remote-x)**2 - (remote-y)**2 for x, y in zip(before, after)]
    first = (1-before[1])**2 - (1-after[1])**2
    denom = lcm(first.denominator, *(v.denominator for v in numerators))
    period = len(before)
    whole = [int(v*denom) for v in numerators]
    scale = 10**16
    lower = scale*int(first*denom) // (2*denom)
    for k in range(2, cut+1):
        lower += scale*whole[k % period] // (denom*k*(k+1))
    low = Q(lower, scale) + Q(min(whole), denom*(cut+1))
    high = Q(lower+cut, scale) + Q(max(whole), denom*(cut+1))
    return {'row':pivot, 'change':str(change), 'gain_lower':str(low), 'gain_upper':str(high)}


def audit():
    outcomes = {}
    for name in ('constant', 'tick'):
        for parent in ('binary', 'six'):
            stages = successive_repairs(name, parent)
            outcomes[name+'_'+parent] = stages
            if parent == 'binary':
                assert Q(stages[0]['gain_upper']) < 0
            else:
                assert Q(stages[0]['gain_lower']) > (Q(1, 160) if name == 'constant' else Q(1, 250))
                assert Q(stages[1]['gain_upper']) < 0
    optima = {str(b):best_columns(b) for b in range(2, 25)}
    assert optima['2'] == '1' and optima['6'] == '4/9'
    return {'height_optima':optima, 'first_two_forced_pivots':outcomes,
            'cut':50000, 'tail':'minimum and maximum over the complete repeated period times 1/(cut+1)'}


if __name__ == '__main__':
    print(json.dumps(audit(), indent=2))
