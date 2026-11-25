"""Follow exact coefficient flow on the two integer clocks and test the common cutoff."""
from fractions import Fraction as Q
from math import gcd, lcm
import json


def mobius_table(n):
    values = [0] * (n+1)
    values[1] = 1
    for d in range(1, n+1):
        for multiple in range(2*d, n+1, d):
            values[multiple] -= values[d]
    return values


def coordinates(n):
    i = j = 0
    while n % 2 == 0:
        n //= 2
        i += 1
    while n % 3 == 0:
        n //= 3
        j += 1
    return n, i, j


def calculate(target, cutoff, head):
    mu = mobius_table(cutoff)
    x, y = [Q(0)]*(cutoff+1), [Q(0)]*(cutoff+1)
    for n in range(1, cutoff+1):
        charge = mu[n] - (mu[n//2] if target == 'tick' and n % 2 == 0 else 0)
        _, i, j = coordinates(n)
        incoming = Q(charge, n)
        if i: incoming += x[n//2]
        if j: incoming += y[n//3]
        x[n] = incoming * Q(i+1, i+j+2)
        y[n] = incoming - x[n]

    flux = {}
    for core in (5, 7, 35):
        assert gcd(core, 6) == 1
        for t in range(3, cutoff.bit_length()+1):
            if core*3**t > cutoff:
                break
            shell = [core*2**i*3**(t-i) for i in range(t+1)]
            outgoing = sum(x[n]+y[n] for n in shell)
            assert outgoing == Q(mu[core], (3 if target == 'constant' else 6)*core)
            flux[f'{core}, layer {t}'] = str(outgoing)

    # A_m=m*x_m and B_m=m*y_m are the actual coefficients of floor(k/m) mod 2 or 3.
    denom = lcm(*(v.denominator for part in (x, y) for v in part))
    A = [int(n*v*denom) for n, v in enumerate(x)]
    B = [int(n*v*denom) for n, v in enumerate(y)]
    impulse = [0]*(3*cutoff+1)
    for m in range(1, cutoff+1):
        impulse[m] += A[m]+B[m]
        impulse[2*m] -= 2*A[m]
        impulse[3*m] -= 3*B[m]
    increment = [0]*(head+1)
    for d, value in enumerate(impulse[1:], 1):
        if value:
            for k in range(d, head+1, d):
                increment[k] += value

    scale = 10**15
    reading = lower = 0
    first_over_one = None
    for k in range(1, head+1):
        reading += increment[k]
        ideal = denom if target == 'constant' or k == 1 else 0
        if k <= cutoff:
            assert reading == ideal
        if k <= cutoff+1 or k in (2*cutoff, 3*cutoff, head//2, head):
            direct = sum(A[m]*((k//m) % 2)+B[m]*((k//m) % 3) for m in range(1, cutoff+1))
            assert reading == direct
        lower += scale*(reading-ideal)**2 // (denom**2*k*(k+1))
        if lower > scale and first_over_one is None:
            first_over_one = k
    return {'target':target,'exact_prefix':cutoff,'last_inspected_row':head,
            'prefix_error_lower':str(Q(lower, scale)), 'prefix_error_upper':str(Q(lower+head, scale)),
            'first_certified_prefix_above_one':first_over_one,
            'absolute_normalized_coefficients':str(sum(abs(v) for part in (x,y) for v in part)),
            'outgoing_by_core_and_layer':flux}


def audit():
    main = [calculate(name, 256, 15000) for name in ('constant', 'tick')]
    assert all(Q(r['prefix_error_lower']) > 1 for r in main)
    # A wider head of construction separately checks the two signs and three shells.
    grid = calculate('constant', 1024, 1025)['outgoing_by_core_and_layer']
    assert grid['5, layer 4'] == '-1/15' and grid['35, layer 3'] == '1/105'
    return {'rule':'at (i,j) split the total in proportions (i+1):(j+1), stop at integer cutoff',
            'finite_cutoff_trials':main, 'larger_constant_grid':grid}


if __name__ == '__main__':
    print(json.dumps(audit(), indent=2))
