"""Price distinct composite slots and replay the one- and two-trace comparisons."""

import json
from fractions import Fraction as Q
from math import comb

from check_pal_dense_square_payment import display, sub
from check_pal_doubled_ruler import extra, q, three_halves
from check_pal_dyson_window import SCALE, log_int, prime_data
from check_pal_finite_prime_budget import PI, logarithm
from check_pal_rise_direction import add, box, divide, mul, sqrt_box


def log_box(n):
    lo, hi = log_int(n)
    return Q(lo, SCALE), Q(hi, SCALE)


def sixth_prefix(N):
    """Sum 0^6 through (N-1)^6 by the seventh-power telescoping identity."""
    sums = [N]
    for r in range(1, 7):
        value, remainder = divmod(
            N ** (r + 1) - sum(comb(r + 1, j) * sums[j] for j in range(r)),
            r + 1,
        )
        assert remainder == 0
        sums.append(value)
    return sums[6]


def marks(n, b):
    result = set()
    for t in range(1, b - 1):
        d = b * b - t * t
        if 2 * n < 3 * d <= 3 * n:
            assert 1 < b - t <= b + t < d and d == (b - t) * (b + t)
            result.add(d)
    return result


def heads():
    top_k = 18
    flags, _ = prime_data(2 * top_k**4)
    primes = [p for p in range(2, len(flags)) if flags[p]]
    logs = {p: log_int(p) for p in primes}
    results = []
    for k in range(2, top_k + 1):
        n, N = k**4, 2 * k**4
        lo = hi = 0
        for p in primes:
            if p > N:
                break
            if p**8 > n**7:
                w = extra(n, p)
                lo += w * logs[p][0]
                hi += w * logs[p][1]
        tick = sub(log_box(n + 1), log_box(n))
        first, second = marks(n, k * k), marks(n, k * k + 1)
        assert not any(flags[d] for d in first | second)
        if k == 8:
            assert first & second == {3696}
            assert 64**2 - 20**2 == 3696 == 65**2 - 23**2
            assert 44 * 84 == 3696 == 42 * 88
        entries = []
        for holes in (set(), first, first | second):
            refund = sum(extra(n, d) for d in holes)
            bill = max(0, sixth_prefix(N) - 16 * n**7 - refund)
            gap = sub((Q(lo, SCALE), Q(hi, SCALE)), mul(box(n * bill), tick))
            gap = divide(gap, box(N**5 * k**6))
            assert gap[0] > 0 or gap[1] < 0
            entries.append(
                {
                    "distinct_slots": len(holes),
                    "paid": gap[0] > 0,
                    "margin": display(gap, 8),
                }
            )
        results.append(
            {
                "index": k,
                "shared_by_both": len(first & second),
                "by_number_of_traces": entries,
            }
        )
    assert marks(16, 4) == {12, 15} and flags[4**2 + 1] and 17**8 > 16**7
    return results


def contact_price():
    # Polynomial identity tested at 13 distinct rationals. Both sides have degree at most 12.
    coefs = (5, -14, 15, -20, -45, 354, -455)
    for j in range(13):
        u = Q(j, 24)
        x = 1 - u * u
        assert (
            2 * q(x / 2) + 2 * q(x) - u * u
            == sum(v * u ** (2 * i) for i, v in enumerate(coefs)) / 32
        )
    # Divide the integral by sqrt(3) so every coefficient stays rational.
    rational = sum(Q(v, 32 * (2 * i + 1) * 3 ** (i + 1)) for i, v in enumerate(coefs))
    assert rational == Q(6481, 168399)
    c = mul(sqrt_box(3), box(rational))
    lower_moment = add(box(1), divide(box(Q(3, 56)), sqrt_box(2)))[0]
    upper_moment = three_halves(96)
    loss = add(
        box(Q(1, 24)), mul(box(Q(2, 3)), sub((lower_moment, upper_moment), box(1)))
    )
    threshold = sub(c, loss)
    assert -Q(13, 1000) < threshold[0] <= threshold[1] < 0
    assert Q(1, 20) + loss[1] < 2 * c[0] <= 2 * c[1] < Q(1, 7)
    return c, loss, threshold


def constant_at_minus_one(M):
    # The digamma value at 2 is 1-gamma. The Euler product supplies -zeta'/zeta(2).
    tau = logarithm(mul(box(2), PI))
    harmonic = sum((Q(1, k) for k in range(1, M + 1)), Q())
    gamma = sub(box(harmonic), (log_box(M)[0], log_box(M + 1)[1]))
    flags, powers = prime_data(M)
    lo = hi = 0
    unit = 10**22
    for n in range(2, M + 1):
        p = n if flags[n] else powers.get(n, (0, 0))[0]
        if p:
            a, b = log_int(p)
            lo += a * unit // (n * n * SCALE)
            hi += -(-b * unit // (n * n * SCALE))
    tail = (1 + log_box(M)[1]) / M
    constant = add(add(sub(tau, box(1)), gamma), (Q(lo, unit), Q(hi, unit) + tail))
    return tau, constant


def recurrence_samples(threshold):
    tau, constant = constant_at_minus_one(4096)
    examples = {}
    for x in (3, 6):
        # Sum (x-d)Lambda(d) exactly by prime-power labels at x.
        flags, powers = prime_data(x)
        area = box(0)
        for d in range(2, x + 1):
            p = d if flags[d] else powers.get(d, (0, 0))[0]
            if p:
                area = add(area, mul(box(x - d), log_box(p)))
        e = sub(area, box(Q(x * x, 2)))
        count = 16
        trivial = sum(
            Q(1, x ** (2 * a - 1) * 2 * a * (2 * a - 1)) for a in range(1, count + 1)
        )
        tail = Q(1, x ** (2 * count + 1)) / (1 - Q(1, x * x))
        elementary = sub(sub(constant, mul(box(x), tau)), (trivial, trivial + tail))
        z = divide(sub(e, elementary), mul(box(x), sqrt_box(x)))
        assert z[1] < threshold[0] if x == 3 else z[0] > threshold[1]
        examples[str(x)] = display(z)
    return {"zeta_log_derivative_minus_one": display(constant), "phases": examples}


def audit():
    c, loss, threshold = contact_price()
    for N in range(1, 65):
        assert sixth_prefix(N) == sum(r**6 for r in range(N))
    return {
        "integral": display(c, 10),
        "omission_coefficient": display(loss),
        "one_trace_threshold": display(threshold),
        "phase_replay": recurrence_samples(threshold),
        "normalized_margin_definition": "(log prime product - n bill log(1+1/n)) / ((2n)^5 k^6)",
        "boards": heads(),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
