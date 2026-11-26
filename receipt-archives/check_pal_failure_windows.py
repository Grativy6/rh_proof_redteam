"""Replay normalized shortfalls on genuine quartic heads and the scale comparisons."""

import json
from bisect import bisect_right
from fractions import Fraction as Q
from math import factorial

from check_pal_doubled_ruler import extra
from check_pal_dyson_window import SCALE, log_int, prime_data


def box(lo, hi, places=10):
    power = 10**places
    a = lo.numerator * power // lo.denominator
    b = -(-hi.numerator * power // hi.denominator)

    def show(n):
        sign = "-" if n < 0 else ""
        whole, fraction = divmod(abs(n), power)
        return f"{sign}{whole}.{fraction:0{places}d}"

    return [show(a), show(b)]


def data():
    indices = (2, 3, 5, 8, 12, 16, 24)
    cap = 2 * indices[-1] ** 4
    prime, _ = prime_data(cap)
    primes = [p for p in range(2, cap + 1) if prime[p]]
    logs = {p: log_int(p) for p in primes}
    ans = []
    for k in indices:
        n = k**4
        N = 2 * n
        bottom = top = area_lo = area_hi = 0
        for p in primes[: bisect_right(primes, N)]:
            lo, hi = logs[p]
            if n**7 < p**8:
                w = extra(n, p)
                bottom += lo * w
                top += hi * w
            d = p
            while d <= n:
                area_lo += (n - d) * lo
                area_hi += (n - d) * hi
                d *= p
        nl, nh = log_int(n)
        next_lo, next_hi = log_int(n + 1)
        tick = N**5 * n * (n - k**2) ** 2
        denom = 14 * SCALE * N**5 * k**6
        short_lo = Q(tick * (next_lo - nh) - 14 * top, denom)
        short_hi = Q(tick * (next_hi - nl) - 14 * bottom, denom)
        e_lo = Q(2 * area_lo - n * n * SCALE, 2 * SCALE * k**6)
        e_hi = Q(2 * area_hi - n * n * SCALE, 2 * SCALE * k**6)
        assert short_hi < 0
        ans.append(
            {
                "index": k,
                "normalized_clock_shortfall": box(short_lo, short_hi),
                "normalized_prime_area_error": box(e_lo, e_hi),
                "clock_less_area": box(short_lo - e_hi, short_hi - e_lo),
            }
        )
    return ans


def exponent_control(theta, eta):
    d = min((theta - Q(1, 2)) / 4, eta / 32)
    assert 0 < d and Q(1, 2) < theta - d
    assert 1 + theta - 2 * d < 1 + theta - d
    assert 1 - 8 * d > 1 - eta and 1 - 2 * d > Q(3, 4)
    return {
        "position": str(theta),
        "window_saving": str(eta),
        "chosen_loss": str(d),
        "physical_excursion_exponent": str(1 + theta - d),
        "physical_width_exponent": str(1 - 2 * d),
        "index_width_exponent": str(1 - 8 * d),
    }


def aligned_sample(K):
    top = 1
    while factorial(top + 1) ** (top + 1) <= 2 * K:
        top += 1
    frame = factorial(top)
    head = (K // frame + 1) * frame
    assert K <= head <= 2 * K and all(head % factorial(j) == 0 for j in range(1, top + 1))
    assert factorial(top + 1) ** (top + 1) > head
    return {"start": K, "factorial_order": top, "aligned_index": head}


def audit():
    # In the smooth negative control the two exact real phases are separated by pi.
    assert Q(9, 8) ** 3 < 2
    examples = [
        exponent_control(t, e)
        for t in (Q(500001, 1000000), Q(3, 4), Q(1))
        for e in (Q(1, 100), Q(1, 4))
    ]
    return {
        "aligned_examples": [aligned_sample(x) for x in (215, 216, 331775, 331776, 10**11)],
        "actual_heads": data(),
        "symbolic_exponent_controls": examples,
        "sampling_condition": "Any fixed power saving in the start-to-hit length is sufficient on paper.",
        "exact_log_observable": "(demand(k)/14 - earned(k^4))/k^6",
        "source_terms": "Johnston Lemma 2.8 at c=0, integrated explicit formula, and the unconditional zero count.",
        "smooth_control_factor": "9/8",
        "smooth_control_is_actual_prime_stream": False,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
