"""Measure the two signs of the actual PAL edge using one finite positive kernel."""
import json
from fractions import Fraction as Q
from functools import lru_cache
from math import gcd, isqrt

from check_pal_growth_windows import sieve
from check_pal_single_parent import Interval, SCALE, ZERO, log_ratio


@lru_cache(maxsize=None)
def root(q):
    q = Q(q)
    assert q >= 0
    scaled = q * SCALE**2
    low = isqrt(scaled.numerator // scaled.denominator)
    return Interval(low, low if low**2 == scaled else low + 1)


def log_between_one_and_two(q):
    q = Q(q)
    assert 1 <= q <= 2
    return log_ratio(q.numerator, q.denominator)


def smooth_source(limit):
    """Exactly the positive 2,3-smooth labels within the cutoff."""
    a = 1
    while a <= limit:
        n = a
        while n <= limit:
            yield n
            n *= 3
        a *= 2


def source_difference(x):
    """The normalized signed difference from the positive source only."""
    total = ZERO
    for q in smooth_source(2 * x):
        lo, hi = Q(q, 2), min(Q(q), Q(x))
        if lo < hi:
            total += ((root(1 / lo) - root(1 / hi)) * Interval.enclose(2)
                      - root(Q(1, x)) * log_between_one_and_two(hi / lo))
    return total


def physical_difference(x):
    """Integrate the signed marks on every cell where both coefficients are fixed."""
    mu, _, _ = sieve(2 * x)
    marks = [v if gcd(n, 6) == 1 else 0 for n, v in enumerate(mu)]
    cuts = {Q(n, 2) for n in range(1, 2 * x + 1)}
    cuts.update(Q(x, d) for d in range(1, 2 * x + 1))
    roots = [ZERO]
    for d in range(1, 2 * x + 1):
        roots.append(roots[-1] + root(Q(1, d)))
    positive, negative = ZERO, ZERO

    def pieces(left, right, intercept, band):
        if intercept:
            cross = Q(band, 1) / intercept
            if left < cross < right:
                return ((left, cross), (cross, right))
        return ((left, right),)

    ordered = sorted(cuts)
    for left, right in zip(ordered, ordered[1:]):
        middle = (left + right) / 2
        n, top = int(middle), int(2 * middle)
        intercept = sum(Q(marks[d], d) for d in range(1, n + 1))
        intercept += 2 * sum(Q(marks[d], d) for d in range(n + 1, top + 1))
        band = sum(marks[n + 1 : top + 1])
        count = int(x / middle)
        for a, b in pieces(left, right, intercept, band):
            if not intercept and not band:
                continue
            flat = Interval.enclose(intercept * (b - a)) - Interval.enclose(band) * log_between_one_and_two(b / a)
            curved = (Interval.enclose(intercept) * (root(b) - root(a))
                      + Interval.enclose(band) * (root(1 / b) - root(1 / a)))
            contribution = Interval.enclose(count) * root(Q(1, x)) * flat - roots[count] * curved
            if intercept - 2 * band / (a + b) >= 0:
                positive += contribution
            else:
                negative -= contribution
    diff = positive - negative
    predicted = source_difference(x)
    assert max(diff.lower, predicted.lower) <= min(diff.upper, predicted.upper)
    assert predicted.lower >= 0 and predicted.upper < 7 * SCALE
    assert diff.upper - diff.lower < SCALE // 10**9
    return {"cut": x, "positive": positive.endpoints(), "negative": negative.endpoints(),
            "direct_difference": diff.endpoints(), "smooth_source_difference": predicted.endpoints()}


def direct_crossing(mu, crossing, scale):
    """Price the two sides of the first crossing directly from the definition."""
    rows = []
    for h in (crossing - 1, crossing):
        low = 0
        inexact = 0
        for residue in (1, 5):
            for n in range(residue, 2 * h + 1, 6):
                if mu[n]:
                    numerator = mu[n] * scale * (h if n <= h else 2 * h - n)
                    step, rem = divmod(numerator, h * n)
                    low += step
                    inexact += bool(rem)
        rows.append([str(Q(low, scale)), str(Q(low + inexact, scale))])
    assert Q(rows[0][0]) > 0 and Q(rows[1][1]) < 0
    return rows


def sparse_ledger(final=52):
    """Independent outward unit-step recurrence at every side through final**4."""
    scale = 10**22
    heights = {j**4: j for j in range(1, final + 1)}
    limit = final**4
    mu, _, _ = sieve(2 * limit + 1)
    def mark(n):
        return mu[n] if n % 6 in (1, 5) else 0
    low = scale
    inexact = band = 0
    pos_low = pos_high = neg_low = neg_high = 0
    negative_first = None
    earlier_undecided = 0
    checkpoints = []
    true_bands = []
    for h in range(1, limit + 1):
        high = low + inexact
        if negative_first is None:
            if high < 0:
                negative_first = h
            elif low <= 0:
                earlier_undecided += 1
        if h in heights:
            j = heights[h]
            pos_low += j * max(low, 0)
            pos_high += j * max(high, 0)
            neg_low += j * max(-high, 0)
            neg_high += j * max(-low, 0)
            if j in (4, 8, 16, 32, 48, 50, 51, 52):
                checkpoints.append({
                    "j": j, "side": h, "slope": [str(Q(low, scale)), str(Q(high, scale))],
                    "positive_sum": [str(Q(pos_low, scale)), str(Q(pos_high, scale))],
                    "negative_sum": [str(Q(neg_low, scale)), str(Q(neg_high, scale))],
                })
            if j in (50, 51, 52):
                width = 2048
                drift = Q(width * (abs(band) + 3 * width + 2), h*h)
                a, b = Q(low, scale) - drift, Q(high, scale) + drift
                assert a > 0 or b < 0
                magnitude = a if a > 0 else -b
                x = limit + width
                # q(X/y)>=1/5 throughout. The bracket prices this band's
                # actual contribution to the corresponding sign at the same X.
                min_charge = Interval.enclose(magnitude * width / 5) * root(Q(1, h + width))
                assert min_charge.lower > 0
                true_bands.append({"begin": h, "end": h + width, "common_cut": x,
                                   "band_count_at_begin": band, "sign": "+" if a > 0 else "-",
                                   "weighted_area_lower": str(Q(min_charge.lower, SCALE))})
        if h < limit:
            first = mark(2 * h + 1)
            numerator = band * (2 * h + 1) + h * first
            denominator = h * (h + 1) * (2 * h + 1)
            step, rem = divmod(scale * numerator, denominator)
            low += step
            inexact += bool(rem)
            band += first - mark(h + 1)
    assert [t["sign"] for t in true_bands] == ["+", "-", "+"]
    return {"last_side": limit, "sieve_upper_limit": 2 * limit + 1, "rounding_denominator": scale,
            "first_certified_negative_side": negative_first,
            "previous_signs_not_resolved": earlier_undecided,
            "direct_check_before_and_at_first_crossing": direct_crossing(mu, negative_first, scale),
            "checkpoints": checkpoints, "separately_certified_sign_bands": true_bands,
            "whole_signed_difference_at_common_cut": source_difference(limit + 2048).endpoints()}


def phase_test():
    """Enclose the actual normalized Laplace response by a finite trapezoid sum."""
    from check_pal_single_parent import Box, exponential, log_integer

    sigma, height = Q(9, 16), Q(133, 4)
    terms = 256
    real = Interval.enclose
    minus_s = Box(real(-sigma), real(-height))
    total = Box(ZERO, ZERO)
    for n in range(1, terms):
        total += exponential(minus_s.times_real(log_integer(n)))
    last = exponential(minus_s.times_real(log_integer(terms)))
    divisor = (sigma - 1)**2 + height**2
    inv = Box(real((sigma - 1) / divisor), real(-height / divisor))
    total += last * (inv.times_real(real(terms)) + Box(real(Q(1, 2)), ZERO))
    # |s|<34, |s+1|<35, 8*(1+sigma)>12 and 256**(-1-sigma)<2**(-12).
    remainder = Q(34 * 35, 12 * 2**12)
    zeta = Box(total.real + Interval.enclose(-remainder, remainder),
               total.imag + Interval.enclose(-remainder, remainder))
    modulus = sigma**2 + height**2
    factor = Box(real((1 - sigma / modulus) / 2), real(height / (2 * modulus)))
    response = factor * zeta
    assert response.real.upper < -SCALE // 100
    assert response.imag.lower > SCALE // 6
    return {"s_real": str(sigma), "s_imaginary": str(height), "terms_before_endpoint": terms - 1,
            "zeta_remainder_absolute": str(remainder), "response_real": response.real.endpoints(),
            "response_imaginary": response.imag.endpoints()}


if __name__ == "__main__":
    print(json.dumps({"two_independent_integrals": [physical_difference(x) for x in (1, 4, 16, 64, 144)],
                      "fourth_power_accounts": sparse_ledger(), "fixed_phase_test": phase_test()}, indent=2))
