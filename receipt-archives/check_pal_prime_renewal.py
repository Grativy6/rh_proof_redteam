"""Compare both orders of the prime/cofactor sum using exact rational log coefficients."""
from fractions import Fraction as Q
from functools import lru_cache
from math import gcd
import json

from check_pal_growth_windows import sieve
from check_pal_single_parent import Interval, ZERO, log_integer


def plus(*forms):
    out = {}
    for form in forms:
        for key, value in form.items():
            out[key] = out.get(key, Q(0)) + value
    return {k: v for k, v in out.items() if v}


def times(scale, form):
    return {k: scale * v for k, v in form.items() if scale and v}


def rational(value):
    return {0: Q(value)} if value else {}


@lru_cache(maxsize=None)
def integer_log(n):
    assert n >= 1
    divisors = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            divisors[p] = divisors.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        divisors[n] = divisors.get(n, 0) + 1
    return divisors


def log_of(q):
    q = Q(q)
    return plus(integer_log(q.numerator), times(-1, integer_log(q.denominator)))


def encoded(form):
    return {("rational" if p == 0 else str(p)): str(c) for p, c in sorted(form.items())}


def enclosure(form):
    total = ZERO
    for p, c in form.items():
        v = Interval.enclose(1) if not p else log_integer(p)
        total += Interval.enclose(c) * v
    return total


def tail_integral(v):
    # Integral of the plateau/taper from v to 2 against dt/t.
    if v >= 2:
        return {}
    if v <= 1:
        return plus(log_of(1 / v), times(2, log_of(2)), rational(-1))
    return plus(times(2, log_of(2 / v)), rational(v - 2))


def audit_side(x, cutoff):
    x, cutoff = Q(x), Q(cutoff)
    stop = int(2 * x)
    raw, _, primes = sieve(max(2, stop))
    marks = [v if gcd(i, 6) == 1 else 0 for i, v in enumerate(raw)]
    primes = [p for p in primes if p >= 5]
    prefix = [0]
    for v in marks[1:]:
        prefix.append(prefix[-1] + v)

    @lru_cache(maxsize=None)
    def side(y):
        return sum(Q(marks[n], n) * max(Q(0), min(Q(1), 2 - n / y))
                   for n in range(1, int(2 * y) + 1))

    def primitive(y):
        return sum(Q(marks[n], n) * (1 - n / y) for n in range(1, int(y) + 1))

    # The continuum, the primitive primes and the repeat primes are computed separately.
    whole_continuum, large_continuum, integrated_primitive = {}, {}, {}
    for n in range(1, stop + 1):
        if not marks[n]:
            continue
        v = n / x
        factor = Q(marks[n], n)
        whole_continuum = plus(whole_continuum, times(factor, tail_integral(v)))
        large_continuum = plus(large_continuum, times(factor, tail_integral(v * cutoff)))
        start = max(Q(1), v)
        integral = plus(rational(2 - start), times(-v, log_of(2 / start)))
        integrated_primitive = plus(integrated_primitive, times(factor, integral))
    whole_primes, later_primes, repeated = {}, {}, {}
    repeated_count = 0
    for p in primes:
        first = {p: side(x / p) / p}
        whole_primes = plus(whole_primes, first)
        if p > cutoff:
            later_primes = plus(later_primes, first)
        power = p * p
        while power <= stop:
            repeat = side(x / power) / power
            repeated = plus(repeated, {p: repeat})
            repeated_count += bool(repeat)
            power *= p
    wall = plus(integrated_primitive, times(-primitive(x), log_of(2)))
    defect = plus(large_continuum, times(-1, later_primes))
    check = plus(whole_continuum, times(-1, whole_primes), times(-1, repeated), wall)
    assert check == times(side(x), log_of(2 * x))

    # Integrate the signed prime discrepancy against the integer cofactor band.
    paired = {}
    if cutoff < 2 * x:
        corners = {cutoff, 2 * x}
        for n in range(1, stop + 1):
            for y in (x / n, 2 * x / n):
                if cutoff < y < 2 * x:
                    corners.add(y)
        corners.update(Q(p) for p in primes if cutoff < p < 2 * x)
        nodes = sorted(corners)
        for a, b in zip(nodes, nodes[1:]):
            middle = (a + b) / 2
            d = prefix[int(2 * x / middle)] - prefix[int(x / middle)]
            if d:
                elapsed = b - a
                count = {p: -elapsed / p for p in primes if cutoff < p <= middle}
                piece = plus(times(b, log_of(b / cutoff)), times(-a, log_of(a / cutoff)),
                             rational(-elapsed), count)
                paired = plus(paired, times(d / x, piece))
    assert paired == defect
    outer_start = max(Q(1), x)
    outer = plus(times(2, log_of(2 * x / outer_start)), rational(-(2*x - outer_start)/x), {
        p: -(2 - p / x) / p for p in primes if x < p <= 2 * x
    })
    return {"side": str(x), "removed_through": str(cutoff), "nonzero_repeat_terms": repeated_count,
            "paid_repeat_log_coefficients": encoded(repeated),
            "large_prime_defect_enclosure": enclosure(defect).endpoints(),
            "nonzero_log_and_rational_coordinates": len(defect),
            "terminal_cofactor_enclosure": enclosure(outer).endpoints()}


@lru_cache(maxsize=None)
def precise_integer_log(p, count):
    """Two rational sides of log(p), with the error from the positive atanh tail."""
    def series(n, d):
        t = Q(n - d, n + d)
        total = 2 * sum(t**(2 * i + 1) / (2 * i + 1) for i in range(count))
        return total, total + 2 * t**(2 * count + 1) / ((2 * count + 1) * (1 - t*t))
    power = p.bit_length() - 1
    a, b = series(p, 2**power)
    l, r = series(2, 1)
    return a + power*l, b + power*r


def log_sign(form):
    assert 0 not in form
    if not form:
        return 0
    fast = enclosure(form)
    if fast.lower > 0 or fast.upper < 0:
        return 1 if fast.lower > 0 else -1
    # Distinct logs of primes are Q-linearly independent by unique factorization.
    # Thus only the empty coefficient vector is a tie, and refinement terminates.
    count = 24
    while True:
        lo = hi = Q(0)
        for p, c in form.items():
            left, right = precise_integer_log(p, count)
            lo += min(c*left, c*right)
            hi += max(c*left, c*right)
        if lo > 0 or hi < 0:
            return 1 if lo > 0 else -1
        count *= 2


def grid_price(h, removed):
    from math import isqrt
    raw, _, primes = sieve(2 * h)
    m = [v if gcd(k, 6) == 1 else 0 for k, v in enumerate(raw)]
    primes = [p for p in primes if p >= 5]

    @lru_cache(maxsize=None)
    def side(x):
        return sum((Q(m[n], n) * min(Q(1), 2 - n/x) for n in range(1, int(2*x)+1)), Q(0))

    largest = 0
    witness = 1
    older_cut = min(h, h.bit_length()**2)
    trimmed = 0
    trimmed_witness = 1
    counted = 0
    for d in range(1, 2*h+1):
        x = Q(h, d)
        top = int(2*x)
        cutoff = max(removed, ((top.bit_length()-1)//160)**2)
        raw_log = {}
        for n in range(1, top+1):
            if m[n]:
                coeff = Q(m[n], n) * min(Q(1), 2 - n/x)
                raw_log = plus(raw_log, times(coeff, log_of(x/n)))
        for p in primes:
            if p > top:
                break
            if p > cutoff:
                raw_log = plus(raw_log, {p: -side(x/p) / p})
        floor_root = isqrt(x.numerator // x.denominator)
        ceil_root = floor_root + int(floor_root**2 != x)
        distance = times(h * ceil_root * log_sign(raw_log), raw_log)
        unit = log_of(4*x)

        def passes(k):
            return log_sign(plus(times(k, unit), times(-1, distance))) >= 0

        def raise_to_price(previous):
            if passes(previous):
                return previous
            low, high = previous, max(1, 2*previous)
            while not passes(high):
                low, high = high, 2*high
            while low + 1 < high:
                mid = (low + high) // 2
                if passes(mid):
                    high = mid
                else:
                    low = mid
            assert passes(high) and not passes(high-1)
            return high

        new = raise_to_price(largest)
        if new > largest:
            largest, witness = new, d
        if x >= older_cut:
            counted += 1
            new = raise_to_price(trimmed)
            if new > trimmed:
                trimmed, trimmed_witness = new, d
    assert counted == h // older_cut and trimmed <= largest

    return {"head": h, "removed_through": removed, "quotient_rows": 2*h,
            "denominator": h, "minimal_numerator": largest, "price": str(Q(largest, h)),
            "row_requiring_the_numerator": witness,
            "cofactor_on_that_row": str(Q(h, witness)),
            "minimum_retained_age": older_cut,
            "remaining_rows_including_cut": counted,
            "trimmed_price": str(Q(trimmed, h)), "trimmed_witness": str(Q(h, trimmed_witness))}


if __name__ == "__main__":
    tests = [audit_side(Q(3, 4), 5), audit_side(4, 5), audit_side(10, 5), audit_side(13, 5),
             audit_side(Q(127, 2), 11), audit_side(128, 31), audit_side(512, 31)]
    assert tests[3]["paid_repeat_log_coefficients"] == {"5": "1/325"}
    assert Q(tests[1]["terminal_cofactor_enclosure"][0]) > 0
    assert Q(tests[2]["terminal_cofactor_enclosure"][1]) < 0
    grids = [grid_price(h, r) for h in (1, 4, 16, 81, 256, 625) for r in (5, 31)]
    print(json.dumps({"two_orders_of_the_sum": tests, "exact_integer_price_grids": grids}, indent=2))
