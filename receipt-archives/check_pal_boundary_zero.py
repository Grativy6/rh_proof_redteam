"""Enclose an actual critical zero and the signed factorial boundary response, without a zero table."""

from fractions import Fraction as Q
from math import isqrt
import json

from check_pal_dyson_window import (
    SCALE,
    ZERO,
    plus,
    minus,
    times,
    natural,
    ceil_div,
    integer_box,
    interval_text,
    log_int,
    inverse_root,
    small_series,
    scaled_div,
)
from check_pal_dense_square_payment import arctan_inverse, sub, display
from check_pal_rise_direction import box, mul, divide, sqrt_box

ONE = (SCALE, SCALE)
PI = integer_box(sub(mul(box(16), arctan_inverse(5)), mul(box(4), arctan_inverse(239))))
HEIGHT = (Q(1413472, 100000), Q(1413474, 100000))


def rational(q):
    return integer_box((Q(q), Q(q)))


def by_int(x, k):
    return x[0] // k, ceil_div(x[1], k)


def neg(x):
    return -x[1], -x[0]


def sin_cos(arg):
    # Exact points and narrow intervals in [-128,128]. Fourteen pairs suffice after reduction.
    u = by_int(arg, 128)
    if max(abs(u[0]), abs(u[1])) > SCALE:
        raise ValueError("argument exceeds the stated trigonometric range")
    sq = times(u, u)
    sn = u
    cs = ONE
    st = u
    ct = ONE
    for k in range(1, 15):
        ct = neg(by_int(times(ct, sq), (2 * k - 1) * (2 * k)))
        st = neg(by_int(times(st, sq), (2 * k) * (2 * k + 1)))
        cs = plus(cs, ct)
        sn = plus(sn, st)
    cs = cs[0] - 1, cs[1] + 1
    sn = sn[0] - 1, sn[1] + 1
    for _ in range(7):
        # Squaring cos alone is less stable near pi/4 than the two-coordinate rotation.
        nc = minus(times(cs, cs), times(sn, sn))
        ns = natural(2, times(sn, cs))
        cs, sn = nc, ns
    return sn, cs


def exp_minus(a):
    m = 1
    while a[1] > m * SCALE:
        m *= 2
    r = scaled_div(ONE, small_series(by_int(a, m), "exp"))
    while m > 1:
        r = times(r, r)
        m //= 2
    return r


def theta_bracket(per_unit=4096):
    count = 8 * per_unit
    q0 = exp_minus(PI)
    step = exp_minus(by_int(PI, per_unit))
    first = q0
    total = [ZERO, ZERO]
    logbase = log_int(per_unit)
    for i in range(count + 1):
        n = per_unit + i
        logx = minus(log_int(n), logbase)
        low = isqrt(isqrt(SCALE**4 * per_unit**3 // n**3))
        power = low, low + (low**4 * n**3 < SCALE**4 * per_unit**3)
        sq = times(first, first)
        weight = times(plus(first, times(sq, sq)), power)
        simpson = 1 if i in (0, count) else 4 if i % 2 else 2
        for k, t in enumerate(HEIGHT):
            _, cos = sin_cos(times(rational(t / 2), logx))
            total[k] = plus(total[k], natural(simpson, times(weight, cos)))
        first = times(first, step)
    # For m=1,2, the fourth derivative is bounded in total by 2000, uniformly on [1,9].
    # The integral tails for x>9 or m>=3 are below 3e-12 since exp(3)>20.
    error = Q(8 * 2000, 180 * per_unit**4) + Q(3, 10**12)
    out = []
    for k, t in enumerate(HEIGHT):
        integ = plus(by_int(total[k], 3 * per_unit), integer_box((-error, error)))
        xi = minus(rational(Q(1, 2)), times(rational(t * t + Q(1, 4)), integ))
        out.append(interval_text(xi, 13))
    assert Q(out[0][0]) > 0 and Q(out[1][1]) < 0
    return {
        "heights": [str(t) for t in HEIGHT],
        "panels": count,
        "fourth_derivative_bound": 2000,
        "integral_tail_bound": "3/1000000000000",
        "xi_at_endpoints": out,
    }


def cmul(a, b):
    return minus(times(a[0], b[0]), times(a[1], b[1])), plus(times(a[0], b[1]), times(a[1], b[0]))


def cadd(a, b):
    return plus(a[0], b[0]), plus(a[1], b[1])


def cneg(a):
    return neg(a[0]), neg(a[1])


def cscale(a, k):
    return times(a[0], k), times(a[1], k)


def reciprocal(a):
    sq = plus(times(a[0], a[0]), times(a[1], a[1]))
    return scaled_div(a[0], sq), scaled_div(neg(a[1]), sq)


def power_minus(n):
    L = log_int(n)
    center = (HEIGHT[0] + HEIGHT[1]) / 2
    sn, cs = sin_cos(times(rational(center), L))
    radius = ceil_div(
        (HEIGHT[1] - HEIGHT[0]).numerator * L[1], 2 * (HEIGHT[1] - HEIGHT[0]).denominator
    )
    err = (-radius, radius)
    return cscale((plus(cs, err), neg(plus(sn, err))), inverse_root(n))


def derivative(N=256):
    # Differentiate the Euler--Maclaurin representation through B2; the fractional B2 is bounded by 1/6.
    z = (rational(Q(1, 2)), integer_box(HEIGHT))
    h = (minus(z[0], ONE), z[1])
    inv = reciprocal(h)
    value = (ZERO, ZERO)
    for n in range(2, N):
        value = cadd(value, cneg(cscale(power_minus(n), log_int(n))))
    L = log_int(N)
    v = power_minus(N)
    value = cadd(value, cmul(cscale(v, rational(N)), cneg(cadd(cscale(inv, L), cmul(inv, inv)))))
    value = cadd(value, cneg(cscale(v, by_int(L, 2))))
    value = cadd(
        value, cmul(cscale(v, rational(Q(1, 12 * N))), cadd((ONE, ZERO), cneg(cscale(z, L))))
    )
    # |2s+1| < 31; |s(s+1)| < 225 throughout this box.
    rem = (Q(31) + 225 * (Q(L[1], SCALE) + Q(2, 3))) / (18 * N * isqrt(N))
    broad = integer_box((-rem, rem))
    re, im = plus(value[0], broad), plus(value[1], broad)
    maxsq = Q(max(abs(re[0]), abs(re[1])) ** 2 + max(abs(im[0]), abs(im[1])) ** 2, SCALE**2)
    upper = sqrt_box(maxsq)[1]
    assert re[0] > 0 and upper < 1
    t = integer_box(HEIGHT)
    _, cos = sin_cos(times(t, log_int(2)))
    K = scaled_div(natural(2, minus(ONE, cos)), times(t, t))
    limit = Q(K[0], SCALE) / upper
    assert limit > Q(1, 50)
    return {
        "terms_before_endpoint": N - 1,
        "zeta_prime_real": interval_text(re, 8),
        "zeta_prime_imag": interval_text(im, 8),
        "derivative_modulus_upper": display((upper, upper), 8)[1],
        "dyson_mass_at_zero": interval_text(K, 9),
        "residue_modulus_lower": display((limit, limit), 8)[0],
    }


if __name__ == "__main__":
    print(json.dumps({"critical_zero": theta_bracket(), "simple_pole": derivative()}, indent=2))
