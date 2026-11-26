"""Rigorous finite prime-error ledger for the returned boards at indices 22 and 23."""

import json
from fractions import Fraction as Q

from check_pal_dense_square_payment import ln, arctan_inverse, display
from check_pal_rise_direction import add, box, divide, flip, mul, sqrt_box
from check_pal_single_parent import Interval, Box, ZERO, SCALE, exponential


def sub(a, b):
    return add(a, flip(b))


def sum_boxes(*pieces):
    result = box(0)
    for piece in pieces:
        result = add(result, piece)
    return result


def times(*pieces):
    result = box(1)
    for piece in pieces:
        result = mul(result, piece)
    return result


def root(v):
    return sqrt_box(v[0])[0], sqrt_box(v[1])[1]


def logarithm(v):
    # Round outward before taking logarithms of nested rational endpoints.
    unit = 10**18
    lo = Q(v[0] * unit // 1, unit)
    hi = Q(-(-v[1] * unit // 1), unit)
    assert lo > 0
    return ln(lo)[0], ln(hi)[1]


def exp_box(v):
    result = exponential(Box(Interval.enclose(*v), ZERO)).real
    return Q(result.lower, SCALE), Q(result.upper, SCALE)


def hyperbolics(v):
    positive, negative = exp_box(v), exp_box(flip(v))
    return mul(box(Q(1, 2)), sub(positive, negative)), mul(box(Q(1, 2)), add(positive, negative))


PI = sub(mul(box(16), arctan_inverse(5)), mul(box(4), arctan_inverse(239)))
C = 35
T = 3 * 10**12
EPS = Q(C, T)
A = Q(1, 4)
START = 10**26


def conditional_shape(y):
    """Schoenfeld's bound, used only in Johnston's published finite range."""
    assert 599 <= y <= 1101 * 10**23
    return add(divide(times(sqrt_box(y), ln(y), ln(y)), mul(box(8), PI)), ln(y))


def upper_envelope(left, right):
    assert START <= left <= right and EPS <= Q(1, 10**4)
    assert C >= 3 and A * T >= 5000 and C / EPS == T
    sinh, _ = hyperbolics(box(C))
    _, cosh = hyperbolics(mul(box(C), sqrt_box(1 - A * A)))
    root_right = sqrt_box(right)
    i1_upper = divide(box(1), root(times(box(2 * C), PI)))
    b0 = times(box(Q(98, 100) * EPS * left), i1_upper, exp_box(box(-EPS)))
    assert b0[0] > 1
    small_log = logarithm(divide(box(A * T), mul(box(2), PI)))
    small = divide(times(root_right, small_log, small_log), mul(box(2), PI))
    middle = divide(
        times(box(1 + 11 * C * EPS), ln(T), cosh, root_right), times(PI, box(C * A * A), sinh)
    )
    high = divide(
        times(
            box(Q(16, 100) * (right + 1)),
            exp_box(mul(box(Q(71, 100)), sqrt_box(C * EPS))),
            ln(3 * C),
            ln(T),
        ),
        sinh,
    )
    correction = times(
        exp_box(box(2 * EPS)),
        add(ln(right), box(EPS)),
        sum_boxes(
            divide(times(box(2 * EPS * right), i1_upper), logarithm(b0)),
            mul(box(Q(201, 100) * EPS), root_right),
            mul(box(Q(1, 2)), logarithm(ln(2 * right * right))),
        ),
    )
    # Prime powers and a possible half-weight convention at the endpoint.
    log_two = right.bit_length() - 1
    cube_upper = 2 ** ((log_two + 1 + 2) // 3)
    assert cube_upper**3 >= right
    powers = mul(ln(4), add(root_right, box(log_two * cube_upper)))
    endpoint = ln(right)
    total = sum_boxes(small, middle, high, correction, box(2), powers, endpoint)
    components = {
        "low_zeros": small,
        "middle_zeros": middle,
        "unrestricted_high_zeros": high,
        "removing_smoothing": correction,
        "prime_power_correction": powers,
        "endpoint_convention": endpoint,
        "constant_in_explicit_formula": box(2),
    }
    return total, {
        "interval": [left, right],
        "lower_bound_denominator_log": display(logarithm(b0)),
        "theta_upper_envelope_in_sqrt_right_units": display(divide(total, root_right)),
        "components_in_sqrt_right_units": {
            k: display(divide(v, root_right)) for k, v in components.items()
        },
    }


def board(j, cuts):
    x = 4 ** (j + 1) * (j + 1) ** 2
    M = 16**j
    limit = cuts[-1]
    assert 599 < x < START <= limit <= M
    assert cuts[0] == START
    below = conditional_shape(START)
    bands = []
    total = below[1]
    for left, right in zip(cuts, cuts[1:]):
        amount, entry = upper_envelope(left, right)
        bands.append(entry)
        total = max(total, amount[1])
    # Absolute coarse upper bound on the price, in whole prime-weight units.
    root_error = conditional_shape(x)
    all_draw = total + root_error[1] + Q(3 * limit, x)
    guard = -(-M // x)
    usable = x // 13 - guard
    assert all_draw < usable
    return {
        "j": j,
        "x": x,
        "board": x * x,
        "full_horizon": M,
        "all_cuts_through": limit,
        "covers_whole_board": limit == M,
        "guard_columns": guard,
        "usable_row_quota": usable,
        "normalized_by": "sqrt(full_horizon)",
        "prime_and_rounding_cost_upper_bound": display(box(all_draw / (4**j))),
        "available_row_quota": display(box(Q(usable, 4**j))),
        "integer_units_of_row_margin_at_least": int(usable - all_draw),
        "earlier_range_and_root": "Johnston Corollary 3.3; the additive log bounds any endpoint convention.",
        "slab_envelopes": bands,
    }


def bessel_price():
    """Check the coefficient at c=35 independently from the positive Bessel series."""
    c = Q(C)
    term = total = c / 2
    for k in range(80):
        term *= c * c / (4 * (k + 1) * (k + 2))
        total += term
    ratio = c * c / (4 * 81 * 82)
    assert 0 < ratio < 1
    series = (total, total + term * ratio / (1 - ratio))
    sinh, _ = hyperbolics(box(C))
    factor = divide(series, mul(box(2), sinh))
    scaled = mul(factor, root(times(box(2 * C), PI)))
    assert scaled[0] > Q(98, 100) and scaled[1] < 1
    return {"normalized_bessel_interval": display(scaled, 12), "last_series_index": 80}


def decimal_replay(entries):
    """Separate 75-digit arithmetic checks the source formulas component by component."""
    from decimal import Decimal as D, localcontext

    with localcontext() as ctx:
        ctx.prec = 75

        def atan_inv(n):
            v = D(1) / n
            return sum((-1) ** k * v ** (2 * k + 1) / (2 * k + 1) for k in range(90))

        pi = 16 * atan_inv(5) - 4 * atan_inv(239)
        c, t, a = D(C), D(T), D(1) / 4
        ep = c / t
        sinh = (c.exp() - (-c).exp()) / 2
        b = c * (1 - a * a).sqrt()
        cosh = (b.exp() + (-b).exp()) / 2
        for item in entries:
            left, right = map(D, item["interval"])
            base = D("0.98") * ep * left * (-ep).exp() / (2 * pi * c).sqrt()
            u = right.sqrt()
            low = (a * t / (2 * pi)).ln() ** 2 / (2 * pi)
            mid = (1 + 11 * c * ep) * t.ln() * cosh / (pi * c * a * a * sinh)
            high = (
                D("0.16")
                * (right + 1)
                * (D("0.71") * (c * ep).sqrt()).exp()
                * (3 * c).ln()
                * t.ln()
                / (sinh * u)
            )
            smear = (
                (2 * ep).exp()
                * (right.ln() + ep)
                * (
                    2 * ep * right / ((2 * pi * c).sqrt() * base.ln())
                    + D("2.01") * ep * u
                    + (2 * right * right).ln().ln() / 2
                )
                / u
            )
            for name, actual in [
                ("low_zeros", low),
                ("middle_zeros", mid),
                ("unrestricted_high_zeros", high),
                ("removing_smoothing", smear),
            ]:
                lo, hi = map(D, item["components_in_sqrt_right_units"][name])
                assert lo <= actual <= hi, (name, actual, lo, hi)
    return len(entries)


if __name__ == "__main__":
    m = 16**22
    data = {
        "finite_zero_height": T,
        "smoothing_c": C,
        "epsilon": str(EPS),
        "low_zero_fraction": str(A),
        "boards": [board(22, [START, m]), board(23, [START, m, 2 * m, 4 * m, 6 * m, 8 * m])],
    }
    data["bessel_at_selected_c"] = bessel_price()
    slabs = [entry for b in data["boards"] for entry in b["slab_envelopes"]]
    data["decimal_replayed_slabs"] = decimal_replay(slabs)
    high = 16**23
    end_bound, _ = upper_envelope(3 * high // 4, high)
    x = 4**24 * 24**2
    data["full_next_head_control"] = {
        "normalized_upper_envelope": display(divide(end_bound, sqrt_box(high))),
        "normalized_row_quota": display(box(Q(x // 13 - (-(-high // x)), 4**23))),
        "covers_full_head_by_this_envelope": False,
    }
    assert end_bound[0] > x // 13
    print(json.dumps(data, indent=2))
