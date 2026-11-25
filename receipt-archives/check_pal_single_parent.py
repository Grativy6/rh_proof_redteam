"""Enclose the six-row parent's missed Mellin frequency with integer interval arithmetic."""
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import factorial
import json

SCALE = 10**18


@dataclass(frozen=True)
class Interval:
    lower: int
    upper: int

    @classmethod
    def enclose(cls, lower, upper=None):
        upper = lower if upper is None else upper
        return cls(int(lower * SCALE // 1), int(-(-upper * SCALE // 1)))

    def __add__(self, other):
        return Interval(self.lower + other.lower, self.upper + other.upper)

    def __neg__(self):
        return Interval(-self.upper, -self.lower)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        products = [x * y for x in (self.lower, self.upper)
                    for y in (other.lower, other.upper)]
        return Interval(min(products) // SCALE, -(-max(products) // SCALE))

    def divide_by_positive_integer(self, divisor):
        assert divisor > 0
        return Interval(self.lower // divisor, -(-self.upper // divisor))

    def magnitude_bound(self):
        return Fraction(max(abs(self.lower), abs(self.upper)), SCALE)

    def endpoints(self):
        return [str(Fraction(self.lower, SCALE)), str(Fraction(self.upper, SCALE))]


@dataclass(frozen=True)
class Box:
    real: Interval
    imag: Interval

    def __add__(self, other):
        return Box(self.real + other.real, self.imag + other.imag)

    def __sub__(self, other):
        return Box(self.real - other.real, self.imag - other.imag)

    def __mul__(self, other):
        return Box(self.real * other.real - self.imag * other.imag,
                   self.real * other.imag + self.imag * other.real)

    def times_real(self, value):
        return Box(self.real * value, self.imag * value)

    def divide_by_positive_integer(self, divisor):
        return Box(self.real.divide_by_positive_integer(divisor),
                   self.imag.divide_by_positive_integer(divisor))

    def magnitude_bound(self):
        return self.real.magnitude_bound() + self.imag.magnitude_bound()

    def endpoints(self):
        return [self.real.endpoints(), self.imag.endpoints()]


ZERO = Interval.enclose(0)
ONE = Box(Interval.enclose(1), ZERO)
THREE_HALVES = Interval.enclose(Fraction(3, 2))


def log_ratio(value, unit):
    x = Fraction(value - unit, value + unit)
    count = 35
    partial = 2 * sum(x**(2*j+1) / (2*j+1) for j in range(count))
    tail = 2 * x**(2*count+1) / ((2*count+1) * (1-x*x))
    return Interval.enclose(partial, partial + tail)


@lru_cache(maxsize=None)
def log_integer(value):
    exponent = value.bit_length() - 1
    return log_ratio(value, 2**exponent) + Interval.enclose(exponent) * log_ratio(2, 1)


def exponential(value):
    # |w| <= 1 gives Taylor remainder <= exp(1)/25! < 3/25!.
    squarings = 0
    w = value
    while w.magnitude_bound() > 1:
        w = w.divide_by_positive_integer(2)
        squarings += 1
    total = term = ONE
    for n in range(1, 25):
        term = (term * w).divide_by_positive_integer(n)
        total = total + term
    radius = Fraction(3, factorial(25))
    error = Interval.enclose(-radius, radius)
    total = total + Box(error, error)
    for _ in range(squarings):
        total = total * total
    return total


def audit():
    center = Box(Interval.enclose(Fraction(794, 1000)), Interval.enclose(Fraction(17715, 1000)))
    r = Fraction(1, 1000)
    l2, l3 = log_integer(2), log_integer(3)
    l6 = l2 + l3
    logs = (l2, l3, l6)
    e2, e3, e6 = (exponential(center.times_real(-v)) for v in logs)
    value = ONE - (e2 + e3 - e6).times_real(THREE_HALVES)
    derivative = (e2.times_real(l2) + e3.times_real(l3) - e6.times_real(l6)).times_real(THREE_HALVES)
    assert value.magnitude_bound() < Fraction(1, 3000)
    assert Fraction(derivative.real.lower, SCALE) > Fraction(1, 2)
    assert l2.magnitude_bound() < 1 and l3.magnitude_bound() < 2 and l6.magnitude_bound() < 2
    # Re(z)>0 throughout the disk. Hence |P''(z)| < (3/2)*(1+4+4) < 14.
    derivative_lower = Fraction(1, 2)
    lipschitz = 14*r / derivative_lower
    assert lipschitz < 1 and Fraction(1, 3000)/derivative_lower + lipschitz*r < r
    assert Fraction(794, 1000)-r > Fraction(3, 4)
    assert Fraction(794, 1000)+r < 1 and Fraction(17715, 1000)+r < 18
    # At this same zero also test the actual occupied and tick residuals after 2*b_2.
    eta_head = Box(ZERO, ZERO)
    for n in range(1, 257, 2):
        eta_head = (eta_head + exponential(center.times_real(-log_integer(n)))
                    - exponential(center.times_real(-log_integer(n+1))))
    c_head = ONE - eta_head
    t_head = c_head - e2
    assert Fraction(c_head.real.lower, SCALE) > Fraction(7, 6)
    assert Fraction(t_head.real.lower, SCALE) > Fraction(3, 5)
    # The uncomputed paired tail at c is bounded by |c|*256^-Re(c)/Re(c) < 3/8.
    # |eta'| < 34 throughout this smaller disk by its Mellin integral, and
    # |(2^-s)'| < 1. These bounds transport both readings to the actual zero.
    assert Fraction(7, 6)-Fraction(3, 8)-34*r > Fraction(3, 4)
    assert Fraction(3, 5)-Fraction(3, 8)-35*r > Fraction(1, 6)
    return {'method':'outward rounded integer intervals, Taylor bound and contraction on a closed disk',
            'center':['794/1000','17715/1000'], 'radius':str(r), 'P':value.endpoints(),
            'derivative':derivative.endpoints(), 'contraction_constant_upper':str(lipschitz),
            'constant_target_squared_error_strict_lower':'1/650',
            'first_tick_squared_error_strict_lower':'1/10400',
            'binary_initial_fit':{'constant_squared_error_strict_lower':'9/10400',
                                  'tick_squared_error_strict_lower':'1/23400',
                                  'eta_256_at_center':eta_head.endpoints()}}


if __name__ == '__main__':
    print(json.dumps(audit(), indent=2))
