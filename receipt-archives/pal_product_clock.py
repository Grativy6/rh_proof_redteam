"""Certified tick counts for a product carried through successive prime arrivals."""

from math import ceil, floor
from bisect import bisect_left, bisect_right

from check_pal_returned_horizon import log_ratio_interval


class LogGrid:
    """Outward integer enclosures. Only the short base table uses rational series."""

    def __init__(self, root, digits=36):
        self.scale = 10**digits
        self.digits = digits
        self.terms = 2 * ((digits + 5) // 6) + 1
        self.base = {}
        a, b = log_ratio_interval(root + 1, root, 2 * digits + 5)
        self.step = (floor(self.scale * a), ceil(self.scale * b))
        if self.step[0] <= 0:
            raise ValueError("precision below the positive clock step")

    def logarithm_table(self, b):
        if b not in self.base:
            low, high = log_ratio_interval(b, 1024, 2 * self.digits + 5)
            self.base[b] = floor(self.scale * low), ceil(self.scale * high)
        return self.base[b]

    def logarithm(self, p):
        e = p.bit_length() - 1
        unit = 1 << e
        b = 1024 * p // unit
        num = 1024 * p - b * unit
        den = b * unit
        S = self.scale
        r0, r1 = S * num // den, -(-S * num // den)
        a0, a1 = r0, r1
        lo, hi = r0, r1
        for k in range(2, self.terms + 1):
            a0, a1 = a0 * r0 // S, -(-a1 * r1 // S)
            low, high = a0 // k, -(-a1 // k)
            if k % 2:
                lo, hi = lo + low, hi + high
            else:
                lo, hi = lo - high, hi - low
        lo -= -(-S // ((self.terms + 1) * 1024 ** (self.terms + 1)))
        bl, bu = self.logarithm_table(b)
        el, eu = self.logarithm_table(2048)
        return lo + bl + e * el, hi + bu + e * eu

    def tick_interval(self, lo, hi):
        step_low, step_high = self.step
        return -(-lo // step_high), -(-hi // step_low)


class ProductClock:
    """Retain the product clock, every individual tick that it leaves aside, and a return label."""

    def __init__(self, x):
        if x < 2:
            raise ValueError("the covered prime clock uses x >= 2")
        self.x = x
        self.grid = LogGrid(x, max(36, 2 * len(str(x)) + 12))
        self.primes = []
        self.lower = self.upper = self.previous = 0
        self.refinements = 0

    def push(self, p):
        if p < 2 or (self.primes and p <= self.primes[-1]):
            raise ValueError("increasing prime labels of at least two required")
        self.primes.append(p)
        low, high = self.grid.logarithm(p)
        self.lower += low
        self.upper += high
        while True:
            individual = self.grid.tick_interval(low, high)
            cumulative = self.grid.tick_interval(self.lower, self.upper)
            if individual[0] == individual[1] and cumulative[0] == cumulative[1]:
                break
            # A positive power of (x+1)/x cannot be an integer for x >= 2.
            # Re-enclosing prior factors is necessary for a close cumulative crossing.
            self.grid = LogGrid(self.x, 2 * self.grid.digits)
            self.refinements += 1
            self.lower = self.upper = 0
            for q in self.primes:
                low, high = self.grid.logarithm(q)
                self.lower += low
                self.upper += high
        total = cumulative[0]
        ticks = individual[0]
        shared = total - self.previous
        self.previous = total
        assert shared in (ticks - 1, ticks)
        return ticks, shared, total


class ProductRows:
    """Literal row slots for original ticks, with separate addresses for the individual rounding flags."""

    def __init__(self, n, x, last, bank, primes, individual, pooled_ends):
        self.n = n
        self.x = x
        self.last = last
        self.bank = bank
        self.primes = primes
        self.individual = individual
        self.ends = [0] + pooled_ends

    def encode(self, p, row, t):
        i = bisect_left(self.primes, p)
        if (
            i == len(self.primes)
            or self.primes[i] != p
            or not 0 <= row < self.n - p
            or not 0 <= t < self.individual[i]
        ):
            raise ValueError("unknown arrival")
        reduced = self.ends[i + 1] - self.ends[i]
        if t == reduced:
            return ("pocket", row, p - 1)
        ordinal = self.ends[i] + t
        if ordinal < self.bank * self.x:
            return ("pocket", row, self.last + ordinal)
        column, lane = divmod(ordinal - self.bank * self.x, self.x)
        d = self.x + 1 + column
        if d > p:
            raise ValueError("the proposed budget has not yet released this cell")
        return ("ordinary", row, row + d, lane)

    def decode(self, place):
        side, row, *fields = place
        if not 0 <= row < self.n:
            raise ValueError("invalid starting row")
        if side == "pocket" and len(fields) == 1:
            slot = fields[0]
            if not 0 <= slot < self.last + self.bank * self.x:
                raise ValueError("outside this row's pocket")
            if slot < self.last:
                p = slot + 1
                i = bisect_left(self.primes, p)
                if (
                    i == len(self.primes)
                    or self.primes[i] != p
                    or self.individual[i] != self.ends[i + 1] - self.ends[i] + 1
                    or row >= self.n - p
                ):
                    raise ValueError("unused flag address")
                return p, row, self.individual[i] - 1
            ordinal = slot - self.last
        elif side == "ordinary" and len(fields) == 2:
            end, lane = fields
            d = end - row
            if not self.x < d or end >= self.n or not 0 <= lane < self.x:
                raise ValueError("invalid released cell")
            ordinal = self.bank * self.x + (d - self.x - 1) * self.x + lane
        else:
            raise ValueError("unknown slot kind")
        i = bisect_right(self.ends, ordinal) - 1
        if (
            i >= len(self.primes)
            or row >= self.n - self.primes[i]
            or (side == "ordinary" and d > self.primes[i])
        ):
            raise ValueError("unused pooled address")
        return self.primes[i], row, ordinal - self.ends[i]
