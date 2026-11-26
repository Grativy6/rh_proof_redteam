"""Share whole columns across retained prime arrivals with one Euclidean remainder."""

from bisect import bisect_left, bisect_right


class TickColumns:
    def __init__(self, n, height, distances, ticks):
        if n < 1 or height < 1 or len(distances) != len(ticks):
            raise ValueError("positive board dimensions and one tick count per distance required")
        if any(a >= b for a, b in zip(distances, distances[1:])) or any(
            p <= 0 or p >= n for p in distances
        ):
            raise ValueError("source distances must be strictly increasing inside the row")
        if any(t < 0 for t in ticks):
            raise ValueError("negative tick count")
        self.n, self.height = n, height
        self.distances = list(distances)
        self.ticks = list(ticks)
        self.ends = [0]
        self.column_ends = [0]
        for count in self.ticks:
            total = self.ends[-1] + count
            self.ends.append(total)
            self.column_ends.append(-(-total // height))

    def encode(self, distance, row, tick):
        i = bisect_left(self.distances, distance)
        if (
            i == len(self.distances)
            or self.distances[i] != distance
            or not 0 <= row < self.n - distance
            or not 0 <= tick < self.ticks[i]
        ):
            raise ValueError("unknown source record")
        column, lane = divmod(self.ends[i] + tick, self.height)
        owner = bisect_right(self.column_ends, column) - 1
        return self.distances[owner], row, column - self.column_ends[owner], lane

    def decode(self, owner, row, column, lane):
        k = bisect_left(self.distances, owner)
        if (
            k == len(self.distances)
            or self.distances[k] != owner
            or not 0 <= lane < self.height
            or not 0 <= column < self.column_ends[k + 1] - self.column_ends[k]
            or not 0 <= row < self.n - owner
        ):
            raise ValueError("unknown allocated column")
        ordinal = (self.column_ends[k] + column) * self.height + lane
        i = bisect_right(self.ends, ordinal) - 1
        if i >= len(self.distances) or row >= self.n - self.distances[i]:
            raise ValueError("unused lane")
        return self.distances[i], row, ordinal - self.ends[i]

    def row_remainder(self, row, last):
        if not 0 <= row < self.n or not 0 <= last <= self.n:
            raise ValueError("invalid row or cut")
        count = bisect_right(self.distances, min(last, self.n - 1 - row))
        return self.height * self.column_ends[count] - self.ends[count]


def column_receipt(n, x, last, primes, ticks, exhaustive=False):
    scheme = TickColumns(n, x, primes, ticks)
    raw = private = shared = refunded_primes = 0
    retired = 0
    previous = 0
    old_remainder = 0
    for i, (p, t) in enumerate(zip(primes, ticks)):
        new = scheme.column_ends[i + 1] - scheme.column_ends[i]
        individual = -(-t // x)
        assert new in (individual, max(0, individual - 1))
        raw += (n - p) * t
        private += x * (n - p) * individual
        shared += x * (n - p) * new
        refunded_primes += int(new < individual)
        retired += (p - previous) * old_remainder
        old_remainder = x * scheme.column_ends[i + 1] - scheme.ends[i + 1]
        assert 0 <= old_remainder < x
        assert shared - raw == (n - p) * old_remainder + retired
        previous = p
    retire_to_last = retired + (last - previous) * old_remainder
    assert shared - raw == (n - last) * old_remainder + retire_to_last
    assert 0 <= shared - raw <= n * (x - 1) and shared <= private
    if exhaustive:
        decoded = set()
        for i, p in enumerate(primes):
            for row in range(n - p):
                for t in range(ticks[i]):
                    slot = scheme.encode(p, row, t)
                    assert slot not in decoded and slot[0] <= p
                    assert scheme.decode(*slot) == (p, row, t)
                    decoded.add(slot)
        assert (
            len(decoded) == raw
            and sum(scheme.row_remainder(row, last) for row in range(n)) == shared - raw
        )
    else:
        for p in primes[:: max(1, len(primes) // 32)]:
            i = bisect_left(primes, p)
            for row in (0, n - p - 1):
                for tick in (0, ticks[i] - 1):
                    slot = scheme.encode(p, row, tick)
                    assert slot[0] <= p and scheme.decode(*slot) == (p, row, tick)
    return {
        "actual_records": raw,
        "separate_upper_columns_in_lanes": private,
        "shared_upper_columns_in_lanes": shared,
        "recovered_lanes": private - shared,
        "unoccupied_shared_lanes": shared - raw,
        "still_active_remainder": old_remainder,
        "retired_lane_sum_through_cut": retire_to_last,
        "primes_relinquishing_one_column": refunded_primes,
        "source_primes": len(primes),
    }
