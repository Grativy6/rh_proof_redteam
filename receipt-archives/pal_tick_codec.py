"""Reversible placement of single (prime trip, tick) records in an n by n by h box."""

from bisect import bisect_right
from math import isqrt

from pal_distance_transport import FreeDistanceOffsets


def ceil_div(a, b):
    return -(-a // b)


def pack_trip(n, layers, p, i, t):
    half = (n + 1) // 2
    block, layer = divmod(t, layers)
    side, start = divmod(i, half)
    return start, (2 * block + side + 1) * p, layer


def unpack_trip(n, layers, stored, primes):
    start, distance, layer = stored
    owners = [p for p in primes if p > isqrt(n) and distance % p == 0]
    if len(owners) != 1:
        raise ValueError("distance needs exactly one large prime owner")
    p = owners[0]
    block, side = divmod(distance // p - 1, 2)
    return p, side * ((n + 1) // 2) + start, block * layers + layer


class TickCube:
    """Reserve the disjoint middle-prime rectangles, then rank the remaining jobs into free cells."""

    def __init__(self, n, layers, prices, keep_prime_addresses=True):
        if n < 1 or layers < 1:
            raise ValueError("positive board dimensions required")
        self.n = n
        self.layers = layers
        self.prices = dict(prices)
        self.half = (n + 1) // 2
        root = isqrt(n)
        blocks = ceil_div(root * n.bit_length(), layers)
        self.owners = {
            p for p in self.prices if keep_prime_addresses and p > root and 4 * blocks * p <= n
        }
        self.reserved = {}
        middle_size = 0
        for p in sorted(self.owners):
            height = self.prices[p]
            for block in range(ceil_div(height, layers)):
                occupied_layers = min(layers, height - block * layers)
                for side in (0, 1):
                    starts = min(self.half, max(0, n - p - side * self.half))
                    if starts == 0:
                        continue
                    distance = (2 * block + side + 1) * p
                    if distance in self.reserved or distance > n // 2 or starts - 1 + distance >= n:
                        raise ValueError("invalid middle-prime geometry or tick prices")
                    self.reserved[distance] = (p, starts, occupied_layers)
                    middle_size += 2 * starts * occupied_layers
        self.outer = sorted(p for p in self.prices if p not in self.owners and p < n)
        self.source_offsets = [0]
        self.source_index = {}
        for index, p in enumerate(self.outer):
            self.source_index[p] = index
            self.source_offsets.append(self.source_offsets[-1] + 2 * (n - p) * self.prices[p])
        self.free_offsets = FreeDistanceOffsets(n, layers, self.reserved)
        self.outer_starts = self.source_offsets[:-1]
        self.middle_records = middle_size
        self.outer_records = self.source_offsets[-1]
        self.count = middle_size + self.outer_records
        assert self.count == sum(2 * (n - p) * h for p, h in self.prices.items())
        assert self.free_offsets[-1] + middle_size == n * n * layers
        if self.outer_records > self.free_offsets[-1]:
            raise ValueError("outer records exceed the remaining free cells")

    def install_outer_starts(self, starts):
        """Each ordered group occupies its full consecutive interval of free cells."""
        if len(starts) != len(self.outer):
            raise ValueError("wrong number of source groups")
        previous = 0
        for i, start in enumerate(starts):
            size = self.source_offsets[i + 1] - self.source_offsets[i]
            if start < previous or start + size > self.free_offsets[-1]:
                raise ValueError("overlap or insufficient room")
            previous = start + size
        self.outer_starts = list(starts)

    @staticmethod
    def oriented(start, distance, layer, direction):
        if direction == 0:
            return start, start + distance, layer
        return start + distance, start, layer

    def encode(self, p, i, t, direction):
        if (
            p not in self.prices
            or direction not in (0, 1)
            or not 0 <= i < self.n - p
            or not 0 <= t < self.prices[p]
        ):
            raise ValueError("invalid trip record")
        if p in self.owners:
            place = pack_trip(self.n, self.layers, p, i, t)
            return self.oriented(*place, direction)
        rank = (
            self.outer_starts[self.source_index[p]]
            + (direction * (self.n - p) + i) * self.prices[p]
            + t
        )
        d = bisect_right(self.free_offsets, rank) - 1
        _, starts, occupied = self.reserved.get(d, (0, 0, 0))
        run = (self.n - d) * self.layers - starts * occupied
        ori, local = divmod(rank - self.free_offsets[d], run)
        fringe = starts * (self.layers - occupied)
        if local < fringe:
            start, layer = divmod(local, self.layers - occupied)
            layer += occupied
        else:
            start, layer = divmod(local - fringe, self.layers)
            start += starts
        return self.oriented(start, d, layer, ori)

    def decode(self, u, v, layer):
        if not 0 <= u < self.n or not 0 <= v < self.n or not 0 <= layer < self.layers:
            raise ValueError("invalid cube cell")
        d = abs(v - u)
        start = min(u, v)
        direction = int(v < u)
        p, starts, occupied = self.reserved.get(d, (0, 0, 0))
        if start < starts and layer < occupied:
            block, side = divmod(d // p - 1, 2)
            return p, side * self.half + start, block * self.layers + layer, direction
        if start < starts:
            offset = start * (self.layers - occupied) + layer - occupied
        else:
            offset = starts * (self.layers - occupied) + (start - starts) * self.layers + layer
        per_direction = (self.n - d) * self.layers - starts * occupied
        rank = self.free_offsets[d] + direction * per_direction + offset
        index = bisect_right(self.outer_starts, rank) - 1
        if (
            index < 0
            or rank - self.outer_starts[index]
            >= self.source_offsets[index + 1] - self.source_offsets[index]
        ):
            raise ValueError("unused cube cell")
        p = self.outer[index]
        side, t = divmod(rank - self.outer_starts[index], self.prices[p])
        ori, i = divmod(side, self.n - p)
        return p, i, t, ori
