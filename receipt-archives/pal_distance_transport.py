"""Optimal bounded changes of distance for the outer trips of a TickCube."""

from bisect import bisect_left, bisect_right


class FreeDistanceOffsets:
    """Free-cell ranks before a distance, including the diagonal at distance zero."""

    def __init__(self, n, layers, reserved):
        self.n = n
        self.layers = layers
        self.occupied_distances = sorted(reserved)
        self.occupied_prefix = [0]
        for d in self.occupied_distances:
            _, starts, levels = reserved[d]
            self.occupied_prefix.append(self.occupied_prefix[-1] + 2 * starts * levels)

    def __len__(self):
        return self.n + 1

    def __getitem__(self, distance):
        if isinstance(distance, slice):
            return [self[d] for d in range(*distance.indices(len(self)))]
        if distance < 0:
            distance += len(self)
        if not 0 <= distance <= self.n:
            raise IndexError("distance outside physical box")
        if distance == 0:
            return 0
        tail = self.n - distance
        full = self.layers * (self.n * self.n - tail * (tail + 1))
        used = self.occupied_prefix[bisect_left(self.occupied_distances, distance)]
        return full - used


def bounded_intervals(n, distances, source_offsets, free_offsets, radius, keep_starts=False):
    """Earliest admissible free intervals, or a whole interval witnessing impossibility."""
    if radius < 0:
        raise ValueError("negative transport radius")
    starts = [] if keep_starts else None
    end = 0
    first = 0
    free_left = 0
    for index, p in enumerate(distances):
        a = max(0, p - radius)
        b = min(n, p + radius + 1)
        left = free_offsets[a]
        if left >= end:
            end = left
            first = index
            free_left = left
        if keep_starts:
            starts.append(end)
        end += source_offsets[index + 1] - source_offsets[index]
        right = free_offsets[b]
        if end > right:
            demand = source_offsets[index + 1] - source_offsets[first]
            room = right - free_left
            assert demand > room
            return False, {
                "first_prime": distances[first],
                "last_prime": p,
                "first_destination": max(0, distances[first] - radius),
                "last_destination": b - 1,
                "source_records": demand,
                "available_cells": room,
                "shortage": demand - room,
            }
    return True, starts


def install_minimum_radius(cube):
    """Assign every remaining record, keep all reserved cells, and prove the minimum radius."""
    under = -1
    enough = cube.n - 1
    while enough - under > 1:
        candidate = (under + enough) // 2
        possible, _ = bounded_intervals(
            cube.n, cube.outer, cube.source_offsets, cube.free_offsets, candidate
        )
        if possible:
            enough = candidate
        else:
            under = candidate
    possible, starts = bounded_intervals(
        cube.n, cube.outer, cube.source_offsets, cube.free_offsets, enough, True
    )
    if not possible:
        raise ValueError("no assignment even at full width")
    obstruction = None
    if enough:
        possible, obstruction = bounded_intervals(
            cube.n, cube.outer, cube.source_offsets, cube.free_offsets, enough - 1
        )
        assert not possible
    cube.install_outer_starts(starts)
    return enough, obstruction


def install_high_to_low(cube):
    """Fill the free cells from their far end, leaving unused room near distance zero."""
    spare = cube.free_offsets[-1] - cube.outer_records
    starts = [spare + v for v in cube.source_offsets[:-1]]
    cube.install_outer_starts(starts)
    maximum = 0
    for p, start, end in zip(cube.outer, starts, [spare + v for v in cube.source_offsets[1:]]):
        low = bisect_right(cube.free_offsets, start) - 1
        high = bisect_right(cube.free_offsets, end - 1) - 1
        maximum = max(maximum, p - low, high - p)
    return maximum
