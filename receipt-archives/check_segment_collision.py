"""Exact integer checks for the fixed-degree Frobenius segment collision."""

from math import prod

P = 17
GAP = 100
PERIOD = 4 * GAP
DEGREE = 2 * P**(12 * GAP)
K = 10**9             # Total number of coordinates, called k in the receipt.
Y = 64 * K
NS = 6
FRAME_RANK = 2


def floor_log(value, base):
    result = 0
    while value >= base:
        value //= base
        result += 1
    return result


def main():
    positions = [i * GAP for i in range(-4, 2)]
    weights = [P**(GAP - x) for x in positions]
    tops = (0, GAP, 2 * GAP, 3 * GAP)
    q = P**PERIOD
    twist_bound = P**(5 * GAP)
    assert weights[:2] == [q * weights[4], q * weights[5]]
    assert NS <= 2 * len(tops) and NS + FRAME_RANK <= K - FRAME_RANK
    # log(2) < 1 and log(17) < 3 give an integer upper bound.
    assert 1088 * NS**2 * (1 + 3 * 12 * GAP) <= K
    assert 128 * K**2 * NS * Y**2 <= P**(GAP - 2)
    assert 32 * P * Y * K**2 * NS * twist_bound**2 <= DEGREE
    assert 4 * len(tops) * FRAME_RANK**2 * K == Y  # the rank prefactor is 3/4

    occurrence_degree = [0] * len(positions)
    for i in range(2, 6):
        exponent, remainder = divmod(DEGREE, 2 * weights[i - 2])
        assert remainder == 0
        assert exponent >= DEGREE // (weights[i - 2] * K**2 * Y)
        occurrence_degree[i-2] += exponent
        occurrence_degree[i-1] += exponent
        assert positions[i-2] % PERIOD != positions[i-1] % PERIOD
    base_degree = {t: 0 for t in tops}
    for x, weight, count in zip(positions, weights, occurrence_degree):
        base_degree[x % PERIOD] += weight * count
    assert set(base_degree.values()) == {P**(12 * GAP) + P**(11 * GAP)}

    multiplicity = P**(6 * GAP)
    padding = {}
    for i in range(2, 6):
        t = positions[i] % PERIOD
        added = 2 * multiplicity * weights[0] if t == 0 else 0
        units, rem = divmod(DEGREE - base_degree[t] - added, weights[i])
        assert rem == 0 and units >= 0
        padding[t] = units
    # All indices have the same two input degrees. Test both endpoints and an
    # interior index. The algebraic expression in the receipt proves all indices.
    for i in (0, 1, multiplicity // 2, multiplicity):
        old = (i, multiplicity - i)
        new = (q * (multiplicity - i), q * i)
        image = tuple(weights[0] * h + weights[4] * l for h, l in zip(old, new))
        assert image == (weights[0] * multiplicity,) * 2
        assert sum(old) == multiplicity and sum(new) == q * multiplicity
        assert base_degree[0] + sum(image) + padding[0] * weights[4] == DEGREE

    # Exercise the general carry formula on an uneven two-frame period, where
    # the coarse powers differ from the gaps between the frame ends.
    first = [-14, 0, 10, 24, 34]
    last = [-12, 4, 12, 28, 36]
    base = 7
    for level in (1, base**8, base**30, base**30 + 3):
        log_level = floor_log(level, base)
        z = [last[j] for j in range(1, 5)]
        previous = first[:4]
        scales = [floor_log(level // base**(v - y), base) for v, y in zip(z, previous)]
        combined = [v + scale for v, scale in zip(z, scales)]
        assert combined == [max(v, log_level + y) for v, y in zip(z, previous)]
        ratios = [base**(b-a) for a, b in zip(combined, combined[1:])]
        assert prod(ratios[:2]) == base**24
        for ratio in ratios:
            for low, high in ((0, 3), (ratio-1, 2)):
                quotient, remainder = divmod(low + ratio * high, ratio)
                assert (quotient, remainder) == (high, low)
    print('All numerical hypotheses checked. At least 17^600 + 1 descriptions have one nonzero image.')
    print('Radices and the strict-digit decoding verified on the two-frame control.')


if __name__ == '__main__':
    main()
