"""Full-row enclosures for Pang's fresh-prime refits, using only rational arithmetic."""
from fractions import Fraction as Q
from math import lcm

UNITS = 10**16
BASE = (2, 3, 6)


def dot(left, right):
    return sum(x * y for x, y in zip(left, right, strict=True))


def inverse(matrix):
    n = len(matrix)
    rows = [row[:] + [Q(i == j) for j in range(n)] for i, row in enumerate(matrix)]
    for i in range(n):
        pivot = rows[i][i]
        if not pivot:
            raise ArithmeticError("Zero principal pivot in the midpoint Gram matrix")
        rows[i] = [x / pivot for x in rows[i]]
        for j in range(n):
            if i != j:
                factor = rows[j][i]
                rows[j] = [x - factor * y for x, y in zip(rows[j], rows[i], strict=True)]
    result = [row[n:] for row in rows]
    for i, row in enumerate(result):
        for j, column in enumerate(zip(*matrix)):
            assert dot(row, column) == int(i == j)
    return result


def around(mid, error):
    return mid - error, mid + error


def enclose_fit(moduli):
    period = lcm(*moduli)
    cutoff = max(12600 // period, 240) * period
    # After the cutoff each residue tail lies within w(cutoff+1) of the
    # average tail. Comparing the earliest and latest visit per period telescopes.
    masses = []
    for r in range(1, period + 1):
        head = sum(UNITS // (k * (k + 1)) for k in range(r, cutoff + 1, period))
        masses.append(Q(head, UNITS) + Q(1, period * (cutoff + 1)))
    entry_error = Q(period, (cutoff + 1) * (cutoff + 2)) + Q(cutoff, UNITS)
    columns = [[Q(r % d, d) for r in range(1, period + 1)] for d in moduli]
    weighted_columns = [[m * x for m, x in zip(masses, c, strict=True)] for c in columns]
    gram = [[dot(c, d) for d in columns] for c in weighted_columns]
    rhs = [sum(c) for c in weighted_columns]
    inv = inverse(gram)
    size = max(sum(map(abs, row)) for row in inv)
    defect = size * len(moduli) * entry_error
    assert defect < 1
    weights = [dot(row, rhs) for row in inv]
    error = size * entry_error * (1 + sum(map(abs, weights))) / (1 - defect)
    loss = 1 - dot(rhs, weights)
    loss_error = entry_error * sum(map(abs, weights)) + error * sum(abs(x) + entry_error for x in rhs)
    means = [Q(d - 1, 2 * d) for d in moduli]
    direction = [dot(row, means) for row in inv]
    direction_error = size * entry_error * sum(map(abs, direction)) / (1 - defect)
    six = moduli.index(6)
    return {
        "period": period, "cutoff": cutoff, "six": around(weights[six], error),
        "loss": around(loss, loss_error),
        "mean residual": around(1 - dot(means, weights), sum(means) * error),
        "mean direction at six": around(direction[six], direction_error),
    }


def display(bounds):
    # Round outwards, including when either bound is negative.
    scale = 100000
    lo, hi = bounds
    left = (lo * scale).__floor__()
    right = (hi * scale).__ceil__()
    def fixed(value):
        sign = "-" if value < 0 else ""
        integer, fraction = divmod(abs(value), scale)
        return f"{sign}{integer}.{fraction:05d}"
    return "[" + fixed(left) + ", " + fixed(right) + "]"


def run():
    results = {}
    for label, primes in (("base", ()), ("five", (5,)), ("seven", (7,)),
                          ("eleven", (11,)), ("five and seven", (5, 7))):
        moduli = BASE + tuple(p * a for p in primes for a in (1, 2, 3, 6))
        row = enclose_fit(moduli)
        results[label] = row
        print(label, "L", row["period"], "cutoff", row["cutoff"],
              "weight at 6", display(row["six"]), "all-row squared error", display(row["loss"]))
    assert results["base"]["six"][0] > Q(59, 100)
    assert results["five"]["six"][1] < 0 and results["seven"]["six"][1] < 0
    assert results["eleven"]["six"][0] > 0
    for key in ("mean residual", "mean direction at six"):
        assert results["base"][key][0] > 0
        print("base", key, display(results["base"][key]))
    base, five, seven, together = (results[s]["loss"] for s in ("base", "five", "seven", "five and seven"))
    excess = (base[0] - five[1] - seven[1] + together[0],
              base[1] - five[0] - seven[0] + together[1])
    assert excess[0] > 0
    print("isolated gains minus actual joint gain", display(excess))


if __name__ == "__main__":
    run()
