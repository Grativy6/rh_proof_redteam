"""Persistent cell supply for an ordered list of exact integer prefix imbalances."""


def minimum_draw(values, capacity):
    """Ordinary stock starts empty and can cross a cut only up to capacity."""
    if not values or values[0] != 0 or capacity < 0:
        raise ValueError("the ledger must start at zero and the capacity must be nonnegative")
    stock = spent = 0
    for a, b in zip(values, values[1:]):
        balance = stock - (b - a)
        if balance < 0:
            spent -= balance
            stock = 0
        else:
            stock = min(capacity, balance)
    return spent


def cut_depth(values):
    """Return the greatest forced carry and its two bracketing peaks."""
    pivot = values.index(max(values))
    best = (0, 0, 0, pivot)
    left = 0
    for cut in range(pivot + 1):
        if values[cut] > values[left]:
            left = cut
        candidate = (values[left] - values[cut], left, cut, pivot)
        if candidate[0] > best[0]:
            best = candidate
    right = len(values) - 1
    for cut in range(right, pivot - 1, -1):
        if values[cut] > values[right]:
            right = cut
        candidate = (values[right] - values[cut], pivot, cut, right)
        if candidate[0] > best[0]:
            best = candidate
    return best


def finite_depths(values):
    """Remove nested reversals and keep their depths, independently of any supply cap."""
    if not values or values[0] != 0:
        raise ValueError("the ledger must start at zero")
    bottom = min(values) - 1
    turns = [bottom]
    for y in values:
        if turns[-1] == y:
            continue
        if len(turns) >= 2 and ((turns[-2] < turns[-1]) == (turns[-1] < y)):
            turns[-1] = y
        else:
            turns.append(y)
    if len(turns) > 1 and turns[-1] < turns[-2]:
        turns[-1] = bottom
    else:
        turns.append(bottom)
    stack = []
    depths = []
    for y in turns:
        stack.append(y)
        while len(stack) >= 4:
            a, b, c, d = stack[-4:]
            inner = abs(c - b)
            if inner > abs(a - b) or inner > abs(c - d):
                break
            depths.append(inner)
            stack[-3:] = [d]
    assert stack == [bottom, max(values), bottom]
    return sorted(depths, reverse=True)


def least_capacity(maximum, depths, budget):
    """Each of the leading k depths gives a necessary bound which is sufficient jointly."""
    if budget < maximum:
        raise ValueError("budget below the unlimited-storage minimum")
    total = maximum
    cap = 0
    for k, d in enumerate(depths, 1):
        total += d
        required = -((budget - total) // k)
        cap = max(cap, required)
    return cap


def read_path(values, locations, budget):
    if len(values) != len(locations):
        raise ValueError("a physical cut is required for every reading")
    peak = max(values)
    depths = finite_depths(values)
    deepest, a, cut, b = cut_depth(values)
    assert deepest == (depths[0] if depths else 0)
    threshold = least_capacity(peak, depths, budget)
    probes = sorted({0, threshold, max(0, threshold - 1), deepest, deepest // 2})
    rows = []
    for cap in probes:
        value = peak + sum(max(0, d - cap) for d in depths)
        assert value == minimum_draw(values, cap)
        rows.append([cap, value])
    assert minimum_draw(values, threshold) <= budget
    assert not threshold or minimum_draw(values, threshold - 1) > budget
    return {
        "unlimited_minimum_pocket": peak,
        "prescribed_pocket": budget,
        "least_persistent_capacity_for_prescribed_pocket": threshold,
        "least_capacity_for_unlimited_minimum": deepest,
        "forced_crossing": {
            "left_peak": [locations[a], values[a]],
            "cut": [locations[cut], values[cut]],
            "right_peak": [locations[b], values[b]],
        },
        "finite_depth_count": len(depths),
        "five_deepest": depths[:5],
        "capacity_and_minimum_pocket": rows,
    }
