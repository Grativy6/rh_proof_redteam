"""Pay two successive late-frame corrections on the actual transported first-tick fit."""
from fractions import Fraction
from check_pal_first_tick import fit_rows
from check_pal_residue_distance import HUNDREDTHS


def signed_gain_bounds(cutoff=2_000_000):
    scale = 1 << 64
    head = [0, 0]
    upper = [0, 0]
    square_head = 0
    for k, _, fit, denominator in fit_rows(cutoff):
        den = 4 * denominator
        residual = 4 * ((denominator if k == 1 else 0) - fit)
        term_den = den * den * k * (k + 1)
        square_head += (scale * residual**2 + term_den - 1) // term_den
        for i, (p, q, direction) in enumerate(((101, 103, 1), (107, 109, -1))):
            digit = (k // p) % 2 - (k // q) % 2
            correction = direction * denominator * digit
            if digit:
                num = scale * (2 * residual * correction - correction**2)
                head[i] += num // term_den
                upper[i] += -((-num) // term_den)
            residual -= correction  # second update sees the actual first update
    bound = Fraction(sum(map(abs, HUNDREDTHS)), 100)
    initial = Fraction(square_head, scale) + bound**2 / (cutoff+1)
    gains = []
    for i in range(2):
        parent_bound = bound + Fraction(i, 4)
        tail = (parent_bound / 2 + Fraction(1, 16)) / (cutoff + 1)
        gains.append((Fraction(head[i], scale)-tail, Fraction(upper[i], scale)+tail))
    return initial, gains


def two_band_receiver(cutoff=4_000_000):
    """Test the same two contrasts on the constant fit after one extra dyadic copy."""
    scale = 1 << 64
    # In units of 1/80, these multipliers include the half in the two-bit readings.
    trials = (("carried", (20, -20), (Fraction(1, 2), Fraction(1, 2))),
              ("refit", (8, -5), (Fraction(1, 5), Fraction(1, 8))))
    lowers = [[0, 0] for _ in trials]
    uppers = [[0, 0] for _ in trials]
    for k, original, _, denominator in fit_rows(cutoff):
        den = 80 * denominator
        term_den = den**2 * k * (k+1)
        digits = tuple((((k//p) % 4).bit_count() - ((k//q) % 4).bit_count())
                       for p, q in ((101, 103), (107, 109)))
        for j, (_, multipliers, _) in enumerate(trials):
            residual = 80 * (denominator-original)
            for i, digit in enumerate(digits):
                correction = multipliers[i] * denominator * digit
                if digit:
                    num = scale * (2*residual*correction-correction**2)
                    lowers[j][i] += num // term_den
                    uppers[j][i] += -((-num) // term_den)
                residual -= correction
    result = {}
    for j, (label, _, caps) in enumerate(trials):
        bound = 1 + Fraction(sum(map(abs, HUNDREDTHS)), 100)
        result[label] = []
        for i, cap in enumerate(caps):
            tail = (2*bound*cap + cap**2)/(cutoff+1)
            result[label].append((Fraction(lowers[j][i], scale)-tail,
                                  Fraction(uppers[j][i], scale)+tail))
            bound += cap
    assert all(hi < 0 for _, hi in result["carried"])
    assert all(lo > 0 for lo, _ in result["refit"])
    assert sum(lo for lo, _ in result["refit"]) > Fraction(1, 100000)
    return result


if __name__ == "__main__":
    initial, gains = signed_gain_bounds()
    assert gains[0][0] > Fraction(1, 10000)
    assert gains[1][0] > Fraction(1, 90000)
    assert initial < Fraction(1, 40)
    print("Initial whole-row squared error at most", initial)
    for j, (lo, hi) in enumerate(gains, 1):
        print("Signed improvement", j, "between", lo, "and", hi)
    print("Final whole-row squared error at most", initial - sum(lo for lo, _ in gains))
    for label, intervals in two_band_receiver().items():
        for step, (lo, hi) in enumerate(intervals, 1):
            print("Constant target", label, "gain", step, "between", lo, "and", hi)
