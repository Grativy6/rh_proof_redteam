"""Transport the existing all-row witness to the first tick. Integer rounding is upward."""
from fractions import Fraction
from check_pal_residue_distance import HUNDREDTHS, squarefree


def fit_rows(cutoff):
    """Yield physical row, original numerator, transported numerator and denominator."""
    if cutoff < 1:
        raise ValueError("The tail must start beyond row one")
    pairs = list(zip((d for d in range(2, 102) if squarefree(d)), HUNDREDTHS, strict=True))
    slope = sum(Fraction(c, 100*d) for d, c in pairs)
    denominator = 100 * slope.denominator
    step = 100 * slope.numerator
    jumps = [0] * (cutoff + 1)
    for d, c in pairs:
        for k in range(d, cutoff + 1, d):
            jumps[k] += c
    fit = 0
    original = 0
    for k in range(1, cutoff + 1):
        change = step - slope.denominator * jumps[k]
        original += change
        fit += change
        if k % 2 == 0:
            fit -= step - slope.denominator * jumps[k//2]
        if k <= 202:
            direct = sum(Fraction(c * ((k % d) - ((k//2) % d)), 100*d) for d, c in pairs)
            assert Fraction(fit, denominator) == direct
            assert Fraction(original, denominator) == sum(Fraction(c * (k % d), 100*d) for d, c in pairs)
        yield k, original, fit, denominator


def run(cutoff=200_000):
    scale = 1 << 64
    head = 0
    for k, _, fit, denominator in fit_rows(cutoff):
        residual = (denominator if k == 1 else 0) - fit
        den = denominator * denominator * k * (k+1)
        head += (scale * residual * residual + den-1)//den
    envelope = Fraction(sum(map(abs, HUNDREDTHS)), 100)
    tail = envelope**2/(cutoff+1)
    head = Fraction(head, scale)
    assert head + tail < Fraction(1, 40)
    print("Cutoff", cutoff)
    print("Head upper bound", head)
    print("Tail upper bound", tail)
    print("Full first-tick squared error below 1/40", head + tail < Fraction(1, 40))


if __name__ == "__main__":
    run()
