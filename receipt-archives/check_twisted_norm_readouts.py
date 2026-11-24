"""Prime certificates and power-residue readouts for the actual order-two tower class.

Run from this directory with Python 3.10+. The number-field identifications and the
class-counting kernel bound are proved in the companion receipts.
"""
from math import factorial

from check_dyadic_window_class import check_window

# (v2(p-1), odd coefficient, Proth witness, square root of -d mod p)
PRIMES = (
    (9, 45, 11, 310),
    (12, 3, 11, 5429),
    (24, 291, 5, 2008617389),
    (48, 15, 11, 1917310808066937),
    (88, 1323, 11, 27783367807805898870018075337),
    (89, 231, 5, 43251830339452905452357883290),
    (96, 1113, 11, 18373890285694839053780575544186),
    (128, 2517, 5, 56263880631777420359185250093930723163221),
)


def v2(n):
    if n == 0:
        raise ValueError("use a nonzero integer")
    return (n & -n).bit_length() - 1


def check_prime(h, k, witness, root, d):
    p = 1 + k * 2**h
    assert k % 2 == 1 and k < 2**h
    # Any prime divisor has an element of order divisible by 2^h and exceeds sqrt(p).
    assert pow(witness, (p-1)//2, p) == p-1
    assert (2**h+1)**2 > p
    assert p % 4 == 1 and pow(-3, (p-1)//2, p) == 1
    assert (root*root+d) % p == 0 and 0 < root < p
    assert pow(2+root, (p-1)//2, p) == pow(2-root, (p-1)//2, p) == p-1
    return p


def norm_exponent_mod(p, c, twist, layer):
    # For alpha^((a-1)/2) fixed by the layer group, the twisted norm is
    # alpha^((a^H-1)/2). Reduce mod 2*(p-1) before the exact division by two.
    a = (1 + 2**c)**twist
    H = 2**(layer-c)
    return ((pow(a, H, 2*(p-1))-1) % (2*(p-1))) // 2


def coefficient(c, twist):
    base = 1 + 2**c
    value = 1
    for j in range(2*twist+1):
        if j != twist:
            value *= base**twist - base**j
    assert v2(value) == 2*twist*c + 2*v2(factorial(twist))
    return value


def readout(p, root, h, c, twist, layer):
    assert c <= min(h, layer)
    f = 2**max(0, layer-h)
    Q = p**f
    assert (Q-1) % 2**layer == 0
    exponent = norm_exponent_mod(p, c, twist, layer)
    norm = pow(2+root, exponent, p)
    index = pow(norm, (Q-1)//2**layer, p)
    expected = p-1 if twist % 2 and layer <= h else 1
    assert index == expected
    pe = coefficient(c, twist)
    assert pow(index, pe, p) == 1
    # The power in the conclusion Few also annihilates the class.
    b = 2*twist + (2*twist+1)*(c+2*twist+1)
    assert pow(index, 2**b, p) == 1
    return f, -1 if index == p-1 else 1


def run():
    check_window()
    u = 1 + 4 * 3**205
    d = 3*u*u - 4
    for h, k, witness, root in PRIMES:
        p = check_prime(h, k, witness, root, d)
        for layer in (h-1, h, h+1, h+2):
            result = readout(p, root, h, 2, 1, layer)
            # Exercise nontrivial odd and even twists satisfying 2*twist+1 < 2^c.
            for twist in (1, 2, 3):
                readout(p, root, h, 3, twist, layer)
            if h in (88, 89) and layer in (88, 89):
                print(f"p={p}, layer={layer}, residue degree={result[0]}, raw={result[1]}, weighted=1")
    assert coefficient(2, 1) == -80
    print("Eight primes certified. Raw twisted norms, the -80 factor and higher layers agree.")


if __name__ == "__main__":
    run()
