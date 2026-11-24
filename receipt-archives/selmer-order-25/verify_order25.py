"""Verify the order-25 Kummer witness by rational and finite-field arithmetic."""

from fractions import Fraction
from math import gcd, isqrt
from pathlib import Path
import json


class Quotient:
    """Power basis for a monic polynomial over Q."""

    def __init__(self, f):
        self.f = tuple(f)
        self.n = len(f) - 1
        assert f[-1] == 1
        self.one = (1,) + (0,) * (self.n - 1)
        self.zero = (0,) * self.n
        self.x = (0, 1) + (0,) * (self.n - 2)

    def mul(self, a, b):
        c = [0] * (2 * self.n - 1)
        for i, u in enumerate(a):
            for j, v in enumerate(b):
                c[i + j] += u * v
        for k in range(len(c) - 1, self.n - 1, -1):
            for j in range(self.n):
                c[k - self.n + j] -= c[k] * self.f[j]
        return tuple(c[: self.n])

    def evaluate(self, coeff, x):
        v = self.zero
        for a in reversed(coeff):
            v = add(self.mul(v, x), scale(self.one, a))
        return v

    def power(self, x, n):
        return power(x, n, self.mul, self.one)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def scale(a, c):
    return tuple(c * x for x in a)


def power(x, n, mul, one):
    value = one
    while n:
        if n & 1:
            value = mul(value, x)
        x = mul(x, x)
        n //= 2
    return value


def mod_value(x, p):
    x = Fraction(x)
    return x.numerator * pow(x.denominator, -1, p) % p


def eval_mod(coeff, t, p):
    v = 0
    for a in reversed(coeff):
        v = (v * t + mod_value(a, p)) % p
    return v


def poly_gcd(a, b, p):
    def trim(v):
        v = [mod_value(x, p) for x in v]
        while v and not v[-1]:
            v.pop()
        return v

    a, b = trim(a), trim(b)
    while b:
        while len(a) >= len(b):
            c = a[-1] * pow(b[-1], -1, p) % p
            shift = len(a) - len(b)
            for j, coef in enumerate(b):
                a[shift + j] = (a[shift + j] - c * coef) % p
            a = trim(a)
        a, b = b, a
    return [x * pow(a[-1], -1, p) % p for x in a]


def trial_prime(n):
    return n >= 2 and all(n % i for i in range(2, isqrt(n) + 1))


def valuation(x, p):
    x = Fraction(x)
    if not x:
        raise ValueError("valuation of zero")

    def count(n):
        t = 0
        while n % p == 0:
            n //= p
            t += 1
        return t

    return count(abs(x.numerator)) - count(x.denominator)


def quadratic_class_number(D):
    count = 0
    for a in range(1, isqrt(-D // 3) + 1):
        for b in range(-a, a + 1):
            val, rem = divmod(b * b - D, 4 * a)
            if rem or val < a or gcd(gcd(a, b), val) != 1:
                continue
            if b < 0 and (abs(b) == a or val == a):
                continue
            count += 1
    return count


def verify(name):
    data = json.loads(Path(__file__).with_name(name).read_text("ascii"))
    q = data["q"]
    f = data["period_polynomial_ascending"]
    Q = Quotient(f)
    hnorm = data["h_polynomial_ascending"][0]
    assert trial_prime(q) and q % 8 == 3 and 1 - 4 * hnorm == -5 * q
    assert (
        quadratic_class_number(-5 * q) == data["class_number"]
        and data["class_number"] % 25 != 0
    )
    phi = [int(i % 5 == 0) for i in range(21)]
    C = Quotient(phi)

    def period(a):
        value = C.zero
        for k in (1, 7, 18, 24):
            value = add(value, C.power(C.x, k * a % 25))
        return value

    t = add(period(1), scale(period(16), 2))
    gt = add(period(16), scale(period(16**2), 2))
    g = tuple(
        Fraction(x, data["gamma_t_denominator"]) for x in data["gamma_t_numerators"]
    )
    assert C.evaluate(f, t) == C.zero and C.evaluate(g, t) == gt and t != gt
    assert Q.evaluate(f, g) == Q.zero
    one = (Q.one, Q.zero)

    def mul(u, v):
        a, b = u
        c, d = v
        bd = Q.mul(b, d)
        return add(Q.mul(a, c), scale(bd, -hnorm)), add(
            add(Q.mul(a, d), Q.mul(b, c)), bd
        )

    def cc(z):
        a, b = z
        return add(a, b), scale(b, -1)

    def gamma(z):
        return tuple(Q.evaluate(v, g) for v in z)

    def pw(a, n):
        return power(a, n, mul, one)

    def field_data(key):
        v, den = data[key]
        u = tuple(Fraction(x, den) for x in v)
        return u[:5], u[5:]

    y = field_data("y")
    R = field_data("gamma_ratio_root")
    local = field_data("local_root")
    assert mul(gamma(y), pw(cc(y), 6)) == mul(pw(R, 25), mul(gamma(cc(y)), pw(y, 6)))

    trace_t = [5]
    for j in range(1, 5):
        trace_t.append(
            -j * f[5 - j] - sum(f[5 - i] * trace_t[j - i] for i in range(1, j))
        )

    def characteristic(v):
        traces = [10]
        z = one
        c = [1]
        for k in range(1, 11):
            z = mul(z, v)
            tr = add(scale(z[0], 2), z[1])
            traces.append(sum(a * b for a, b in zip(tr, trace_t)))
            c.append(-Fraction(sum(c[k - j] * traces[j] for j in range(1, k + 1)), k))
        return c

    chy = characteristic(y)
    assert all(c.denominator == 1 for c in chy)
    # Lift each prime of the stated divisor all the way to p^25.
    # The total norm then leaves no room for another factor.
    expected = 1
    seen = set()

    def simple_lift(poly, root, p):
        deriv = [i * poly[i] for i in range(1, len(poly))]
        assert eval_mod(poly, root, p) == 0 and eval_mod(deriv, root, p)
        mod = p
        for _ in range(24):
            mod *= p
            root = (
                root
                - eval_mod(poly, root, mod) * pow(eval_mod(deriv, root, mod), -1, mod)
            ) % mod
        assert eval_mod(poly, root, mod) == 0
        return root

    for p, rt, rh, degree in data["divisor_primes"]:
        key = p, rt, rh
        assert key not in seen and trial_prime(p) and (1 - 4 * hnorm) % p
        seen.add(key)
        assert poly_gcd(f, [i * f[i] for i in range(1, 6)], p) == [1]
        mod = p**25
        h = simple_lift([hnorm, -1, 1], rh, p)
        if rt is None:
            assert p == 2 and degree == 5
            # Irreducible factors of X^32-X have degrees dividing 5.
            assert all((a - b) % 2 == 0 for a, b in zip(Q.power(Q.x, 32), Q.x))
            assert poly_gcd(f, [0, -1, 1], 2) == [1]
            assert all(
                (mod_value(a, mod) + h * mod_value(b, mod)) % mod == 0
                for a, b in zip(*y)
            )
        else:
            assert degree == 1
            root = simple_lift(f, rt, p)
            assert (
                eval_mod(y[0], root, mod) + h * eval_mod(y[1], root, mod)
            ) % mod == 0
        expected *= p ** (25 * degree)
    assert chy[-1] == expected

    delta = mul(cc(y), pw(local, 25))
    delta = tuple(add(a, scale(b, -1)) for a, b in zip(y, delta))
    assert (
        valuation(characteristic(delta)[-1], 5) == data["local_precision"]
        and data["local_precision"] > 40
        and valuation(characteristic(local)[-1], 5) == 0
    )

    for test in data["residue_tests"]:
        p, rt = test["d"], test["t"]
        assert (
            trial_prime(p)
            and p % 16 == 7
            and (p + 1) % (3 * 7 * q) == 0
            and valuation(p + 1, 5) == 2
        )
        assert eval_mod(f, rt, p) == 0 and pow(-5 * q, (p - 1) // 2, p) == p - 1

        def prodmod(u, v):
            a, b = u
            c, d = v
            return (a * c - hnorm * b * d) % p, (a * d + b * c + b * d) % p

        a, b = (eval_mod(x, rt, p) for x in y)
        norm = (a * a + a * b + hnorm * b * b) % p
        residue = prodmod(prodmod((a, b), (a, b)), (pow(norm, -1, p), 0))
        detected = power(residue, (p * p - 1) // 25, prodmod, (1, 0))
        assert list(detected) == test["residue"]
        order = next(
            k for k in [1, 5, 25] if power(detected, k, prodmod, (1, 0)) == (1, 0)
        )
        assert order == test["order"]
        raw = {1: 0, 5: 5, 25: 1}[order]
        sizes = []
        for n in range(1, 5):
            k = min(2, n)
            val = 5 ** max(n - 2, 0) * raw
            sizes.append(sum((i * val) % 5 ** min(n, 2) == 0 for i in range(5**k)))
        assert (
            sizes == {1: [5, 25, 25, 25], 5: [5, 5, 25, 25], 25: [1, 1, 5, 25]}[order]
        )
        print("d", p, "residue", detected, "order", order, "finite strict sizes", sizes)
    print("Norm and divisors verified. Gamma acts by 6 modulo 25th powers.")
    print("Hensel valuation at 5:", data["local_precision"])
    print(
        "Reduced quadratic forms at discriminant",
        -5 * q,
        ":",
        quadratic_class_number(-5 * q),
    )


if __name__ == "__main__":
    for name in ("order25_witness.json", "order25_at_106619.json"):
        verify(name)
