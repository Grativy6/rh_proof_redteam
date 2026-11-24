# All positive odd twists at 2179 and 106619

**24 November 2026.** We tried to raise either of the earlier strict groups beyond order 25 by changing the cyclotomic twist while preserving the order-25 class. The answer for these two conductors is periodic over **all** positive odd twists. For $q=2179$ and for $q=106619$, at $\ell=5$, put $A_j=(\mathbb Q_5/\mathbb Z_5)(\chi_{-q}^{-1}\varepsilon^{-j})$. Then

| Positive odd $j$ | Strict group over $\mathbb Q$ |
| --- | --- |
| $j\equiv3\bmod4$ | Trivial |
| $j\equiv1\bmod4$, $j\not\equiv1\bmod20$ | $C_5$ |
| $j\equiv1\bmod20$ | $C_{25}$ |

This closes the search for a larger length in either of these fixed character sectors. The two sectors have different characteristic-zero explanations. The [new fixed conductor-256 class](2026-11-24-a-class-inside-the-zeta-windows.md) tests the final window independently of both.

## Why finitely many readings settle infinitely many twists

Cohomology with coefficients of order $5^n$ only sees $j\bmod 4\cdot5^{n-1}$. At 5 an inertia scalar differs from one by a unit for every odd $j$. Globally the invariants vanish, and at primes away from 5 the inertia invariants of the divisible module are all or zero. These facts identify strict finite-coefficient classes, with the source's inertia conditions away from 5, with the $5^n$-torsion of the divisible strict group. At any unramified rational prime a positive twist has nonzero Frobenius-minus-one scalar on the divisible module, hence an unramified class there vanishes locally. [Exact finite and divisible conditions](2026-11-24-two-classes-of-order-twenty-five.md)

At $j\equiv3\bmod4$ the residual Kummer character is $\chi_{-q}$. The radicand descends to $\mathbb Q(\sqrt{-q})$ across prime-to-five degree. Strictness at 5 and unramifiedness elsewhere make all its valuations multiples of five. Its class injects into the 5-torsion of the ideal class group since this imaginary quadratic field has no 5-primary units. Reduced forms give class numbers **7** and **119** for the two fields. Thus neither group has an element of order five.

At $j\equiv1\bmod4$ the order-five group is the same one-dimensional group for every twist, as in the previous [Kummer witnesses](2026-11-24-two-classes-of-order-twenty-five.md). At $j\equiv1\bmod20$ those same witnesses supply order 25. To bound the exponent at $m=25,125$, restrict a hypothetical strict class to $\mathbb Q(\zeta_{mq})$. Restriction preserves its order because the finite abelian quotient contains a central coefficient scalar whose difference from one is a unit. All valuations of the radicand are multiples of $m$. The kernel of the map to ideal classes lies in units modulo powers. On the odd part these come from roots of unity, and at $q$ the radicand character has sign $-1$ while inertia fixes all the 5-power roots of unity. Thus an eigenclass of exact order $m$ would yield an ideal class of exact order $m$. This argument works even when $5\mid j+1$ and the faithful radicand field drops in degree.

On that ideal class the [Jacobi divisor annihilator](2026-11-24-why-the-classes-stop-at-twenty-five.md#a-divisor-identity-at-a-splitting-prime) acts by
$$k_m(j)=\sum_{mq/2<a<mq,\ (a,mq)=1}\left(\frac aq\right)a^{-(j+1)}\pmod m.$$

| $q$ | $k_{25}$ at $j=1,5,9,13,17$ | $k_{125}$ at $j=1,21,41,61,81$ |
| ---: | --- | --- |
| 2179 | $0,15,5,20,10$ | $0,75,25,100,50$ |
| 106619 | $0,10,20,5,15$ | $50,100,25,75,0$ |

A nonzero entry prevents an element of that column's order. This leaves just one possible twist residue modulo 100 at each conductor. At 2179 the [previous digit-161 obstruction](2026-11-24-why-the-classes-stop-at-twenty-five.md#at-2179-the-obstruction-is-local) excludes order 125 at $j=1$.

## The remaining local test at 106619

Here the exceptional residue is $j=81$. Take $f=125q$, $r=12f+1=159928501$, prime, with primitive element 7. Form the Jacobi sum and radicand as in the previous calculation, now with weights $\chi_{-q}(a)a^{-82}\bmod125$. The zero divisor multiplier gives a relaxed class at coefficient order 125. The relaxed group is cyclic: its 5-torsion is the stage-one group calculated from the mirror field with class number 480, divisible by five only once. This comparison also applies at $j=81$ because the residual action is unchanged.

Norming the Jacobi sum over the 53,309 square conjugates at $q$ leaves three rows of 125 coefficients. Evaluate the quadratic periods using a root of $T^2+106619\bmod625$ and use $u=2-\zeta_{125}-\zeta_{125}^{-1}$ as local uniformizer. For a putative 125th root, the first nontrivial digit of the fourth power of the radicand occurs at 115. The successive nonzero corrections $(i,b)$ using $(1+u^i)^{125b}$ are
$$(3,4),(4,1),(5,4),(6,1),(7,4),(8,3),(9,1),(10,3),(11,1),(12,2).$$
The remainder begins at **161**. The fifth-power digit map is $i\mapsto\min(5i,50+i)$, and three iterations jump from 160 to 163. No root has an available leading digit at 161. There are local fifth and 25th roots. The relaxed class therefore lies outside the strict subgroup which already contains $C_{25}$. Cyclicity rules out a strict order-125 class. Any higher order would supply one. [Coefficients](twist-precision/orbit_coefficients.json) · [Digit and twist verifier](twist-precision/twist_precision.py)

The Python computation rebuilds the 375 coefficients using the square generator 5 and binary subdivision of its orbit. A separate C++ calculation uses the generator 4, ternary subdivision, and FLINT polynomial multiplication modulo 625. They agree on every coefficient. PARI/GP tests the three powers directly in the degree-50 real local field and gives `[1,1,0]`. The reference runs used NumPy 2.3.5, gmpy2 2.2.1, FLINT 3.0.1 and PARI/GP 2.15.4. [Independent FLINT calculation](twist-precision/flint_norm.cpp) · [Independent local-field calculation](twist-precision/local_power.gp)

From `receipt-archives/twist-precision`, `python -B twist_precision.py` checks the table and local obstruction. Add `--rebuild-norm` to recompute the full norm. The accelerated run used about 640 MB for the first logarithm table plus the space for the polynomial arithmetic. The alternative replay, from the same directory with FLINT development files and PARI/GP available, is

```sh
src=$PWD
tmp=$(mktemp -d)
c++ -O3 -std=c++17 "$src/flint_norm.cpp" -lflint -o "$tmp/norm"
(cd "$tmp" && ./norm independent-three.json && gp -fq "$src/local_power.gp")
```

## Which trace explanation persists?

At 2179, for $j\equiv1\bmod4$ multiply the mod-five reduction of the [weight-two cusp form](2026-11-24-one-adjoint-at-2179.md) by $H^{(j-1)/4}$ on the same tame modular curve. Its $q$-expansion stays fixed. At primes away from 5 the change of weight preserves the Hecke recurrence modulo five, and at 5 the eigenvalue remains a unit. Thus it is a cuspidal ordinary eigensystem at weight $j+1$. The tame cusp lattice surjects onto the mod-five space (regular differentials at weight two and vanishing of the dual negative-weight sections at higher weights). The diamond projector is integral. A maximal ideal of its finite torsion-free Hecke algebra lifts to characteristic zero, giving an ordinary characteristic-zero eigenform of that weight. The primitive nebentypus forces the same conductor. The residual ratio has order four, so the same coset trace argument as at weight two excludes dihedral induction. Its adjoint gives a cuspidal point in the required arithmetic level and flag. For $j>1$ no two flag weights differ by one, so a potential cyclotomic link is excluded already on inertia. Galois conjugates of the Hecke system remain in the same space and satisfy these same conditions. Since the length is at most two, the norm over the distinct local trace-field conjugates supplies the pointwise numerical bound for every such $j$. Here we assert the scalar `OneCharU` conclusion. The previously constructed [explicit marked family](2026-11-24-the-two-tangent-signs.md) is for weight two.

At 106619 the proposed rational adjoint at these twists would instead have a weight-$j+1$ cusp form on the minimal level with residual character $1\oplus\chi_{7q}\omega$. The tame bad-prime coefficients agree with the normalized Eisenstein system after twisting away the weight-zero character, and ordinarity fixes the coefficient at 5. The weight-two Eisenstein constant is nonzero modulo five from $B_{2,\chi_{7q}}\equiv3$. Multiply by the appropriate Hasse power and compare the constant $q$-expansion. Its fourth power would force $4\mid j+1$ by the simple supersingular zero, whereas $j+1\equiv2\bmod4$. The rational adjoint therefore fails throughout the nonzero-length twists. The corner alternative reduces in the same way to weight three and character $\eta=\chi_{-7}$. There $B_{3,\eta}=48/7$ and $B_{3,\eta}/3=16/7\equiv3\bmod5$, again nonzero. This extends the [original $a_{11}$ exclusion](2026-11-24-the-rank-two-alternative-at-571.md) across these weights. [Tame-level and Hasse-invariant argument](2026-11-24-the-rank-three-obligation-at-577.md)

## Unresolved

At 106619 the signed two-prime test still needs a genuine marked non-self-dual cuspidal system on its required residual character. Changing the positive odd twist does not increase the strict length beyond two. The fixed character at 577 supplies a separate in-window test where the same-kernel orbit can also be measured.
