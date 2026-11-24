# Why the two groups stop at 25

**24 November 2026.** The [two explicit order-25 classes](2026-11-24-two-classes-of-order-twenty-five.md) face different obstructions to order 125. At $q=106619$ a global divisor calculation gives $50x=0$ on a subgroup of exponent 125. At $q=2179$ the same multiplier is zero modulo 125. There a local unit at 5 has a nonzero digit at a position no 125th power can reach. Together with cyclicity these give the **exact** strict groups for both inputs. The previously reported Browkin–Gangl table motivated the test at 2179. Its conjectural entry is no premise of either calculation. [Conjectural table](https://www.maths.dur.ac.uk/users/herbert.gangl/k2table.pdf) · [Exact divisor sums](selmer-order-25/check_two_sums.py)

## A divisor identity at a splitting prime

Write $m=125$, $f=mq$, $F=\mathbb Q(\zeta_f)$, $\psi(a)=(\frac{a}{q})$, and $\lambda(a)=\psi(a)a^2\bmod m$. For either $q$, $[F:B]=2(q-1)$ is prime to 5 for the degree-50 field $B$ of the preceding receipt. Given a prime $r\equiv1\bmod f$, choose a primitive element $g$ of $\mathbb F_r^\times$, a prime $P\mid r$ with $\zeta_f\mapsto g^{(r-1)/f}$, and a character $\chi(g)=\zeta_f$. Form the algebraic integer
$$J=\sum_{x\in\mathbb F_r\setminus\{0,1\}}\chi^{-1}(x)\chi^{-1}(1-x).$$
The character and its square are nontrivial, and character orthogonality gives $J\bar J=r$. For instance, expand the absolute square of each Gauss sum and use additive orthogonality to get norm $r$. Multiplying two Gauss sums and grouping by the sum of the arguments gives the Jacobi-sum quotient. Thus the only possible valuations are zero and one over $r$.

Let $\sigma_a(\zeta_f)=\zeta_f^a$ with $1\le a<f$, $(a,f)=1$. At $P$, $\sigma_a J$ reduces to $\sum_x x^e(1-x)^e$ for $e=(r-1)(1-a/f)$. The exponents in the expansion run from $e$ through $2e<2(r-1)$. A sum of powers can be nonzero only at exponent $r-1$, and its binomial coefficient is nonzero modulo $r$ whenever it occurs, since $e<r$. Therefore $v_P(\sigma_aJ)=\lfloor2a/f\rfloor$. In particular the integral group-ring element
$$T=\sum_{(a,f)=1}\lfloor2a/f\rfloor\,\sigma_a^{-1}$$
sends $P$ to the principal divisor of $J$. Every ideal class of $F$ has such a representative. Its Hilbert class field is Galois over $\mathbb Q$. Apply Chebotarev to a representative of the required class in the subgroup over $F$ and choose a prime above the rational prime with that specific Frobenius. The rational prime splits in $F$ and the resulting prime of $F$ is in the desired class by class field theory. Thus $T$ annihilates the entire ideal class group of $F$.

## At 106619 the global obstruction suffices

Any strict level-three class gives an eigen-power-class $z$ in $B^\times/B^{\times125}$ with every valuation divisible by 125. At 5 this follows from local triviality. Map it to $[I]$ by $(z)=I^{125}$. The kernel comes from units modulo 125. For a unit $u$ in the CM field $B$, $u/\bar u$ is an algebraic-integer unit of absolute value one at every embedding, hence a root of unity. The field $B$ has a unique quadratic subfield $\mathbb Q(\sqrt{-5q})$ and contains no $\mu_5$. Complex conjugation therefore acts trivially on its units modulo 125, while $\lambda(-1)=-1$. The map to the class group is injective in this sector. Extending ideals to $F$ is injective on this 5-primary subgroup because the norm after extension raises to $[F:B]$, a unit modulo 125.

On the resulting ideal class the multiplier of $T$ is
$$k=\sum_{f/2<a<f,\ (a,f)=1}\left(\frac aq\right)a^{-2}\pmod {125}.$$
For $q=106619$ the sum is **50**. Hence $50[I]=0$, so $25[I]=0$ since 2 is a unit. This excludes a strict class of order 125. Any element of greater order, including elements in a divisible subgroup, would have a multiple of order 125. With the lower witness and the one-dimensional residual group this gives $S(A)=C_{25}$. [Standard-library calculation](selmer-order-25/check_two_sums.py)

## At 2179 the obstruction is local

Here $k=0\bmod125$. Use $r=20f+1=5447501$, prime, with primitive element 2. For each unit $a\bmod f$ let $w(a)\in[-62,62]$ represent $\lambda(a)^{-1}$. Define
$$\beta=\prod_a(\sigma_aJ)^{w(a)}.$$
The weights are constant on $\ker\lambda$, which puts $\beta$ in $B$. For any $s$, reindexing multiplies its exponent vector by $\lambda(s)$ modulo 125, so $\sigma_s\beta/\beta^{\lambda(s)}$ is a 125th power in $F$. Descent of that power across $F/B$ follows by the norm and coprime degree. At $P$ its valuation is $k=0\bmod125$. All the conjugate valuations are scalar multiples of $k$ modulo 125. This makes $\beta$ a class in the relaxed group $R_3$ via Kummer descent. At primes outside 5 unramifiedness follows from the divisor condition over $F$, and the possible extra ramification at $q$ has inertia degree dividing $q-1$, prime to five. Its behavior at 5 distinguishes it from the strict subgroup.

Take the local embedding $\sqrt{-2179}=264\bmod625$. To compute $\beta$, first norm $J$ over the 1089 square conjugates of its $q$-part. The exponents of the resulting integral group-ring polynomial are constant on the square and nonsquare classes modulo $q$ at fixed exponent modulo 125. Evaluating the two quadratic periods $(-1\pm\sqrt{-2179})/2$ leaves two polynomials $P_+(z),P_-(z)$ with $z$ a primitive 125th root. They satisfy $P_+(z)P_-(z^{-1})=r^{1089}$. Hence every division in the remaining product for $\beta$ uses a unit. The result is invariant under $z\mapsto z^{-1}$.

In the real local field $u=2-z-z^{-1}$ is a uniformizer, $v(5)=50$, and the residue field is $\mathbb F_5$. Raise $\beta$ to the fourth power to remove its residue-field unit. This preserves the question of being a 125th power. For a unit whose first principal-unit digit occurs at position $j$, its fifth power first changes at
$$m(j)=\min(5j,50+j).$$
There is no tie for integral $j$. The binomial expansion shows that every nonzero first coefficient occurs as the first coefficient varies in $\mathbb F_5^\times$. Iterating three times gives the allowable first digits of a 125th power from $j=1,\ldots,14$,
$$75,\ 100,\ 115,\ 120,\ 125,\ 130,\ 135,\ 140,\ 145,\ 150,\ 155,\ 160,\ 163,\ 164.$$
Successively divide $\beta^4$ by $(1+u^j)^{125t}$ whenever the current digit can be cancelled. The nonzero corrections $(j,t)$ are
$$(1,2),(2,2),(3,4),(4,2),(5,3),(6,2),(8,1),(10,2),(12,2).$$
The remainder first differs from one at **161**. A different choice at any earlier position fails already at that position, since the first coefficient map is bijective. Every deeper unit starts at 163 or later after taking its 125th power. This proves nonexistence. The precision $625=5^4$ retains 200 digits of the real uniformizer. For fifth and 25th powers, the same cancellation reaches the range $j>50/4$ at the root, where the fifth-power map shifts every digit by 50 and is onto the deeper filtration. Both of those roots exist. [Jacobi sum, precision and digit verifier](selmer-order-25/jacobi_obstruction.py)

The cyclic relaxed group $R_3$ already contains the strict subgroup of order 25. The nonlocal class $\beta$ is outside that subgroup. Hence $R_3$ has order 125 and the strict subgroup has order exactly 25. A higher-order strict element would yield a strict order-125 element. This proves $S(A)=C_{25}$ here as well.

## Reproduce the local calculation twice

Run `python -B jacobi_obstruction.py` in `receipt-archives/selmer-order-25` with NumPy. The first implementation packs coefficients into exact integers with a checked no-carry bound. Optional `gmpy2` accelerates multiplication. Independently, the C++ program uses two finite-field number-theoretic transforms and exact CRT with a coefficient bound. It takes the norm along subgroups of indices 3, 11, 3 and 11. PARI then tests powers directly in the degree-50 local number field. From that same directory, using a temporary directory for outputs, run

```sh
src=$PWD
tmp=$(mktemp -d)
c++ -O2 -std=c++17 "$src/jacobi_norm.cpp" -o "$tmp/jacobi_norm"
(cd "$tmp" && ./jacobi_norm independent-norm.txt && gp -fq "$src/check_local_powers.gp")
```

The independent power answers in order are `[1,1,0]`. The reference replay used NumPy 2.3.5, GMP 6.3.0 via gmpy2 2.2.1, and PARI/GP 2.15.4. [Integer convolution and norm](selmer-order-25/jacobi_norm.cpp) · [Independent local power tests](selmer-order-25/check_local_powers.gp)

## Unresolved

The class calculation fixes the left side of the released trace inequality at two in both examples. Its right side behaves differently. [Trace contribution at 2179](2026-11-24-one-adjoint-at-2179.md) · [Obstruction at 106619](2026-11-24-where-the-adjoint-disappears.md)
