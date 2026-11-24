# The last possible 577th-power lift

**24 November 2026.** For the even character $\psi$ of conductor 256 in the [actual zeta windows](2026-11-24-a-class-inside-the-zeta-windows.md), the strict group over $\mathbb Q$ is **exactly $C_{577}$ at every positive twist $j\equiv296\bmod576$**. The previously exceptional residue $j\equiv265256\bmod(576\cdot577)$ does acquire a relaxed class of order $577^2$. Its local obstruction at 577 is nonzero. Two separate primes give **177 modulo 577** after normalizing to the same original class. This closes the [exception left by the divisor multiplier](2026-11-24-one-of-thirty-two-characters.md#what-happens-when-the-twist-changes).

## Produce two order-squared classes on the actual characters

Put $p=577$, $m=p^2$, $f=256m$ and $F_2=\mathbb Q(\zeta_f)$. Use the primes $r_A=340919297=4f+1$ and $r_B=1022757889=12f+1$. For either $r$ let $\chi$ send the least primitive element of $\mathbb F_r^\times$ to $\zeta_f$. As before use the Jacobi sum $J=\sum_{x\ne0,1}\chi^{-1}(x)\chi^{-1}(1-x)$. Take a weighted product of its conjugates with weights representing $\lambda_2(a)^{-1}$, where $\lambda_2=\psi\varepsilon^{j+1}\bmod p^2$. This gives the radicand $\beta_{r,2}$ for the twisted coefficient $\psi^{-1}\varepsilon^{-j}$. Reindexing proves the power-class eigencondition. Restriction and inflation preserve the global class and its order because the finite abelian quotient contains a central coefficient scalar whose difference from one is a unit.

The divisor of $J$ at the split prime is given by the upper-half carry $\lfloor2a/f\rfloor$. Consequently each conjugate valuation of the product is a unit multiple modulo $p^2$ of $p\,k(j)$ with
$$k(j)=261+37(j+1)\pmod p.$$
This is the same finite sum as $287+540u$ for $j=296+576u$. At $j=265256$ it is zero. Thus the classes there are unramified away from $p$. At other weights these particular representatives may have controlled last-digit inertia at their indicated auxiliary prime. [Divisor argument](2026-11-24-why-the-classes-stop-at-twenty-five.md#a-divisor-identity-at-a-splitting-prime) · [Level-squared multiplier](fixed-character-577/bounds.py)

Reduction of each new class is exactly its first-level Jacobi class. Use compatible primitive roots and $F_1=\mathbb Q(\zeta_{256p})$. Above each split prime of $F_1$, the $p$ translates of the upper-half divisor have $(p-1)/2$ constant carries plus the original upper-half carry. Thus $\mathrm N_{F_2/F_1}J_2$ and $r^{(p-1)/2}J_1$ have the same principal ideal. All their conjugates have absolute value $r^{p/2}$, so their quotient is a root of unity. Roots of order prime to $p$ are $p$th powers. Inertia at 2 fixes every $p$-power root and acts nontrivially in the required character, so projection kills that part as well. The rational factor disappears because the sum of the character weights is zero modulo $p$. The wild weights all reduce to one. At the fixed detecting prime 2363393, the first-level exponents are 507 and 101. Both new global classes therefore project to generators. The strict residual group is $C_p$ and the relaxed residual group is also $C_p$ by the [original field calculation](2026-11-24-the-577-class-on-paper.md). The relaxed divisible group has $p$-rank one, by the same invariant and inertia argument for a positive twist. In particular its $p^2$-torsion is cyclic.

## A missing digit in local units

In the composite local cyclotomic field write $Y^4=\operatorname{Teich}(20)$ for the unramified quartic part. The fixed field for the common tame kernel has ramification degree $e=64p=36928$. We may include the unramified quartic extension without changing the power test, since its degree is prime to $p$. The full cyclotomic local field has ramification degree $d=p(p-1)=332352$, nine times $e$. The subgroup of order nine on its ramified side fixes all our radicands. A root in this degree-nine extension would also give a root in its fixed field by taking the norm and using that 9 is invertible modulo $p^2$. In the field of ramification degree $e$, the leading-digit map for a $p$th power on principal units is
$$i\longmapsto \min(pi,e+i).$$
There is no tie at integral $i$. Two iterations give $e+pi$ for $1\le i\le64$ and $2e+i$ for $i\ge65$. They jump from **73856 to 73921**. A nonzero remainder at $2e+33=73889$ is impossible for a $p^2$th power.

Here is how we compute that remainder. Let $\pi$ and $\pi_1$ be the tame Teichmüller projections of $\zeta_{p^2}-1$ and $\zeta_p-1$ to inertia character $\omega$. Explicitly average $(\zeta^{a}-1)/\tilde a$ over the 576 Teichmüller elements and divide by 576. The first is a uniformizer in the full field and $\pi_1\equiv\pi^p\bmod p$. Lift $Y$ as a 256th root so $Y^p=\tilde\xi Y$, $\xi=553\bmod p$. Put $w=Y\pi^{297}$, which has valuation 33 in the degree-$e$ normalization. We chose the unramified embedding compatibly with the earlier lower-layer digit. Direct binomial expansion gives
$$ (1+cw)^{p^2}-1\equiv p\,c\,Y^p\pi^{297p}+p^2c\,Y\pi^{297}
              \pmod{p^2\pi^{577}},\qquad c\in\operatorname{Teich}(\mathbb F_p).$$
Only binomial indices 1 and $p$ can contribute at this precision. The coefficient at $p$ is $p\bmod p^2$, and $c^p=c$. Replacing $\pi^{297p}$ by $\pi_1^{297}$ costs nothing here, since $\pi^p-\pi_1$ is divisible by $p$ and the other 296 factors have valuation at least $p$ each. No logarithm with denominator $p$ is needed for the test.

For each row the calculation measures $l,h\in\mathbb F_p$ such that
$$\beta_{r,2}^{576}-1\equiv
 l\,pY\pi_1^{297}+h\,p^2Y\pi^{297}\pmod{p^2\pi^{577}}.$$
The matching power occupies the line $(l,h)=c(\xi,1)$. Cancel the lower digit with $c=l/553\bmod p$. At the exceptional twist this gives $c=219$ and $153$ at the two probes. The high remainders are $205$ and $240$ respectively. Divide by the indicated explicit $p^2$th power. In each case the first remaining digit has valuation exactly 73889, strictly inside the forbidden gap for every possible root. When the reading vanishes, the full congruence places the remainder at valuation at least $2e+65$ in the degree-$e$ field with the unramified quartic adjoined. Indeed $577/9>64$ in this normalization and the valuation is integral. On principal units of depth $65>e/(p-1)$ the logarithm and exponential are inverse. Dividing the remainder's logarithm by $p^2$ and exponentiating therefore gives the required root. This proves both directions of the local test.

In this convention $l-\xi h$ is the residual local character reading. One unit of the first-level Kummer group, normalized to logarithmic coefficient $Y$ at degree 297 after the 576th power, contributes $pY\pi_1^{297}$ upon coefficient inclusion. The first-level local group in this character is one-dimensional. Higher digits of that first-level unit are in higher tame filtration or are $p$th powers, and do not change this reading. Restriction is injective from the local twisted cohomology, by the nonidentity central residual scalar. The 576th power removes the residue-field unit in the radicand field.

| Prime $r$ | Twist $j$ | $l$ | $h$ | $l-553h\bmod577$ |
| ---: | ---: | ---: | ---: | ---: |
| 340919297 | 171368 | 514 | 0 | 514 |
| 340919297 | 296 | 514 | 254 | 263 |
| 340919297 | **265256** | 514 | 424 | **304** |
| 1022757889 | 171368 | 367 | 0 | 367 |
| 1022757889 | 296 | 367 | 445 | 84 |
| 1022757889 | **265256** | 367 | 393 | **567** |

At 171368 the radicand weight is the Teichmüller lift modulo $p^2$. This control independently recovers the [divided first-layer logarithms](2026-11-24-two-independent-obstruction-primes.md). At 265256 the two normalized readings are both 177 modulo 577. In integers the two differences are
$$177\cdot507-304=155\cdot577,\qquad 177\cdot101-567=30\cdot577.$$ In particular a lift of the original class is locally nonzero. The relaxed group already contains the strict order-$p$ subgroup. Cyclicity now forces relaxed $p^2$-torsion of order $p^2$ and strict $p^2$-torsion of order $p$. An element of higher strict order would give a strict element of order $p^2$. All twists in this residue modulo $576p$ have exactly the same finite test. Together with the divisor upper bound at all the other residues this proves the assertion for the entire sequence.

## Reproduce the computation

[The small replay](boundary-577/local_gap.py) checks the arithmetic on the [published readings and digests](boundary-577/second_level_readings.json). To recompute the entries, from `receipt-archives/boundary-577` use the following commands with NumPy, a C++17 compiler and FLINT development libraries available. Keep the binary arrays in a temporary directory. The histogram is about 170 MB per prime. The default counts the solutions of $x(1-x)=t$ by the Legendre symbol of $1-4t$, and the independent `--logs` mode uses a discrete-log table of about four bytes per residue. Both methods gave identical histogram digests.

```sh
src=$PWD
tmp=$(mktemp -d)
c++ -O3 -std=c++17 "$src/jacobi_histogram.cpp" -o "$tmp/histogram"
c++ -O3 -std=c++17 "$src/second_level.cpp" -lflint -o "$tmp/level"
cd "$tmp"
for r in 340919297 1022757889; do
    ./histogram "$r" "hist-$r.bin"
    ./level build "$r" "hist-$r.bin" "r$r"
    for j in 171368 296 265256; do
        ./level weight "r$r" "$j"
        python -B "$src/local_gap.py" --binary "r$r-e$j.bin" --prime "$r" --twist "$j"
    done
done
```

The first implementation multiplies polynomials using $W=Y\zeta_{p^2}$ with $W^{4p^2}=\operatorname{Teich}(20)^{p^2}$. It norms the 1152 kernel conjugates, projects the tame character modulo $p^3$, and accumulates both the wild norm and the product whose $i$th conjugate has exponent $i$. Since $(1+p)^{-i(j+1)}\equiv1-pi(j+1)\bmod p^2$, those two products supply every requested twist. Tame weights taken modulo $p^3$ suppress irrelevant higher powers at the precision used here. The final verifier reduces all 1,329,408 cyclotomic tensor coefficients, checks divisibility by $p$, subtracts the full lower coefficient polynomial, and checks divisibility by $p$ again. The surviving row is $A\,i^{-297}$ for $1\le i\le576$, on the $Y$ basis component. Its first nonzero Taylor coefficient, when $A\ne0$, is $-A/297!$ at index 297 by finite-field power sums. The verifier also recovers it by the binomial transform. The full row belongs to the tame character $\omega^{297}$ in $k[\zeta]/(\zeta-1)^{577}$. In the tame eigenparameter $\pi$ the monomials of degrees $0,\ldots,576$ form a basis, and just degree 297 has this character. Thus the row determines the full congruence through degree 576. Its higher coefficients in the original variable have been included in the test. [Histogram code](boundary-577/jacobi_histogram.cpp) · [FLINT norm and wild derivative](boundary-577/second_level.cpp)

A second implementation uses four separate unramified coefficient rows, 96-bit no-carry integer convolution with GMP, the locally coupled Frobenius norm of order 36, reversed tame and wild generators, and a direct weighted norm at $j=265256$. At the first prime it gives the same $514,424,304$. Its full representative differs by allowed power factors. From the same scratch directory run `python -B "$src/independent_projection.py" 340919297` with gmpy2, then `python -B "$src/local_gap.py" --alternate alt-340919297-e265256.npy --prime 340919297 --twist 265256`. The reference runs used FLINT 3.0.1, gmpy2 2.2.1, GMP 6.3.0 and NumPy 2.3.5. [Independent projection](boundary-577/independent_projection.py)

## Unresolved

The order-squared strict test is settled. Its two arithmetic obstruction directions can now be [measured separately](2026-11-24-two-independent-obstruction-primes.md). The mixed rank-three obstruction coefficients are a different calculation.
