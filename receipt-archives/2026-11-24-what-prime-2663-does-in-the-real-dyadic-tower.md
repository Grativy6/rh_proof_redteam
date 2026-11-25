# What prime 2663 does in the real dyadic tower

**24 November 2026.** Christopher Daniel Pang suggested testing 2663 in place of 577. His PAL and CLEF question keeps the same field tower, local conditions and observation while changing the coefficient prime. Hearthline derived the period, computed the finite obstruction and traced the one surviving candidate to a circular unit. Alpöge and Claude supply the arithmetic groups and the window in which they are counted. The classical class-field and circular-unit criteria are identified below. [PAL atlas](../corpus/PAL_v2.4-M_Mathematical_Realization_Atlas.docx) · [CLEF](../corpus/CLEF_cluster_layer_entropy_focus_v1_0.pdf) · [The 577 result](2026-11-24-one-strict-class-in-the-entire-real-dyadic-tower.md)

**Result.** Put $F_m=\mathbf Q(\zeta_{2^{m+2}})^+$, $p=2663$, and $A_j=(\mathbf Q_p/\mathbf Z_p)(-j)$. For **every** $m\ge0$ and **every positive even** $j$, the group of continuous classes in $H^1(F_m,A_j)$ that are unramified away from $p$ and locally zero above $p$ is zero. At 577 this same test gives a cyclic group of order 577 when $m\ge6$ and $j\equiv296\bmod576$. The full host also has terms twisted by its two moving quadratic characters and their product. The present result covers the contribution from the real dyadic field. [Release's strict local conditions](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GaloisCohomology/Statement.lean#L54-L78) · [Character selection](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/DirichletPrimeToLPartMulLPowerPart.lean#L179-L192)

## How a possible class enters the calculation

The degree of each $F_m/\mathbf Q$ is a power of two. Restriction, corestriction and the character idempotents therefore split the $p$-primary question into even dyadic characters $\psi$. We can extend coefficients to the unramified $p$-adic ring containing their values and reduce in its residue field. A nonzero torsion group contains an element of order $p$. The exact sequence for multiplication by $p$ gives it a residual preimage for $\bar\psi^{-1}\omega^{-j}$, where $\omega$ is the mod-$p$ cyclotomic character. The residual preimage is unramified away from $p$: at a tame inertia group the invariants of the divisible coefficient module are divisible, by averaging its finite prime-to-$p$ image. Inflation and restriction here preserve the local conditions because the finite relative degrees are units at $p$.

First let $\psi$ be nontrivial of conductor $C=2^s$, $s\ge3$. Over $L=\mathbf Q(\zeta_{Cp})$, restriction is injective on residual cohomology because $[L:\mathbf Q]$ is prime to $p$. Kummer theory puts the radicand in the $\lambda=\bar\psi\omega^{j+1}$ part of $L^\times/L^{\times p}$ after extending scalars. The conjugation character on the root translations is $\omega\lambda^{-1}$. The radicand has valuations zero modulo $p$ away from $p$ by unramifiedness. At $p$, the cyclotomic inertia $\mathbf F_p^\times$ fixes the primes over $p$, and $\omega^{j+1}$ is nontrivial because $j+1$ is odd. Thus the valuation component there vanishes as well.

Dividing the principal divisor by $p$ gives a class in the $\lambda$ part of the $p$-torsion ideal class group. This detects the radicand injectively: its kernel comes from units. For a CM unit $u$, $u/\bar u$ is a root of unity by the absolute values of its conjugates. The odd unit part modulo $p$ can therefore contribute only the cyclotomic character $\omega$, whereas $\lambda$ is nontrivial on dyadic inertia. The exact Kummer and divisor sequences allow these arguments after character projection. [Earlier derivation on this tower](2026-11-24-one-strict-class-in-the-entire-real-dyadic-tower.md#which-finite-calculation-can-rule-out-a-character)

The integral Jacobi-sum divisor annihilator consequently gives a necessary congruence
$$K(\psi,j)=\sum_{\substack{Cp/2<n<Cp\\(n,Cp)=1}}\bar\psi(n)^{-1} n^{-j-1}=0\pmod p.$$
For a rational prime splitting completely in $L$ the Jacobi sum for two copies of a character of order $Cp$ gives exponent $\lfloor2n/(Cp)\rfloor$ on the conjugate prime labelled by $n$ (with the inverse Galois element in the divisor operator). This follows by reducing the character sum and its conjugate and using their product equal to the rational prime. Every ideal class has such a representative by Chebotarev in the Hilbert class field. Hence the operator kills the class group and acts on this component by the displayed scalar. [Jacobi divisor derivation and conventions](2026-11-24-the-577-class-on-paper.md#the-element-and-its-divisor)

## Why a finite product covers every level

Set $M=(p-1)/2=1331=11^3$. Direct modular powering gives $2^{1331}=1$ and $2^{121}=72\bmod p$, so $2$ has order 1331. Every even twist is represented by $j=0,2,\ldots,2660$. The even dyadic labels are powers of $5$ modulo sign, and $Z=\bar\psi(5)^{-1}$ has order $C/4$.

For $s\ge6$ put $h=C/64$. The root $\xi=Z^h$ has order 16. Since $p\equiv7\bmod16$ and $v_2(p^2-1)=4$, successive squaring gives $\operatorname{ord}_{C/4}(p)=2h$. It follows that $1,Z,\ldots,Z^{h-1}$ is a basis over $\mathbf F_{p^2}$. In the sum for $K$, group powers of $Z$ by their exponent modulo $h$. The coefficient of the basis element $1$ uses precisely the dyadic columns $\pm5^{hk}$ for $0\le k<16$. If that coefficient is nonzero, the whole sum is nonzero for every lift $Z$ of $\xi$.

For $s\ge9$, $5^h=1+15(C/16)\bmod C$. At $s=9$ this is $5^8=481\bmod512$. Squaring proves the next case since $(C/16)^2$ is divisible by $2C$. The least positive labels are therefore $t_k=1+(C/16)u_k$, where $u_k=15k\bmod16$ in $[0,15]$. All lifts of this label are $n=t_k+Cb$, $0\le b<p$. The upper half takes $b>M$ and also $b=M$ exactly when $u_k\ge8$.

Put $r_k=C^{-1}+u_k/16$ in $\mathbf F_p$. In the next sum omit any zero argument. A unit multiple of the coefficient just described is
$$H_{s,j}(\xi)=\sum_{k=0}^{15}\xi^k\left(
\sum_{b=M+1}^{p-1}(r_k+b)^{-j-1}
+{\bf1}_{u_k\ge8}(r_k+M)^{-j-1}\right).$$
The multiplier restoring the coefficient is $2C^{-j-1}$. Indeed the positive and negative dyadic columns have the same upper-half sum: $n\mapsto Cp-n$ changes the sign of the odd power, while the complete signed power sum on a residue column is zero.

Here $s$ matters only through $2^s\bmod p$, with period 1331. The eight primitive sixteenth roots fall into four Frobenius pairs. The product of the norms $N_{\mathbf F_{p^2}/\mathbf F_p} H_{s,j}(\xi)$ over $9\le s<1340$, all 1331 twist residues, and one root from each pair is
$$\boxed{95\bmod2663}.$$
This finite computation proves that no one of the 7,086,244 factors vanishes.

The [exact replay](check_prime_2663.py) evaluates the positive and negative columns using the actual residues of $5^{hk}$ at each of the 1331 conductors, and independently implements the periodic formula. It evaluates at $\xi=(484+1147i)^b$ for $b=1,3,9,11$, $i^2=-1$. It also reduces the polynomials modulo the four quadratics $X^2-TX-1$, with $T=369,968,1695,2294$. Their roots have order 16 since $T^4+4T^2+2=0$, their product is $X^8+1$, and the norm of $a+bX$ is $a^2+Tab-b^2$. The program compares the two multisets of four norms separately for every period and twist. Sixteen additional entries are recomputed by summing the original unscaled CRT lifts term by term. All modular products use integers.

## The one small-conductor candidate

For $s=3,\ldots,8$, enumerate all cosets of the subgroup generated by $5^h$ when $C/4>16$, and sum the entire orbit directly when $C/4\le16$. Checking the same upper-half expression for every even twist gives the following complete list.

| Conductor | Pairs with zero divisor test |
| --- | --- |
| 8 | Quadratic character $\chi_8$, $j\equiv1232\bmod2662$ |
| 16, 32, 64, 128, 256 | None |

For that one pair the residual Galois character is $\theta=\chi_8\omega^{-1232}$. Its cyclotomic part has order 121, so at $p$ there are no local invariants that could prevent the residual preimage from being locally zero. Over $L$ the preimage now gives an everywhere unramified character. Its $\theta$ is even, so a nonzero class would require a nonzero $\theta$ part of the $p$-class group of $L^+$. The transfer between $L$ and $L^+$ on the plus part has degree two, invertible at $p$.

Take $f=8p$, the prime $r=63913=24p+1=3f+1$, and $z=2197=13^3\bmod r$ of order $f$. The integer 13 is a primitive root modulo $r$. For each unit $a\bmod f$ use the exponent $w(a)=[\chi_8(a)a^{1232}]_p$ in $[0,p-1]$. At the prime taking $\zeta_f$ to $z$, the projected circular unit has the explicit reading
$$u=\prod_{a\in(\mathbf Z/f)^\times}(1-z^a)^{w(a)}=60430\bmod r,\qquad u^{24}=41215\bmod r.$$
In particular $u$ is not a $p$th power in the residue field. Pairing $a$ with $-a$ expresses the global unit as a product of conjugates of $N_{L/L^+}(1-\zeta_f)$. This is a real circular unit because $f$ has two prime divisors. Its weights are the inverse of $\theta$, so its class modulo $p$ is in the $\theta$ component.

The $\theta$ component of the full units has rank one over $\mathbf Z_p$ by the unit theorem ($\theta$ is nontrivial and takes values in $\mathbf Z_p^\times$ after Teichmüller lifting). The non-power test makes the circular unit primitive in this component, hence its circular units already span the full unit lattice there. Greither's Corollary 4.15 identifies the character lengths of units modulo circular units and of the class group for the real abelian field $L^+$, whose degree $2(p-1)$ is prime to $p$. It follows that the necessary $\theta$ class group is zero. This application uses the character-specific theorem as well as the numerical reading. [Greither, Corollary 4.15](https://www.numdam.org/item/10.5802/aif.1299.pdf#page=48)

## The principal character and the irregular index

The one irregular Bernoulli index is **1244**. Inverting the truncated series $(\exp X-1)/X$ modulo $p^2$ gives $B_{1244}/p=612\bmod p$. Exact rational evaluation of that Bernoulli number in PARI/GP gives the same residue. For the corresponding real-class test take the prime $r=31957=12p+1$ and the order-$p$ root $z=4096\bmod r$. The Buhler–Harvey product is
$$V=\prod_{c=1}^{1331}(z^c-z^{-c})^{c^{2662-1244}}=29748\bmod r,
\qquad V^{12}=19454\bmod r.$$
Their criterion for all irregular indices therefore verifies that $p$ does not divide the class number of $\mathbf Q(\zeta_p)^+$. The irregular index itself records a minus-component phenomenon. [Buhler and Harvey, §4](https://arxiv.org/pdf/0912.2121#page=5)

For the trivial dyadic character, a strict class of order $p$ again has a residual preimage. The global and $p$-local cyclotomic images over $\mathbf Q$ are both $\mathbf Z_p^\times$, so their invariants on $A_j$ agree. Subtracting a global connecting class therefore makes this preimage locally zero even when $j$ is a multiple of $p-1$. Over $\mathbf Q(\zeta_p)$ the preimage gives an unramified class-group character with even action $\omega^{-j}$. The real-class calculation excludes it. This completes all dyadic characters for the stated group.

## Two other places the number could enter

**As a moving prime.** The first slot requires $q=3\bmod8$ and 2663 is $7\bmod8$. It has the right residue $7\bmod16$ for $d$, but is too small for every admissible window scale $Y\ge1$. Write $A=Y^{\epsilon/5}$. From $A\ge\log q\ge\log3>13/12$ and $0<\epsilon<1/52$ we get $\log Y>260\log(13/12)>20$. The lower bound $\log d>A(\log Y)^2/2$ gives $\log d>200$, whereas $\log2663<9$. The estimate for $\log3$ follows from the first two positive terms of $2\operatorname{arctanh}(1/2)$. The additional condition $q\mid2664=2^3 3^2 37$ would in any case leave only $q=3$. Independently, $\mathbf Q(\sqrt{-2663})$ has class number 43 by enumeration of reduced positive binary forms, and either prime above 2 has order 43 since no element has norm 2. The explicit identity $5137947^2+2663\cdot57439^2=2^{45}$ gives a generator of a 43rd power via $(5137947+57439\sqrt{-2663})/2$, whose odd trace excludes the conjugate prime from its divisor. [Window inequalities](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L19-L47) · [Reduced forms and identity](check_prime_2663.py)

**As the distinguished split prime.** Rank three gives $(2663-1)^2=4\cdot11^6=7{,}086{,}244$ surviving directions in the [local projector](2026-11-24-the-integral-cost-of-the-distinguished-prime-projector.md). The trace of its idempotent on the integral regular representation reads zero modulo $11^6$. The image remains a summand of that full rank. Modulo $11^7$, its trace first distinguishes it from the zero operator. Here the residue size 2663 is a unit at $\ell=11$. A concrete field meeting the place conditions is $E=\mathbf Q(\sqrt{-23},\sqrt{-43})$. Both quadratic discriminants split at 2663 and have opposite symbols at 11. As in the preceding projector calculation, their coprime discriminants give no finite ramification over their real quadratic subfield. The source compares the rank of the projected space. [Place and coefficient hypotheses](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/WeilGroupCharacters/ContinuousResP.lean#L82-L92) · [Dimension used in the release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TZEqDimE.lean#L86-L104)

## Reproduction and scope

Run `python -B check_prime_2663.py` in the receipt archive with Python and NumPy. The largest dot products use 16 terms bounded by $(p-1)^2$, and the products across cases are reduced modulo $p$ in pairs. No approximation of a complex root enters the result.

## Unresolved

The full host contains three additional character sectors involving its moving quadratic primes. The vanishing proved here disposes of the pure real dyadic contribution at 2663. Whether a moving-character term forces a failure at the eventual cutoff remains open.
