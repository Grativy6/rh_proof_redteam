# Thirty-two identical Frobenius readings and one nonzero length

**24 November 2026.** The [persistent class](2026-11-24-a-class-inside-the-zeta-windows.md) gives a direct test of a possible shortcut. All 32 faithful characters of the same cyclic quotient have the same kernel. At the permitted split prime 3329 they even give the **same characteristic-zero comparison trace**. Their strict Selmer lengths at 577 and twist 296 are thirty-one zeros and one unit. We checked how the released argument groups these measurements. [Full orbit calculation](fixed-character-577/bounds.py)

## Which label carries the class?

Set $\psi_b(5)=\operatorname{Teich}(5^{9b}\bmod577)$, $\psi_b(-1)=1$ for odd $b=1,3,\ldots,63$. Each character cuts out the real degree-64 cyclotomic field of conductor 256. The mod-577 divisor multiplier at twist 296 is
$$k_b=\sum_{f/2<a<f,\ (a,f)=1}\bar\psi_b(a)^{-1}a^{-297},\qquad f=256\cdot577.$$
In ascending order of $b$ the residues are

```text
508 87 37 444 421 367 54 178 112 372 482 497 476 461 510 76
407 157 414 0 341 31 525 559 432 288 325 303 417 121 506 345
```

Any nonzero multiplier is invertible on the corresponding residual ideal class. The proof of injectivity into the odd ideal class sector applies to each label, since its inertia character at 2 is primitive. Hence each of the 31 labels has zero residual group and zero divisible-coefficient torsion group. At $b=39$ the [explicit class and upper bound](2026-11-24-the-577-class-on-paper.md) give exactly $C_{577}$. Normalizing length over $\mathbb Z_{577}$ gives one. Thus this kernel orbit has total length **one**.

At $p=3329$ we have $p\equiv1\bmod256$ and $p\equiv4\bmod7$. The prime is good and splits in $\mathbb Q(\sqrt{-7})$. Both primes over it have norm 3329. Either Frobenius direction gives the same target for every $b$,
$$1+p^{296}+p^{-296}\equiv384\bmod577.$$
In fact $\psi_b(p)=1$ as an exact root of unity before reduction. Neither the kernel, the one-prime comparison trace, nor the two together determine even the *vanishing* of the strict group. The certified counterexample concerns this specific replacement of the index. [Actual character orbit](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/OrbFacts.lean#L17-L20) · [Complex orbit and its readings](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/FPropGKU.lean#L131-L140)

The split prime **11** has the opposite behavior. Here $\bar\psi_{39}(11)=141$ has order 64 and $11^{296}=496\bmod577$. Its required trace is $1+119+417=537$, since $141\cdot496=119$ and $119^{-1}=417$ in the residue field. All 32 labels give different traces. Indeed $1+y+y^{-1}$ agrees at two arguments only when they are equal or reciprocal. Reciprocity at distinct labels would force $11^{2\cdot296}$ to lie in the order-64 group, whereas its 64th power is 363. Equivalently, solving the trace equation at 537 gives roots 119 and 417. Dividing them by 496 gives 141 and 465, and $465^{64}=213\ne1$. Thus one further measurement recovers the surviving label. It does not by itself identify a global eigenform.

## Does the source make that replacement?

The release transfers the good-datum hypotheses and the local character at the coefficient prime across the orbit. Here every one of those local character components is trivial and all 32 characters meet the hypotheses. It then applies the individual trace theorem **separately for each character**, chooses a separate finite set of representations for each, and sums their individual inequalities. Reindexing by the complex characters is a bijection of labels. No equality of the 32 Selmer lengths is needed in these steps. [Precisely what is transferred](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/GdFacts.lean#L22-L27) · [Individual choices and final reindexing](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/FPropGKU.lean#L146-L172) · [Use in Case I](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/CountI.lean#L52-L69)

We also checked the integer used to bound the traces. Its factors are indexed by the Cartesian product of the orbit labels and the trace catalogue. In the present test they have the form
$$F(b,s)=p^{296}\big(t_s-(1+p^{296}+p^{-296})\big).$$
At this prime $F(b,s)$ is independent of $b$. Consequently the constructed integer is the **32nd power** of $\prod_s F(39,s)$. This inner product is integral and fixed by the complex automorphisms permuting the catalogue, hence is a rational integer. In the valuation comparison the catalogue injection is required separately within each label. Multiplicities across different labels survive. The dataset has exactly the collision that would expose a premature deduplication. The displayed product retains all 32 copies. [Construction of the integer](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/AdmissibleResidues/FrobeniusTraceCountBoundOfRatEigensystemCount.lean#L329-L355) · [Local product comparison](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/AdmissibleResidues/FrobeniusTraceCountBoundOfRatEigensystemCount.lean#L376-L395)

There is a concrete consequence for the construction. If the release supplies its asserted trace bound for the computed positive length, the constructed integer at this prime must be divisible by $577^{32}$. Positive length forces at least one factor of 577, and integral 32nd powers have valuations divisible by 32. The catalogue also allows representations outside the particular marked points. Divisibility alone would therefore leave the origin of the marked witness open.

## What happens when the twist changes?

At $j=296+576u$ the residual character is constant, so the same 31 labels vanish and the $b=39$ group still contains $C_{577}$. At level $577^2$, write $a^{-576}=1+577c_a$. The divisor sum for the surviving label is
$$k(j)=577(287+540u)\pmod{577^2}.$$
Indeed multiply the level-two weights at $j=296$ by $1+577u c_a$ and sum over the upper half of the units. The two integers are independently computed in the [bounds script](fixed-character-577/bounds.py). Thus the exact group is $C_{577}$ whenever $u\not\equiv460\bmod577$. Only $j\equiv265256\bmod(576\cdot577)$ can have higher exponent in this sequence. The mod-577 group stays one-dimensional, so an element of higher exponent would have to lift the same residual line.

## Unresolved

At that exceptional twist the divisor multiplier is zero and gives no upper bound of 577. At the original twist 296 the exact group is known. The proof still needs an admissible rank-three system there, subject to the [two modular exclusions](2026-11-24-the-rank-three-obligation-at-577.md).
