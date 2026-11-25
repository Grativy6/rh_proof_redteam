# One strict class in the entire real dyadic tower at 577

**Corpus and derivation.** This result was developed in Christopher Daniel Pang’s PAL research program with Hearthline. Pang asked us to reconstruct the arithmetic rows of rhOfAll and keep one character fixed while the window changes. Hearthline wrote the mathematical argument. [PAL v2.4-M, Mathematical Realization Atlas](../corpus/PAL_v2.4-M_Mathematical_Realization_Atlas.docx) · [Cluster-Layer Entropy Focus v1.0](../corpus/CLEF_cluster_layer_entropy_focus_v1_0.pdf) · [APCI v1.0.0, Exact Certification Through a Declared Interface](../corpus/APCI_Declared_Interface_v1.0.0.docx)

**Proof inputs and the release.** The release supplies the host, twists and normalized plus-count. This paper computes its pure-character contribution and states which other characters remain outside that computation.

[Proof collection](README.md) · [Dated receipt and supporting checks](../receipt-archives/2026-11-24-one-strict-class-in-the-entire-real-dyadic-tower.md) · [Contribution record](PROVENANCE.md)

**24 November 2026.** Chris Pang asked Hearthline to take the released `rhOfAll` apart and identify which arithmetic pieces the reconstruction must supply. The [two-prime counterexample](../receipt-archives/2026-11-24-two-primes-break-one-window-budget.md) counted one order-577 class repeatedly. We can now give an exact count on an entire part of the same host, including every later dyadic page. The argument uses class groups, local conditions and finite-field arithmetic independently of Lean.

Put $p=577$, $F_m=\mathbb Q(\zeta_{2^{m+2}})^+$ and $A_j=(\mathbb Q_p/\mathbb Z_p)(-j)$. Let $S(K,A_j)$ consist of continuous degree-one Galois cohomology classes unramified away from $p$ and locally zero at every place above $p$. For **every $m\ge6$ and every positive even $j$**, we obtain
$$ S(F_m,A_j)\ \simeq\
\begin{cases}
\mathbb Z/577\mathbb Z,&j\equiv296\pmod{576},\\
0,&\text{otherwise}.
\end{cases} $$
On the surviving line the Galois group of $F_m/\mathbb Q$ acts through the even character of conductor 256 with $\psi(5)\equiv510\bmod577$. For $0\le m<6$ the displayed group is zero at every positive even twist, since the surviving character has conductor 256. This sharpens the [previous lower bound](../receipt-archives/2026-11-24-a-class-inside-the-zeta-windows.md), which followed just that character. [Strict module used in the release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GaloisCohomology/Statement.lean#L54-L78) · [Conductor and finite-field replay](../receipt-archives/fixed-character-577/dyadic_conductors.py) · [The 27 remaining local tests](../receipt-archives/2026-11-24-which-of-the-27-class-group-directions-split.md)

## What this removes from the published count

The actual zeta host is $E_m=F_m(\sqrt{-q},\sqrt{-d})$. Its Galois group is the product of a cyclic group of order $2^m$ and two quadratic groups. For an odd coefficient prime, division by the group order is integral. After adjoining its character values in an unramified coefficient extension, the ordinary character projectors split the cohomology. Restricting to decomposition groups at $p$ and inertia elsewhere commutes with this decomposition by the double-coset form of Shapiro’s lemma. In particular the part fixed by the two quadratic groups is exactly the strict group over $F_m$. [Explicit host](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L19-L25) · [Descent of the local kernels](../receipt-archives/2026-11-24-two-dyadic-pages-behind-one-prime-sum.md#an-arithmetic-distinction-behind-the-same-row)

The release’s plus sign means eigenvalue $(-1)^j$ for complex conjugation. On the part from $F_m$ the eigenvalue is $+1$, so it occurs at even $j$. Equivalently the character sum `h.X` uses $\psi(-1)=(-1)^j$. Over $\mathbb Q$ the corresponding module is $A_j\otimes\psi^{-1}$ with coefficient extension understood. The extra decomposition tests at the primes of the tame level do not lose this class. Away from $p$ the inertia image of a host character has order prime to $p$. Its invariants are zero for nontrivial inertia. At an unramified prime $r$ the Frobenius scalar minus one is nonzero, since it is a root of unity times $r^{-j}$ minus one. It acts surjectively on the divisible coefficient module. An unramified class is therefore locally zero there. [Released plus sign](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean#L64-L76) · [Tame level and character length](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/DirichletPrimeToLPartMulLPowerPart.lean#L104-L120) · [Local subgroups being tested](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/ConjStableShaFam.lean#L92-L97)

For $t\ge1$ and $m\ge6$, the **exact** contribution to the plus sum from $p=577$ and characters factoring through $F_m$ is
$$(\log577)\left\lfloor\frac{t+279}{576}\right\rfloor.$$
Here the twist index runs from 1 through $t-1$. The one character contributing length has values in $\mathbb Z_{577}$. In larger coefficient rings the length is multiplied by the ramification index, which the source divides out. This gives the same answer as the upstairs $\mathbb Z_{577}$-length. [Normalization](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/ShaFamMono.lean#L66-L76) · [Which labels enter](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/DirichletPrimeToLPartMulLPowerPart.lean#L179-L192) · [Use of the total](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/SumOut.lean#L119-L142)

## Which finite calculation can rule out a character?

An even primitive character of conductor $C=2^s$, $s\ge3$, is specified by $\psi(5)$ of order $C/4$ and $\psi(-1)=1$. Bars denote reduction mod $p$, and $\omega$ is the mod-$p$ cyclotomic character. Put $f=Cp$ and $\lambda=\bar\psi\,\omega^{j+1}$. An order-$p$ strict class for $A_j\otimes\psi^{-1}$ has a residual preimage. Over $L=\mathbb Q(\zeta_f)$, Kummer theory puts its radicand in the $\lambda$ component of $L^\times/L^{\times p}$ after scalar extension. Indeed conjugation on the character of a $p$th root is $\omega\lambda^{-1}$. The extension degree $[L:\mathbb Q]$ is prime to $p$, so restriction preserves a nonzero residual class.

Outside $p$ a residual preimage is unramified. The inertia invariants of the divisible module are zero or divisible, so their quotient by $p$ cannot obstruct the lift of this local condition. Its Kummer valuations away from $p$ are multiples of $p$. At $p$ the inertia group on the cyclotomic $p$ factor fixes each prime divisor, and $\omega^{j+1}$ is nontrivial for even $j$. Thus the projected valuations at $p$ vanish mod $p$ as well. Since $\lambda$ is odd, its unit kernel could only come from roots of unity. For a CM unit $u$, $u/\bar u$ is a root of unity by the absolute values of its conjugates. The $p$-power roots here have character $\omega$, different from $\lambda$ on the dyadic inertia. Dividing the principal divisor by $p$ therefore injects this Kummer component into the corresponding minus ideal class group. [Earlier divisor argument](../receipt-archives/2026-11-24-why-the-classes-stop-at-twenty-five.md#a-divisor-identity-at-a-splitting-prime)

Use the carry sum, omitting multiples of $p$ and all even $n$,
$$K(\psi,j)=\sum_{f/2<n<f,\ (n,f)=1}\bar\psi(n)^{-1}n^{-j-1}.$$
The integral group-ring element $\sum_{(n,f)=1}\lfloor2n/f\rfloor\sigma_n^{-1}$ annihilates the cyclotomic ideal classes. At a completely split rational prime this is the divisor of a Jacobi sum, and every ideal class has a representative above such a prime by Chebotarev in the Hilbert class field. Its scalar on the radicand component is $K$. Hence a nonzero $K$ rules out a strict class. For the smaller conductors we also need relative class numbers and the local test when $K=0$. [Divisor and normalization](../receipt-archives/2026-11-24-the-577-class-on-paper.md#the-element-and-its-divisor) · [Small-conductor verification](../receipt-archives/2026-11-24-which-of-the-27-class-group-directions-split.md)

## Why three coefficients suffice at every higher conductor

Let $h=C/256=2^{s-8}$ for $s\ge8$. Write $Z=\bar\psi(5)^{-1}$ and $\xi=Z^h$. The order of $577$ mod $2^{s-2}$ is $h$, since $v_2(577-1)=6$ and squaring increases that valuation by one. Thus $1,Z,\ldots,Z^{h-1}$ form a basis over $\mathbb F_{577}$, and $Z^h=\xi$ for one of the 32 primitive 64th roots in $\mathbb F_{577}$. If even one basis coefficient of $K$ is nonzero, the full sum is nonzero.

For an odd $a$ take the coefficient from the dyadic coset $\{\pm a5^{hk}:0\le k<64\}$ and factor out $\bar\psi(a)^{-1}$. Put $t_k$ equal to the least positive residue of $a5^{hk}$ mod $C$. The remaining coefficient is exactly
$$H_{s,a}(\xi,j)=2\sum_{k=0}^{63}\xi^k
\sum_{\substack{0\le b<577\\ Cb+t_k>Cp/2\\p\nmid Cb+t_k}}(Cb+t_k)^{-j-1}.$$
The factor 2 can be checked before any transform. Pair $n$ with $Cp-n$. The odd power of the residue changes sign, and the sum on one whole residue column mod $C$ is zero in $\mathbb F_{577}$. Its upper-half sum therefore agrees with the upper-half sum on the negative dyadic column.

At $s=13$, $5^{32}=1+31\cdot128\bmod8192$. Squaring shows $5^h\equiv1+31(C/64)\bmod C$ for every $s\ge13$. For $a=1,3,5$ this makes $t_k=a+(C/64)u_k$ with $u_k=31ak\bmod64$ in $[0,63]$. Now $t_k>C/2$ exactly when $u_k\ge32$. It follows that the entire calculation depends on $s$ only through $C\bmod577$, of period **144**. The $j$ dependence has period 576, giving 288 even twist residues. The code evaluates both the original CRT columns and the reduced interval sums on an entire period.

| Test on the $144\cdot32\cdot288$ possibilities | Still zero |
| --- | ---: |
| Coefficient from $a=1$ | 2,274 |
| Both $a=1$ and $a=3$ | 5 |
| All of $a=1,3,5$ | 0 |

The five last cases are listed as $(s\bmod144,b,j,H_{s,5})$, where $\xi=5^{9b}$ in $\mathbb F_{577}$. The values are
$$ (5,27,374,565),\ (22,43,408,67),\ (83,35,468,412),\ (123,5,226,214),\ (133,1,340,572). $$
For $s=9,10,11,12$ the original CRT formula already separates every case with $a=1,3$. Thus **no primitive even character of conductor $512$ or larger contributes**, at any positive even twist. An eventual stabilization theorem for a fixed abelian base gives relevant context. The explicit cutoff, local conditions and coefficient-prime calculation here come from the displayed arithmetic. [Two evaluations of the carry](../receipt-archives/fixed-character-577/dyadic_conductors.py) · [Sinnott on Washington’s class-number theorem](https://www.numdam.org/book-part/AST_1987__147-148__209_0/)

## The remaining 577 sum on one field

Write $\ell_p$ for length over $\mathbb Z_{577}$ and $\chi_q,\chi_d$ for the two quadratic characters restricted to $G_{F_m}$. For a twist ramified at a moving prime, keep the definition of $S$ in absolute Galois cohomology, using trivial restriction to inertia away from 577. The four idempotents of the biquadratic extension over $F_m$ have denominator 4. On positive even twists the plus part retains $1,\chi_q\chi_d$. On positive odd twists it retains $\chi_q,\chi_d$. Consequently the exact unweighted length in the source, for $m\ge6$, is
$$\begin{aligned}
\sum_{1\le j<t}\mathrm{plusLen}_{577}(E_m,j)
={}&\left\lfloor\frac{t+279}{576}\right\rfloor
+\sum_{\substack{1\le j<t\\j\ {\rm even}}}\ell_p S(F_m,A_j\otimes\chi_q\chi_d)\\
&+\sum_{\substack{1\le j<t\\j\ {\rm odd}}}
\bigl(\ell_p S(F_m,A_j\otimes\chi_q)+\ell_p S(F_m,A_j\otimes\chi_d)\bigr).
\end{aligned}$$
This equality of lengths allows infinity. The release separately requires finiteness before converting any length to a natural number. The three sums on the right now specify precisely what remains to be measured with the same $q,d,F_m$.

## Unresolved

The two moving quadratic primes have independent characters $\chi_q,\chi_d$. For even twists the other labels in the plus sum are $\theta\chi_q\chi_d$ with $\theta$ a real-tower character. For odd twists the labels are $\theta\chi_q$ and $\theta\chi_d$. The conductor used in their carry sum includes the moving odd part, so the period argument above supplies no uniform bound for them. The one surviving pure class still requires the release’s [marked rank-three witness](../receipt-archives/2026-11-24-the-rank-three-obligation-at-577.md). The present calculation settles the pure-character count conditional only on the classical inputs and the cited arithmetic certificates. The mixed-character and other coefficient-prime contributions remain open in this audit. [Live Case I demand](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/Counts.lean#L53-L58) · [What a marked point must provide](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/NumberU3US.lean#L49-L59)
