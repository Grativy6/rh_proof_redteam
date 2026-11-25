# The order-seventeen class at conductor 64

**25 November 2026.** Christopher Daniel Pang asked for an arithmetic check that stands independently of the proof under audit. His PAL and APCI method led Hearthline to hold the coefficient prime and the moving host fixed and vary only the auxiliary conductor. The release supplies the Case II input and its three vanishing conditions. Hearthline derived the signed-sum argument, its shorter dyadic cutoff and the two-row test for the other two characters. The class-number and annihilation theorems used below are classical. [PAL atlas](../corpus/PAL_v2.4-M_Mathematical_Realization_Atlas.docx) · [APCI](../corpus/APCI_Declared_Interface_v1.0.0.docx) · [The release’s Bernoulli condition](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/UnramifiedCocycleIsCoboundaryOfBernoulliUnit.lean#L14-L26)

**Result.** Fix the coefficient prime 17, twist 8 and the even quadratic character of conductor 8 in the trivial outer-character zeta family. At auxiliary conductor 64 there is a nonzero unramified class of order 17 that is locally zero at 17. Its character label can be found with a polynomial of degree seven. At conductor 128 and every higher power of two, all six of the tested character directions vanish for every primitive odd label. The release chooses an exponent at least 22 in these windows. Our conductor-64 witness breaks the version with the auxiliary conductor shortened. It does not refute this use in the release.

## Which characters are being tested?

Write $\chi_8(a)=(2/a)$ on odd integers and let $\omega$ be the residual cyclotomic character at 17. The real character $\psi=\chi_8$ occurs once the dyadic host exponent admits conductor 8. For sufficiently late windows the twist range includes $j=8$. The prime-to-17 character in the Case II test has order two and $17-1\mid 2j$. The moving odd primes can stay as chosen in the release. The local test set is $\{17\}$, since $\psi$ has no inertia image of order divisible by 17. The source’s two-adic conductor exponent is 3, its $f_0$ is 1 and its $n_0$ is 4. In the trivial outer-character family the second entry of the maximum defining $n_{\rm II}$ is $2^9\cdot17^3>2^{21}$. Hence $n_{\rm II}\ge22$. [Host characters](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/DirichletPrimeToLPartMulLPowerPart.lean#L174-L192) · [Character components](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/DirichletPrimeToLPartMulLPowerPart.lean#L75-L106) · [Case and conductor](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/DirichletPrimeToLPartMulLPowerPart.lean#L208-L224) · [Actual auxiliary choice](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DataEx.lean#L366-L384)

Let $\xi$ be a primitive odd character of conductor $2^n$. Up to inversion, the three residual coefficient characters are
$$
 \xi,\qquad \chi_{17}\chi_8\xi^{-1},\qquad \chi_{17}\chi_8\xi ,
$$
where $\chi_{17}(a)=(a/17)=\omega(a)^8$. The equalities follow from cancellation of the residual cyclotomic and Teichmüller characters in the first root. For $n\ge4$, multiplication by $\chi_8$ permutes the primitive odd characters of conductor $2^n$. It suffices to test $B_{1,\phi\xi}$ for every primitive odd $\xi$ and $\phi=1$ or $\chi_{17}$. [Root definitions and strict vanishing](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DecompSigmaOrd.lean#L57-L92) · [Same residual characters in the construction](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DataEx.lean#L234-L243) · [Three uses](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/DataEx.lean#L321-L345) · [Downstream tangent directions](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/SymplecticGSp4/NumsZero.lean#L14-L35)

## An exact signed sum, including when 17 divides the conductor

Let $N=2^n$, $n\ge3$, write $f$ for the odd conductor of $\phi$, and assume $\phi\xi$ is odd. For the formulas with a general $\phi$, take the parity of $\xi$ accordingly. Put $\zeta=\xi(5)$, of order $N/4$, and $a_j=5^j\bmod N$ in $[0,N)$. The ordinary Bernoulli sum for a nontrivial odd character gives
$$
 B_{1,\phi\xi}=\frac1{fN}\sum_{x=1}^{fN}x\phi(x)\xi(x)
              =\sum_{j=0}^{N/8-1} C_j\zeta^j,\qquad
 C_j=\sum_{k=0}^{f-1}\operatorname{sgn}\big(2(a_j+kN)-fN\big)\phi(a_j+kN).
$$
For $f=1$, take $\phi=1$. For the identity, group the integers by their residues $\pm5^j\bmod N$. Replacing $x$ by $fN-x$ supplies the minus sign from oddness. Next pair $j$ with $j+N/8$. The character changes sign, and the residue $a_j$ moves by $N/2$. Translation by $fN/2$ modulo $fN$ leaves $\phi(x)$ unchanged and implements exactly that move. Each paired difference contributes the sign in the formula. For $n=3$ the same pairing would use $5^{N/8}=5=1+N/2$, as required. No integer division by 17 is needed in the reduced sum. [Released normalization](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/LemmaX.lean#L32-L46) · [Integer replay](check_seventeen_dyadic_cutoff.py)

## One fewer dyadic layer for the pure character

Let $Q$ be an odd prime power with $4\mid Q-1$, and put $e=v_2(Q-1)$. For $f=1$ the release’s sufficient condition is $n\ge2e$. We obtain the following bound directly from the signs.
$$
 n\ge 2e-1\quad\Longrightarrow\quad B_{1,\xi}\text{ is a unit at }\operatorname{char}\mathbf F_Q
$$
for every odd primitive $\xi$ of conductor $2^n$. Replacing $2e-1$ by $2e-2$ in this universal implication fails at $Q=17$.

Write $S=2^e$, $h=N/S$ and $K=N/(4S)$. In this paragraph $K$ denotes a stride. The case $e=2,n=3$ has the single coefficient $-1$ and is immediate. In the other cases $K$ is a positive integer. The reduction of $\zeta$ still has order $N/4$. Its degree over $\mathbf F_Q$ is $K$, because $v_2(Q^u-1)=e+v_2(u)$ for positive $u$. Thus its minimal polynomial is $X^K-\beta$, where $\beta=\zeta^K$ in the residue field has order $S$. If the whole sum vanished, its coefficient in the residue class $j=0\bmod K$ would vanish. This coefficient is $\sum_{i<S/2} C_{Ki}\beta^i$.

Write $5^K=1+hc\bmod N$ with $c$ odd; the valuation identity $v_2(5^K-1)=2+v_2(K)$ gives this. If $n\ge2e$, $h^2=0\bmod N$. The sign of $a_{Ki}=1+h(ci\bmod S)$ is the sign of the upper or lower half of a cycle of length $S$, traversed with odd step $c$. Put $b=c^{-1}\bmod S$. Extending the sum to the full cycle doubles it, since both the sign and the root power change sign after $S/2$ steps. Reordering the full cycle and summing its first half as a geometric progression gives
$$
 \sum_{i<S/2} C_{Ki}\beta^i=-\frac{2}{1-\beta^b}\ne0 .
$$

At the extra layer $n=2e-1$, with $e\ge3$, $h^2=N/2$ and $h^3=0\bmod N$. The quadratic binomial term flips the previous sign exactly by $(-1)^{\binom i2}$. Its period-four sequence is $1,1,-1,-1$. Set $I=\beta^{S/4}$, $A=(1-I)/2$, $B=(1+I)/2$. This sequence equals $A I^i+B(-I)^i$. The two shifted frequencies $\beta I$ and $-\beta I$ are primitive of order $S$. The same half-cycle sum, at these two frequencies, now gives
$$
 -2\left(\frac{A}{1-\lambda}+\frac{B}{1+\lambda}\right)
       =-2\,\frac{1-I\lambda}{1-\lambda^2},\qquad \lambda=(\beta I)^b .
$$
The denominator is nonzero and $\lambda$ has order at least 8, while $I^{-1}$ has order 4. This proves the extra layer. Washington’s work on class numbers in cyclotomic towers provides historical context. We claim an independent derivation for this audit without asserting literature priority. [Washington, 1978](https://doi.org/10.1007/BF01399512)

## All higher layers for the character at 17

For $\phi=\chi_{17}$, put $S=16$ and fix $n\ge8$. Take $j=0,1$, with $a=5^j\in\{1,5\}$, smaller than $h=2^{n-4}$. In the residue class $j\bmod K$, the linear shift gives $a_{j+Ki}=a+h(ac i\bmod 16)$. Put $\gamma=\beta^{(ac)^{-1}\bmod16}$. Summing a full signed cycle and inserting the formula for $C$ gives
$$
 \sum_{i<8} C_{j+Ki}\beta^i
 =-\frac{2}{1-\gamma^{17}}
       \sum_{b=0}^{16}(a+hb)^8\gamma^b \quad\text{in }\mathbf F_{17}.
$$
To verify this reduction, write each argument as $a+hu$ with $0\le u<17\cdot16$. The sign changes at $u=17\cdot8$. Translation by this half-period preserves $\chi_{17}$ and negates the frequency. The lower half consists of eight complete blocks of length 17. Their phases form a geometric progression with ratio $\gamma^{17}$. Finally $\chi_{17}(v)\equiv v^8\bmod17$, including $v=0$.

The possible $h\bmod17$ form $\langle2\rangle$, of order eight. For each value there are eight primitive frequencies. Denote by $\gamma_0$ the frequency for $a=1$. For $a=5$ it becomes $\gamma_0^{13}$ since $5^{-1}=13\bmod16$. Of the 64 cases, the table lists every zero of the first short sum and the corresponding value of the second.

| $h\bmod17$ | $\gamma_0$ | Second short sum modulo 17 |
| ---: | ---: | ---: |
| 2 | 5 | 1 |
| 2 | 7 | 11 |
| 9 | 6 | 4 |
| 9 | 7 | 3 |
| 16 | 3 | 7 |
| 16 | 5 | 11 |

Thus at least one coefficient of the reduced polynomial is nonzero at every layer $n\ge8$. At $n=7$ the eight primitive values of $\beta$ in increasing order are $3,5,6,7,10,11,12,14$. The even and odd coefficient sums from the signed formula are respectively the pairs
$$
 (0,12),(15,12),(9,11),(3,2),(1,9),(8,1),(0,5),(14,16).
$$
None is $(0,0)$. Together with the pure-character result this proves the unit assertion for the full six-direction test for every $n\ge7$. The [standard-library calculation](check_seventeen_dyadic_cutoff.py) replays the finite table and compares the row formula against the original integer sums. The finite table covers all larger $n$ by the two congruences just derived.

## The missing class at conductor 64

At $n=6$ the pure signed polynomial is
$$
 P(X)=X^7-X^6+X^5+X^4+X^3-X^2-X-1 .
$$
Of the eight primitive sixteenth roots in $\mathbf F_{17}$ only 11 is a root of $P$. Its integral norm is $2176=2^7\cdot17$. For a hand check, successively multiply by the conjugate obtained by negating the primitive root. In the next power bases the three results are $2Y^3+2Y^2+6Y-2$, $24-40Z$ and $2176$. For $\phi=\chi_{17}$ all eight evaluations at conductor $17\cdot64$ are nonzero.

The zero gives a genuine arithmetic class. Let $E=\mathbf Q(\mu_{64})$ and $M=E^{\{1,31\}}$. It is the cyclic degree-16 CM field cut out by any of these primitive odd characters. Its odd characters are exactly the eight primitive ones above. The abelian relative class number formula and the computed norm give a minus class group of order exactly 17 at the prime 17. In this statement only the 17-part is taken; the Hasse unit index, roots of unity and the powers of 2 in the formula are all prime to 17. [Relative class number formula, Hirabayashi](https://cm.osu.cz/sites/default/files/contents/22-2/cm022-2014-2_133-140.pdf)

Write $\sigma_5(\zeta_{64})=\zeta_{64}^5$. Its eigenvalue on that line of the class group is **14**, the inverse of 11 modulo 17. To see which direction occurs, apply Stickelberger’s annihilation theorem in $E$. Extension of ideals from $M$ is injective on the 17-part because the degree is two. The Stickelberger element uses $\sigma_a^{-1}$, so on the class-group direction with character $\kappa$ its eigenvalue is $B_{1,\kappa^{-1}}$. The integral annihilator $(65-\sigma_{65})\Theta_{64}=64\Theta_{64}$ has multiplier 64, invertible modulo 17. The unique vanishing evaluation then gives $\kappa(5)^{-1}=11$. [Stickelberger’s theorem and conventions](https://dept.math.lsa.umich.edu/~kartikp/teaching/678-Fall2009/L9.pdf)

The resulting unramified additive class on $G_M$ extends to a twisted cocycle on $G_{\mathbf Q}$ because 16 is invertible in $\mathbf F_{17}$. It splits locally at 17. Indeed $17\equiv5^{12}\bmod64$ and $14^{12}\equiv4\bmod17$. The Frobenius ideal class at a prime of $M$ over 17 is fixed by its decomposition group, while the element corresponding to 17 acts on the detected direction by 4. Its value there must be zero. The residual local cocycle over $\mathbf Q_{17}$ then factors through a group of order prime to 17, so is a coboundary by averaging. Thus this is a nonzero class that passes the local splitting and unramifiedness tests when the pure auxiliary coefficient is shortened to the bad label. The public bound and the smaller uniform cutoff 128 both exclude it. Six of the eight primitive labels at 64 still have both pure inverse tests nonzero as Bernoulli values. A single bad label does not make every possible auxiliary choice fail.

The same classical annihilation theorem proves the positive conclusion for the actual coefficients. For any of the six characters let $E$ now be the cyclotomic field of its primitive conductor $f2^n$, $f=1$ or $17$. Its degree is prime to 17. A cocycle satisfying the source’s strict local conditions gives an unramified homomorphism on $G_E$. Away from 17 the residual diagonal representation has image of order prime to 17, so vanishing on inertia in its kernel forces vanishing on the remaining inertia in $G_E$. At 17 use the given local coboundary. Choose a positive integer $b\equiv1\bmod2^n$, $b\equiv2\bmod17$. One has $\kappa(b)=1$ for all six characters since $(2/17)=1$. The integral Stickelberger annihilator $(b-\sigma_b)\Theta_{f2^n}$ acts on the target character by $(b-\kappa(b))B_{1,\kappa^{-1}}$, a unit at 17 by the preceding calculation. This excludes any nonzero equivariant class-group homomorphism. The remaining cocycle factors through the prime-to-17 Galois group and is a coboundary. This independently verifies the three vanishing conditions and their inverses on the stated late-window family. The release uses a general shift argument with its larger bound. [Published reduction to vanishing](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/ChrInvNeg.lean#L197-L209) · [General finite-field step](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/LxCore.lean#L65-L76) · [Application to the symplectic input](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LevelCohomology/HcXvan.lean#L19-L36)

An optional PARI/GP replay computes the field and the class-group action directly. A prime above 31 has nonzero class, its image under $\sigma_5$ is 14 times that class, and the four primes above 17 all have zero class. The command `bnfcertify` certifies the class-group computation.

```gp
F = factor(polresultant(polcyclo(64,y), y^2-x*y-1, y))[1,1];
B = bnfinit(F,1);
print([B.cyc, bnfcertify(B)]);
P = idealprimedec(B,31)[1];
a = Mod(x^5+5*x^3+5*x,F);
v = bnfisprincipal(B,P,0)[1];
w = bnfisprincipal(B,nfgaloisapply(B,a,P),0)[1];
print(lift(Mod(w/v,17)));
print([[q.e,q.f,bnfisprincipal(B,q,0)] | q <- idealprimedec(B,17)]);
```

Here $x$ represents $\zeta_{64}-\zeta_{64}^{-1}$, fixed by $\sigma_{31}$. The automorphism polynomial is the identity $\zeta^5-\zeta^{-5}=x^5+5x^3+5x$. The symbolic proof, finite arithmetic and class-field computation have separate inputs. None establishes a failure at the conductor chosen by the release.
