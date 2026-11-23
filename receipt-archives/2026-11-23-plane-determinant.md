# When every integral test on the exact line misses the plane bound

**23 November 2026.** We fixed a signed chain, its cutoffs and a vector spanning the exact source line, then varied only the unit weights in its pairing. Even with positive normalized factorial weights, **every integral test on that line can miss the promised valuation bound by arbitrarily many powers of a fixed prime**. The permitted remainder cannot rescue it. An integral test that loses one unit of determinant weight does meet the published bound. This example tests the restricted plane-pairing statement, including a case where its relaxed weight cutoff exceeds six billion. [Source, permitted tests, remainder and claimed valuation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/Lemma5aAt.lean#L278-L311) · [Use of this estimate on the chosen arithmetic vector](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/DualFockLinear/RestXiPOfNS.lean#L34-L45)

## The factorial weights can cancel to any prescribed precision

Take $r=p\ge5$. For a first row with $r$ coordinates, fix $P=p^h$ and low digits $0\le a_i<P$. On a monomial using coordinate $i$ once, the release's factorial weight is
$$
 u_i=U_h(a_i)=\binom{p^h+a_i}{a_i}
     =\prod_{j=1}^{a_i}(1+p^h/j).
$$
Unused coordinates contribute one. Each $u_i$ is a positive integer congruent to one modulo $p$. For any $L\ge1$ there are digits at depth $L-1$ for which $\sum_i u_i=0\bmod p^L$. [Actual factorial ratio and its product over plane coordinates](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/DiagonalSupport/PickDefs.lean#L11-L29)

Start at depth zero with $p$ copies of digit zero. Their weights sum to $p$. On passing from depth $h-1$ to depth $h$, extend a digit $a$ to $pa+d$ with $d=0$ or $1$. The factors with $p\mid j$ reproduce $U_{h-1}(a)$. The other factors, multiplied modulo $p^{h+1}$, contribute $1+p^h d$. The reciprocals of the nonzero residues sum to zero modulo $p$ in each complete block. Consequently extending one digit with $d=1$ increments the sum by $p^h$ modulo $p^{h+1}$. Extending any number from zero through $p-1$ of the digits this way gives every possible next digit of the sum. Induction proves the claim.

To check the signed-chain unit hypothesis independently on the full domain, use
$$
 \gamma(\alpha)=\prod_{i=1}^r \bigl(1+(u_i-1)\alpha_{1i}\bigr).
$$
Both this function and its reciprocal are integral units. Modulo $p^k$ their expansions need only total degree $<k$, since each factor increment is divisible by $p$. Ordinary integer monomials have integral expansions in the binomial basis. This meets the source's $6k$ allowance. On **every monomial of the prescribed degrees** the first-row exponents are zero or one with sum one, so this function agrees with the normalized factorial weights above, taking trivial factorial factors on the padding variables. The extension gives an explicit witness away from those degrees. We have not identified these digit choices with one selected global frame. [Full unit and approximation hypotheses](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/Lemma5aAt.lean#L183-L204)

## Restrict the space while keeping the theorem's hypotheses

Use the integers $O$ of an unramified quadratic extension of $\mathbb Q_p$ with $w=\sqrt p$ adjoined, and normalize $v_p(p)=1$. Use one segment with $2r$ vector letters, the rows of two generic $r\times r$ matrices $X,Z$. Give their rows degrees $1$ and $b=p^h$ respectively. Here $h$ fixes the padding degree and is independent of the factorial digit depth. Give all frame labels degree zero and set the chain's power exponents to zero. The two strictly nested chain sets include all frame labels, first with the $X$ rows and then with every row. Use thresholds $1,b+1$ respectively and set all link thresholds to $b+1$. Use the release constants $CH=26$, $CE=2$, $C_6=24$, $C_{18}=60$. [Local field hypothesis](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/Lemma5aAt.lean#L19-L20) · [Digit parts, chain sets and links](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/Lemma5aAt.lean#L230-L259) · [Constants actually supplied](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments.lean#L14-L26)

Put $D_m=\mathrm{Dm}$, $D_l=\mathrm{Dl}$, $\kappa=\mathrm{kp}$ and $n_0=r\,v_p(b!)/2$. In this instance $D_m+D_l=(r+1)e_P$. The source formulas give $e_P\le r^2(h+3)$ and $\kappa\le r^2(h+7)$. Set
$$
 B=r^2\big[(r+1)(h+3)+3(h+7)\big],\qquad c=4B+1,
$$
and give both chain positions slack $r^2(b+1)+26rc$. All link thresholds are positive. The slack and the strict condition $c>4(D_m+D_l+3\kappa)$ follow directly. For $p=r=17,h=8$, we get $b=6{,}975{,}757{,}441$, $B=70{,}227$ and $c=280{,}909$. The relaxed link cutoff is still $6{,}958{,}902{,}902$. [Valuation and logarithmic constants](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/ObjPol.lean#L61-L68) · [Numerical hypotheses](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/Lemma5aAt.lean#L264-L280)

Write $A=\det X$ and $E=(\det Z)^b$. The exact source at these degrees is the line spanned by $AE$. Indeed the digit part at zero is the original polynomial with renamed letters, and every other digit part vanishes. The first threshold requires a polynomial of degree $r$ in $X$ to have minimum coordinate weight at least one in every basis. The second requires minimum weight at least $b+1$ on the total degree $r(b+1)$. In each case the sum of the coordinate weights forces equality in all coordinates. In every basis the corresponding diagonal torus therefore acts by the determinant character to the indicated power. Conjugates of the diagonal torus generate $GL_r$ in characteristic zero, as can be checked on elementary shears. Thus the polynomial has character $\det$ in $X$ and $\det^b$ independently in $Z$. Its value on pairs of invertible matrices is a scalar times $AE$, which determines the polynomial. The link tests hold because they also see all the active rows. [Valuation by a generic change of basis](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/ObjPol.lean#L84-L110) · [Exact and relaxed weights](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/Lemma5aAt.lean#L282-L294)

## The failed bound and an allowed witness

Let $e=v_{\rm BB}(E)$ and take $F=w^{-2e}AE$. The exponent $2e$ is integral. The determinant $A$ has coefficients $\pm1$ on distinct multilinear monomials, so $v_{\rm BB}(F)=0$. Under the twist each permutation monomial of $A$ acquires the weight $u_i$ of the column used in its first row. Each column occurs in $(r-1)!$ permutations. With $K_b=\langle E,E\rangle_{\rm Fock}$ this gives
$$
 B_{\gamma}(F,AE)=w^{-2e}K_b(r-1)!\sum_i u_i .
$$

The Fock norm is $K_b=\prod_{j=0}^{r-1}(b+j)!/j!$. For a short verification, the determinant differential operator applied to $(\det Z)^b$ is a relative invariant proportional to $(\det Z)^{b-1}$. At $Z=I$, the term for a permutation $\sigma$ contributes $b^{\#\text{cycles}(\sigma)}$ including its derivative sign. In the expansion of $\det(I+Y)^b$ each cycle can be put into any of the $b$ factors. Summing by insertion of the last element gives $b(b+1)\cdots(b+r-1)$. Iterating gives the norm. Since $r=p$, $p\mid b$ and $0\le j<p$, every $\binom{b+j}{j}$ is a $p$-adic unit. Hence $v_p(K_b)=2n_0$. [Cayley determinant identity](https://arxiv.org/abs/1105.6270)

Also $n_0-\kappa/2\le e\le n_0$. The diagonal monomial gives the upper bound. For the lower bound, in a row of degree $d$ the multinomial valuation is a sum of base-$p$ carries, at most $(r-1)\lfloor\log_p d\rfloor$ for $d\ge1$, and zero for $d=0$. Summing over rows bounds the factorial loss by $\kappa$. This reasoning applies to the entire prescribed multidegree.

Take digit precision $L>B$. Every integral test on the exact line has scalar in $O$, since $AE$ has a unit coefficient. Its pairing has valuation at least $2n_0-e+L>n_0+B$. The release's upper bound is $n_0+D_m+D_l+3\kappa\le n_0+B$. Adding a permitted remainder cannot change this conclusion. The degree conditions exclude model variables mapping to positive frame degrees. The coefficients of that remainder have valuation at least $c-D_m-D_l-2\kappa$. The factorial estimate and $v_{\rm BB}(F)=0$ give pairing valuation at least $c-D_m-D_l-2\kappa+n_0-\kappa/2>n_0+B$. Thus a test constrained to the exact line fails even with the full remainder allowance. [Both bounds and the remainder](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/Lemma5aAt.lean#L298-L309)

Now take $H=x_{11}\partial A/\partial x_{11}$ and use the model test $G=HE$, $R=0$. Exactly the permutations using cell $(1,1)$ survive, so
$$
 B_{\gamma}(F,\mathrm{ph}(G))=w^{-2e}K_b(r-1)!\,u_1 .
$$
Its valuation is $2n_0-e\le n_0+\kappa/2$, within the bound. The test is integral, has all the required degrees, and $v_{\rm BB}(\mathrm{ph}(G))=e\ge n_0-\kappa$. Its first prefix weight is at least zero. Its full and link weights are at least $b$, from $E$. Each is within one unit of the exact threshold and therefore satisfies the published restrictions. The relaxed target is genuinely restrictive in the numerical example. A monomial using only one matrix column has full minimum weight zero and fails the positive link cutoff.

## Reproduce

Run `python receipt-archives/check_plane_determinant.py`. It constructs the low digits, checks factorial congruences and a unit cofactor pairing at $p=5,17$, compares small determinant norms by coefficient expansion, and verifies the large numerical cutoff. The induction covers all digit precisions. [Exact checker](check_plane_determinant.py)

## Unresolved

This example rules out a uniform estimate using the exact line itself. The weaker test space in the release detects the same vector within its budget. The example has zero frame-label degrees, so the model-to-true substitution acts identically on its active letters. The next pressure point is that substitution with nonzero frame degrees, where low digits, powers and an additional copy of a letter can produce the same exponent. [Substitution and digit splitting](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/Lemma5aAt.lean#L221-L244) · [Lifting the test through that map](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L409-L426) · [Earlier corrected trace test](2026-11-23-corrected-trace-test.md)
