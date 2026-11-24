# A local norm whose witnesses have nonintegral logarithms

**24 November 2026.** For the actual lower target at 577, *every* global solution of the norm equation in the top cubic-character field has a nonintegral $577$-adic logarithm at some place over each of the eight coefficient places of the base field. The field has cyclic degree 577 over the residual field. The word “cubic” refers to the degree of its tangent polynomial. We construct a local norm witness for the lower unit and identify the term that an integral trace calculation would lose.

## The two different ramification breaks

Let $K=F_v$ be a completion of the residual field from the [four cyclic equations](2026-11-24-cyclic-norm-equations-and-the-missing-divisors.md#compute-the-same-value-in-four-cyclic-fields). It has absolute ramification index 72 and residue field $\mathbb F_{577^2}$. Write $U_K^n=1+\mathfrak m_K^n$ and use integer valuations normalized separately in each field. At a nonzero affine parameter, $F(U_2)$ and $F(U_3)$ give the same cyclic local extension, denoted by $C_U/K$. The two quartic coefficients $V_2,V_3$ give $C_V/K$. At the origin only $U_3$ is ramified among the four.

The respective breaks are **37 and 2**. The two ramified characters read 35 and 387 on units of these respective depths. In the logarithm of a base unit the tame inertia weights at depths 1 through 72 are $\omega^{8n}$. The required weights $\omega^{296}$ and $\omega^{16}$ occur only once. Units deeper than 72 are $p$th powers in this base field. This proves the conductor exponents are 38 and 3. Local reciprocity then gives the asserted upper breaks, equal to the lower breaks for cyclic degree $p$. [Measured generators and the tame characters](2026-11-24-four-local-units-at-577.md) · [Serre, *Local Fields*, XV §2, ramification and reciprocity](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Serre-Local.pdf)

For a totally ramified cyclic degree-$p$ extension $C/K$ with break $b$, the different exponent is $D=(p-1)(b+1)$ and
$$ \operatorname{Tr}_{C/K}\mathfrak m_C^k
     =\mathfrak m_K^{\lfloor (k+D)/p\rfloor}. $$
Indeed containment in $\mathfrak m_K^n$ is equivalent by trace duality to $k-pn\ge-D$. For an input whose first nonzero digit is at depth $n$, the sharp norm filtration index is $\psi(n)=n$ up through $b$ and $\psi(n)=b+p(n-b)$ above it, subject at the break to the norm residue condition. In the table both inputs are real and are local norms. The indices give the deepest possible solution.

| Local cyclic field | Different exponent | Lower unit, depth 35 | Diagonal unit, depth 72 |
| --- | ---: | ---: | ---: |
| $C_U$ | 21888 | 35 | 20232 |
| $C_V$ | 1728 | 19043 | 40392 |

For $0<k<b$, expand $N(1+x)$ for $v_C(x)=k$. For $1\le j<p$, the traces of $x^j$ have valuation at least $b$ by the formula above. Newton's identities give the same lower bound on the elementary symmetric terms of orders 1 through $p-1$. The last term $N x$ has valuation exactly $k$. Thus the first digit of $N(1+x)-1$ is at $k$ and is the residue Frobenius on leading coefficients if the downstairs uniformizer is the norm of the upstairs one. Terms from $U_C^{b}$ give norm depth at least $b$. Above the break the trace grade at $\psi(n)$ maps onto grade $n$ and the next grade maps into $\mathfrak m_K^{n+1}$. These are also the norm filtration bounds in Serre's result. [Serre, *Local Fields*, V §§3 and 6](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Serre-Local.pdf)

## Why an integral trace misses the actual lower input

The local lower test unit is $u_-=\exp(Y^{-1}\pi^{280})$, of depth 35 in $K$. It is real, while the first-order cubic character has odd sign, so its local Artin symbol in $C_U$ vanishes. It has norm preimages. Every such preimage $w$ is a principal unit and has $v_{C_U}(w-1)=35$ by the preceding norm calculation. However $v_{C_U}(p)=72p$. In the power series for $\log w$ the unique term of lowest valuation is the one with index $p$. Therefore
$$ v_{C_U}(\log w)=35p-72p=-21349. $$
More generally the same calculation gives $p(d-72)$ at every principal-unit depth $1\le d\le35$. For an index $m p^j$ with $p\nmid m$, the valuation is $mp^j d-j(72p)$. The minimum is unique at $m=1,j=1$. The series still converges. Its trace is $\log Nw$. In contrast, the trace of *every integral element* of $C_U$ lies in $\mathfrak m_K^{37}$, too deep to produce the lower digit.

This applies to an entire genuine global solution as well. The norm of the actual $S$-unit $X_R$ from the real affine field has nonzero lower depth-35 coefficient 488 at each conjugate coefficient place. The sum of the logarithms of its 577 factors has that coefficient. At least one factor has principal logarithm of depth at most 35. The cubic top character $U_3$ is ramified at every affine parameter. If $N_{F(U_3)/F}y=X_R$, remove the Teichmüller factors locally. The norm commutes with this removal, and the base logarithm preserves depths here. Every such $y$ consequently has logarithm of valuation at most $-21349$ at one place over each of the eight base places. This argument allows other local components in $X_R$. It only uses the first depth which survives. [The actual inputs and their support](2026-11-24-the-576-primes-of-the-two-norm-targets.md)

## An explicit norm preimage for the lower unit

Work first in the earlier tame comparison field $T$, of degree 48 over $K$, with $v_T(\pi)=1$ and $v_T(p)=576$. Let $A$ be the normalized upper circular radicand for the cubic tangent, let $s^p=A$, and set $\rho=s-1$ in $C_UT$. In this paragraph $s$ is the upper root. The lower Jacobi root used to construct the affine coordinate is a different element. The integral convention and residue field calculation give
$$ A-1=(211\,\tau_1)\pi^{281}+\text{terms of higher valuation},\qquad
   \tau_1=\sum_{v\bmod1792}\phi_1(v)\bar Y_{1792}^{\,v}. $$
Here and below leading coefficients are read in the residue field. In $C_UT$, $v(\rho)=281$, $N_{C_UT/T}\rho=A-1$, and the break is 296 after the tame base change. This follows also from $(1+\rho)^p=A$ and $\sigma(\rho)-\rho=(\xi-1)s$ for a primitive $p$th root $\xi$. For example choose a uniformizer $\rho^j\pi^k$ with $281j+577k=1$. Its ratio under $\sigma$ has first nonconstant term at depth $577-281=296$. [Upper radicand and compatible local parameters](2026-11-24-four-local-units-at-577.md#compute-the-first-order-numbers)

An explicit first lift is
$$w'=1+[223]\frac{\rho^{155}}{\pi^{75}}.$$
Brackets denote a Teichmüller lift. The added term has depth $281\cdot155-577\cdot75=280$, below the break 296. Its norm supplies the first nonzero digit. In the residue basis $X^{12}=5$ used for the circular sum, $Y=543X^3$ and $\tau_1=430X^3$. The residue coefficients give the following integer identity.
$$ 223(211\cdot430)^{155}\cdot543\cdot5^{39}=1\bmod577. $$
Thus $N w'\equiv u_-\bmod U_T^{281}$. The replay also obtains 223 directly by inverse Frobenius in the full residue field.

Here is an exact correction of the remaining digits. Let $w_1$ be the unique principal $48$th root of $N_{C_UT/C_U}w'$. Then $N_{C_U/K}w_1\equiv u_-\bmod U_K^{36}$ by norm transitivity. Apply the $z^{-1}$, even-sign character projector on principal units to $w_1$, using lifts of the order-144 local complement. The local extension is stable because it is cut out by the pure top character. The norm commutes with that projection. One may use the Teichmüller weights in $\mathbb Z_p$ and continuous powering of principal units. Write $w_2$ for the result. The logarithm downstairs of $u_-/Nw_2$ now has depth at least 107, since the next occurrence of that tame character after 35 is $35+72$. It follows that
$$ w=w_2\exp\!\left(\frac{\log (u_-/Nw_2)}{p}\right),\qquad N_{C_U/K}w=u_- . $$
The last exponential is taken in $K$. Division by $p$ there leaves depth at least 35. This constructs the norm without taking an exponential of the shallow upstairs logarithm.

For the entries above the break there is a shorter formula. In the same tame construction put
$$ q_s=\frac{(1-s^{-1})^{p-1}}p. $$
Its trace to $T$ is one by summing the powers of $s^{-1}$ over the $p$ conjugates. For the cubic root use $i=296$, and for the quartic root use $i=16$ and $v(s-1)=p-i$. The valuation of $q_s$ upstairs over $T$ is $-(p-1)i$. For $u_0=1+p$ in either field, or for $u_-$ in the quartic field, $\exp(q_s\log u)$ converges and has norm $u$. The valuation after dividing by the tame ramification factor eight is exactly the table entry. Taking the $48$th root of the norm back down gives the corresponding solution over $K$. On the cubic lower input the proposed exponent instead has valuation $-1117$ in $C_U$ units of valuation. The explicit nonlinear lift above handles that case.

## Check the ramification boundary in the real directions

One can also lift digit by digit without the circular formula. Choose an upstairs uniformizer $\Pi$ fixed by a lift of complex conjugation, and use $N\Pi$ downstairs. Such a uniformizer exists because the fixed field has residue $\mathbb F_p$ and the quadratic extension back upstairs is unramified. At the break $b$, Newton's identities and trace duality show the norm polynomial on the residue digit is $a^p+ca$. The only intermediate linear term comes from the trace, since traces of powers of order at least two start past $b$. The first digit $\gamma$ of $\sigma(\Pi)/\Pi-1$ is nonzero and in the kernel. Conjugation inverts $\sigma$, so $\gamma^p=-\gamma$. This gives $c=-\gamma^{p-1}=1$. The norm **doubles a real residue digit at the break**. Below the break it leaves a real leading digit unchanged.

At a nonzero affine parameter the joint local field has group $C_p^2$ with upper breaks 2 and 37. Its inverse Herbrand function has slopes $1,p,p^2$. The deepest compatible lift depths for the two real inputs are **19043 and 11672712**. These can be obtained by successively lifting real units in the two cyclic extensions. At a break the real residue map doubles. Above a cyclic break one can use an element $a\Pi^{p-1}/f'(\Pi)$ of trace $a$, where $f$ is the minimal polynomial of $\Pi$. Adding one gives the required norm digit by Newton's identities. Successive lifts converge. At the origin the quartic line projects to zero in the four-field comparison. These local constructions specify the comparison available when normalizing global cyclic solutions.

## What the release counts on this same local field

The local index used by the release can be checked despite the failed integral-logarithm shortcut. The field $C_U$ has absolute degree $2\cdot72\cdot577=83088$. It contains no primitive $p$th root of unity, since 576 does not divide its ramification index 41544. Thus the $p$th-power map is injective on the units. On $U_{C_U}^{73}$ the logarithm and exponential are inverse, since $73>41544/576$. Raising to the $p$th power sends this subgroup onto $U_{C_U}^{41617}$. Its index there is $p^{83088}$. Passing to all units preserves this index because an injective power map gives the same index between the images of two nested groups as between the groups themselves. The valuation factor in $C_U^\times$ supplies another $p$. The result is **$577^{83089}$**.

Substituting the actual residue norm $577^2$, base ramification index 72, extension degree 577 and torsion cardinality one into the released formula gives precisely this answer. Its proof applies a binomial contraction to units congruent to one modulo $p\Pi$ and carries the finite quotient through an index identity. On our field this subgroup has depth at least 41545 for an integral parameter of positive valuation. Our shallow witness is accounted for by the quotient. [Exact local index in the release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/PIdxUnitsFiniteExtensionAdicCompletionStatement.lean#L7-L8) · [Depth of the binomial argument](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SubgroupPowImageUnitsCongruentOneModOfIsAdicComp.lean#L87-L103) · [Passage to the full unit group](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SubgroupPowRelIndexUnitsOfIsAdicComplete.lean#L38-L60)

## Reproduce

Run `python -B receipt-archives/boundary-577/ramified_norm_depths.py` with NumPy. It checks the filtration indices for all depths through 72, the minimum in the logarithm, the actual circular coefficient and the norm of the explicit first lift on its leading grade. The equalities for full local norms use the arguments above. [Replay](boundary-577/ramified_norm_depths.py)

## Unresolved

This excludes imposing an integral-logarithm condition on a norm witness for the actual lower input. The release's norm statement asks for an element with the specified multiplicative norm, and the finite-index assertion under audit concerns traces in a discrete valuation domain. Neither of those two statements imposes this extra condition. The ordinary ideal-class readings for the two target inputs are still missing. [Released norm witness](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/MemPowSub.lean#L58-L67) · [Released trace quantifier](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CurveDVRSpecialization/RatTorsionFree.lean#L29-L32)
