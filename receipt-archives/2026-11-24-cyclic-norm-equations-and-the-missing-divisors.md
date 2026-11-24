# Four cyclic norm equations recover the two quadratic forms at 577

**24 November 2026.** For each of the two real inputs in the conductor-256 test, four fixed cyclic equations of degree **577 over the residual field** suffice for all slopes. Each equation has solutions. The positions of the prime factors of those solutions determine the two square coefficients. The mixed coefficient also compares their local values above 577. A change of the common local preimage can change four individual readings there by **403, 29, 261 and 461**. Their sum is $2\cdot577$. The divisors of solutions for the two target inputs remain unknown.

This is a calculation on the branch where a trace cube would test the first two obstruction equations. The release ultimately uses a discrete valuation domain. On this route a counterexample to that use requires unbounded nilpotency indices at one fixed input. [Actual subgroup, traces and downstream use](2026-11-24-two-raw-traces-on-the-released-subgroup.md#a-numerical-milestone-for-the-next-obstruction)

## How the input one can read 183

Set $x=1$ and use the mixed direction $(1,1)$. Initially choose 1 in all four cyclic fields. Every prime valuation vanishes. Now change just the solution in $C_1=F(U_2)$, keeping its norm exactly one.

Choose a place above 577 with $t=1$. On the translated quartic unit the local polynomial is $387(T+1)^4$ and the entire cubic reading vanishes. In particular $U_2$ kills this unit, so it is a local norm from $C_1$. Its degree-one reading is $4\cdot387=394\bmod577$. Choose a global $d\in C_1^\times$ sufficiently close to a local norm preimage there and to 1 at every other place above 577. Such a $d$ exists by weak approximation, since the finite Artin readings are locally constant. This prescribes exactly the character values needed, without specifying the other prime factors of $d$. [The measured units](2026-11-24-four-local-units-at-577.md)

Use $y_1=\sigma_1(d)/d$ and keep $y_2=y_3=y_4=1$. Its norm telescopes to 1. At a split prime away from 577, the signed first moment of the valuations of $y_1$ is the sum of the valuations of $d$ modulo 577. At a nonsplit unramified prime the restricted character has zero Frobenius. Global reciprocity for $U_1+V_1$ on $C_1$ therefore makes the prime-divisor sum **$-394=183\bmod577$**. The local term for the same $d$ is **394**, restoring zero. Replacing $d$ by a power runs the incomplete calculation through all 577 residues while every global norm remains 1. The global element here is specified by an existence construction with prescribed local readings. The numbers follow from reciprocity.

This control falsifies the procedure that keeps only the four cyclic divisor sums in a mixed direction. The published proof uses a different argument. The control identifies exactly what an independent test of its arithmetic must retain.

## Where one preimage exists for every slope

Keep $p=577$, $k=\mathbb F_p$, $F=L_y\mathbb Q(\sqrt{-7})$ and the original twist 296. Let $U_j,V_j$ be the degree-$j$ scalar coefficients of the two globally normalized first-order characters on $G_F$. The joint image is the direct sum of cubics and quartics. At places over $p$ its two local generators are $35(T+t)^3$ in the first summand and $387(T+t)^4$ in the second, for $t\in k$. This choice labels the translation by $+t$. The coefficient of degree $j$ has complement character $\eta z^{j-2}$, with $z$ of order 576. [Global prescriptions](2026-11-24-the-unramified-character-that-local-data-miss.md#four-actual-global-tests) · [Joint image and decomposition groups](2026-11-24-which-norm-tests-see-the-cube.md#the-first-order-fields-and-their-local-groups)

Write $\alpha=(U_2,U_3,V_2,V_3)$, let $C_i/F$ be its four cyclic fields, and let $A$ be their compositum. Then $\Gamma=\operatorname{Gal}(A/F)=k^4$. The first four coordinates of each polynomial together cut out an extension of $A$ unramified everywhere and split at $p$. Indeed at $t\ne0$ the two projected local generators have nonzero entries in disjoint summands. At $t=0$ the cubic survives in $U_3$ and the quartic is zero in degrees zero through three. Away from $p$ the joint extension over $F$ was already unramified. In a mixed direction the determinant of projection to degrees two and three alone is $6\cdot35\cdot387\,ab\,t^2$ for direction $(a,b)$.

Let $x$ represent a weight-$z^{-1}$ real $S$-unit in the [two-dimensional test space](2026-11-24-four-norm-kernels-for-the-two-quadratics.md#the-real-elements-to-test). Every real $S$-unit is an everywhere-local norm from $A$. The local characters at $p$ have odd sign under complex conjugation, the support above 12407809 splits in the joint field, and units are norms at the other unramified places. The obstruction to a global norm is the quotient of $\bigwedge^2\Gamma$ by the local wedges. This identification respects the complement action. Dualizing Tate's canonical character-group description gives the exterior quotient with its original action. [Frei, Loughran and Newton, version 4, Theorem 6.1 and Lemma 6.4](https://arxiv.org/pdf/1508.02518v4#page=34)

In the four mixed wedge coordinates, ordered $U_2V_2,U_2V_3,U_3V_2,U_3V_3$, the local vectors, up to their common nonzero scale, are
$$ (18t^3,\ 12t^2,\ 6t^2,\ 4t). $$
The two pure wedge entries vanish. The three powers of $t$ are independent on $k$. The ambient exterior dimensions at weights $1,z,z^2$ are $1,4,1$, and the respective local ranks are $1,1,1$. The entire three-dimensional norm obstruction has weight **$z$**. The map from real $S$-units to this obstruction factors through their quotient by $p$th powers, since the units are everywhere-local norms and the obstruction has exponent $p$. It therefore kills the $z^{-1}$ test space. This gives an actual $b\in A^\times$ with $N_{A/F}b=x$. The weight restriction matters.

## What the prime factors of a common solution record

For direction $(a,b)$ put $H_j=aU_j+bV_j$ and define four characters, in the same order as $\alpha$, by
$$ \lambda=(aH_1,\ -2aH_0,\ bH_1,\ -2bH_0). $$
Write $\Psi_{a,b}(x)$ for the $A_0$ coordinate of the relaxed Artin product. Its original alternating bracket has $\Omega(e_0,e_3)=-1/8$, $\Omega(e_1,e_2)=1/16$. The preimage of degrees zero and one in the associated central extension is abelian. Apply the product formula to $b$ over $A$ in the compositum with that extension. Transporting a symbol at $g w_0$ back to $w_0$ contributes $-\Omega(g,h)$ if its first-order part is $h$. The low entries of $g$ pair to zero with $h$, whose degree-two and degree-three entries vanish. The quartic coefficient pairs to zero in the $A_0$ coordinate. Multiplication by 16 leaves $H_2(g)H_1(h)-2H_3(g)H_0(h)$. This uses the same orientation as the earlier calculation with the opposite two coefficients. [Original Artin-product proof](2026-11-24-four-norm-kernels-for-the-two-quadratics.md#evaluate-a-rank-four-test-through-a-bicyclic-preimage)

There is no contribution at $p$, where all four low characters split over $A$. At an unramified prime $v$ that does not split in $A$, the residue degree is $p$, which kills all first-order Frobenius values upstairs. At a split prime choose a place $w_0$ of $A$ above $v$. The formula is
$$
16\Psi_{a,b}(x)=
 \sum_{v\nmid p,\ v\ {\rm split\ in}\ A}
 \sum_{i=1}^4 \lambda_i(\operatorname{Frob}_v)
 \sum_{g\in\Gamma}\alpha_i(g)\,v_{g w_0}(b).
$$
The notation $v_w$ means the integer valuation normalized at $w$. At every prime with a nonzero coefficient the unweighted inner valuations sum to $v(x)=0$. The primes in $S$ give zero Frobenius. Changing $w_0$ therefore adds zero. The remaining information is the first moment of a zero-sum divisor.

## Compute the same value in four cyclic fields

For each $C_i$ take **any** global $y_i$ of norm $x$. Use the generator $\sigma_i$ with $\alpha_i(\sigma_i)=1$. For a prime $v$ split in $C_i$, label its places $\sigma_i^j w_0$. Define
$$
W_i(y_i)=\sum_{v\nmid p,\ v\ {\rm split\ in}\ C_i}
 \lambda_i(\operatorname{Frob}_v)\sum_{j=0}^{p-1}j\,v_{\sigma_i^j w_0}(y_i).
$$

At each $v\mid p$ choose **one local** $\beta_v\in(A\otimes F_v)^\times$ of norm $x$. Put $m_{i,v}=N_{A/C_i}\beta_v$, with norms taken on the local algebras. Cyclic Hilbert 90 supplies $c_{i,v}$ with $y_i/m_{i,v}=\sigma_i(c_{i,v})/c_{i,v}$. The answer is
$$
16\Psi_{a,b}(x)=\sum_{i=1}^4 W_i(y_i)
 +\sum_{v\mid p}\sum_{i=1}^4
   \lambda_{i,v}\bigl(\operatorname{rec}_{F_v}N_{C_i\otimes F_v/F_v}c_{i,v}\bigr).
\tag{1}
$$
At the origin every $\lambda_{i,v}$ is zero. Elsewhere above $p$ a completion of $A$ has degree $p^2$. One can put $\beta_v$ in one factor and 1 in the others. To obtain it, start with the available local preimage $y_{U_3}$ and lift once through a cyclic local extension of degree $p$. Local Artin norm functoriality gives this lift because $N y_{U_3}=x$ has trivial symbol in the bicyclic completion.

First use the global $b$ to choose all the local $\beta_v$. For $m_i=N_{A/C_i}b$, the preceding sum over $\Gamma$ is exactly $\sum_iW_i(m_i)$ by grouping places. If $v$ splits in $C_i$ but has residue degree $p$ in $A$, every valuation of $m_i$ there is a multiple of $p$. Write $y_i/m_i=(\sigma_i-1)d_i$ multiplicatively by global Hilbert 90. At split primes the change in the weighted valuation sum is the ordinary sum of the valuations of $d_i$ modulo $p$, including the wrap from $p-1$ to 0. At the other unramified primes the restricted Frobenius is zero. Global reciprocity on $C_i$ moves the resulting sum to $v\mid p$ with the sign in (1). Multiplying a Hilbert 90 solution by an invariant element changes its local norm by a $p$th power.

## Why the local choices agree

At a nonzero $t$ write $u,v'$ for the dual basis of the two normalized local Artin generators. Each $\alpha_i$ is a nonzero multiple of one basis character. Each $\lambda_i$ is a linear combination of both. Changing $\beta_v$ compares two local preimages through an element $d$ of norm one. For one high character $\alpha$ and one low character $\ell$, its local ambiguity, up to simultaneous reversal of the comparison, is
$$ B_d(\alpha,\ell)=\ell(\operatorname{rec}N c),\qquad
  (\sigma_\alpha-1)c=N_{A/C_\alpha}d. $$
It vanishes on $d=(g-1)h$. In that case the signed product of translates solving for $c$ has norm $(N_{A/F}h)^{\alpha(g)}$, and every low character kills this local norm. Consequently one may move each component of $d$ into one chosen completion and multiply there. Two ways to move a component differ by an augmentation element of the same kind. The resulting element in the bicyclic local field has norm one. Scaling $\alpha$ by a nonzero $n\in k$ multiplies the reading by $n$ because $\sigma_{n\alpha}^n$ generates with $\alpha$-value one and a product of $n$ translates changes the norm to its $n$th power.

In that bicyclic field let $\sigma,\tau$ be dual to $u,v'$. Choose $c_\sigma,c_\tau$ with $(\sigma-1)c_\sigma=N_\tau d$ and $(\tau-1)c_\tau=N_\sigma d$. The crossed product with $ST=d\,TS$, $T^p=c_\sigma$, $S^p=c_\tau^{-1}$ has exactly these compatibility equations. Restrict it to the two cyclic degree-$p$ subfields. Its two invariants are $B_d(u,v')/p$ and $-B_d(v',u)/p$. Each restriction multiplies the base invariant by $p$, so the two readings are opposite. The diagonal readings vanish because a cyclic character kills norms from its own field. Conversely a local Brauer class of invariant $1/p^2$ splits over the bicyclic field and gives such a crossed product with a unit off-diagonal reading in $k$. Choosing the sign of the class fixes that reading to one. [Hanke, §2.3, equations (7)](https://www.math.rwth-aachen.de/~Timo.Hanke/thanke_isomorphism-problem.pdf#page=3) · [Milne, Class Field Theory, III §2, equation (29)](https://www.jmilne.org/math/CourseNotes/CFT.pdf#page=114)

It follows that the change in (1) is given by the alternating sum $\sum_i\alpha_i\wedge\lambda_i$ on the local plane, times one scalar. Its two pure square coefficients vanish term by term. In its mixed coefficient the four terms, after removing $35\cdot387\,t^4$, are
$$ 3\cdot4,\quad -2\cdot1,\quad -6\cdot3,\quad 2\cdot4. $$
They sum to zero. With the unit ambiguity just constructed, $a=b=t=1$ gives $403+29+261+461=1154$. Reversing the local change reverses all four signs together. This checks independence from the common local preimage while exhibiting the variation in each individual term.

In particular the square coefficients may be read from arbitrary cyclic solutions using only their prime divisors. For the mixed coefficient one may include the local correction in (1), or move all four solutions into agreement with the chosen local preimages to the precision of the finite characters. To do the latter, approximate the finitely many $c_{i,v}$ in each $C_i$ by a global $c_i$ and replace $y_i$ by $y_i/((\sigma_i-1)c_i)$. The residual comparison has trivial local reading by continuity, and the global norms still equal $x$.

For the two square coefficients the divisor calculation reduces further to ideal classes. For each $i$ use the low character $\ell$ from the same pure polynomial as $\alpha_i$. Above $p$ it is proportional to $\alpha_i$ at nonzero $t$, and vanishes at the origin. Its restriction to $C_i$ therefore defines an everywhere-unramified character split above $p$. Choose a divisor $J_i$ supported above $S$ with norm $\operatorname{div}x$, using splitting at $S$. Then
$$ \operatorname{div}y_i-J_i=(\sigma_i-1)I_i $$
for a fractional divisor $I_i$. Indeed the valuations on each cyclic orbit sum to zero after subtracting $J_i$, and the successive differences span all such integer vectors. The contribution of $\ell$ to the first moment is exactly its Artin reading on $[I_i]\in\operatorname{Cl}(C_i)$. At split primes this follows by shifting the index once. Nonsplit primes outside $p$ have trivial restricted character, the $S$-primes split in the low field, and all $p$-primes have trivial reading. A different solution changes $I_i$ by a principal divisor and an invariant divisor for fixed $J_i$. The character kills both, including full orbits of length $p$. Thus the pure directions require two ordinary ideal-class readings each.

## Reproduce

Run `python -B receipt-archives/boundary-577/cyclic_norm_moments.py` from the repository root with NumPy. The replay checks all 577 local parameters, the complement-weight ranks, the inverse-conjugation signs against the actual three-by-three Lie matrices and the valuation shift at every index. I replayed the calculation on 24 November 2026 with Python 3.12.14 and NumPy 2.3.5 from a fresh copy of its nine source dependencies, including the script. The bounded run completed, and the input hashes agreed before and after. The existence of the norm preimages uses the displayed class-field argument. [Finite replay](boundary-577/cyclic_norm_moments.py)

## Unresolved

For the normalized preimages of $R$ and $R_0$ the polynomials in (1) are respectively $16\cdot442\,h_-(a,b)$ and $16\cdot366\,h_0(a,b)$. The arithmetic still needs representatives upstairs and the divisors of four cyclic solutions for each representative. Their local cyclic compatibility enters only the mixed term. No values for these two quadratics, common root, or failure of the release's domain statement have been obtained. [Target definitions and normalizations](2026-11-24-two-opposite-ideal-class-readings-at-577.md#feed-these-results-into-the-original-test)
