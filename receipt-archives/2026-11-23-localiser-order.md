# Exact order of the released localiser on graph planes

**23 November 2026.** This test uses the polynomial `Rloc` from the higher-rank branch of the release. For every valid frame and every $2\le r<k$, its order at a plane with graph matrix $A$ is exactly the number of nonzero entries of $A$, using the representatives described below. In particular, a single off-diagonal entry produces a competing plane at which the localiser earns **exactly one** power of the uniformizer. The later estimate uses a separate copy of the localiser for each additional power it claims from this factor. [Released polynomial](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SourceCleaning.lean#L97-L112) · [Powered term and off-plane obligation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SourceCleaning.lean#L167-L181) · [Use in the estimate on competing planes](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/WittFrameLocaliserOrders.lean#L1566-L1599)

## The actual polynomial and chart

Use the release's local hypotheses, including $p\ge13$, $n'$ even, and a uniformizer $w$ with $w^2=p$. Write $q=p^{n'}$. At integer frame $j$, put $f_{j\ell}=\mathrm{fr}(j,\ell)$, $z_j=f_{j,r-1}$ and $Q_j=p^{z_{j+1}-z_j}$. The valid-frame conditions order the $r$ even positions in each frame, separate consecutive frames, and translate them by $n'$ after $J$ frames. Over a single period all $rJ$ positions are distinct modulo $n'$. Each $Q_j-1$ is positive, even, and prime to $p$. [Frame hypotheses](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegRing.lean#L46-L58) · [Powers at successive frames](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SourceCleaning.lean#L46-L50)

Take the reference plane to be the first $r$ coordinates. For $A\in M_{r,k-r}(\mathbb F_q)$ take the competing chart with inverse matrix

$$
 \begin{pmatrix}I_r&\widetilde A\\0&I_{k-r}\end{pmatrix},
$$

where the entries of $\widetilde A$ lift those of $A$ to Witt integers. This represents the plane spanned by the rows of $[I_r\ A]$. The polynomial order in the release is the minimum valuation of the coefficients after chart substitution. We use the order at $A=0$ as our reference as well. [Chart, coefficient order and rational plane](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/ObjPol.lean#L327-L356) · [Chart substitution at even positions](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/WittFrameLocaliserOrders.lean#L467-L486)

Write $\Delta_j$ for the minor using the first $r$ columns and $M_{j,ab}$ for the minor that replaces column $a$ by the extra column $r+b$. Indices $a,b$ start at one here. The polynomial is $\Delta_0$ times one factor for every such exchange.

$$
 L_{ab}=\prod_{j=0}^{J-1}\Delta_j^{Q_j-1}
       -\prod_{j=0}^{J-1}M_{j,ab}^{Q_j-1}.
$$

The column order in a minor may supply a sign. Every exponent $Q_j-1$ is even. [Rows, minors and the full product](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SourceCleaning.lean#L88-L107)

## Each entry contributes zero or one

Modulo $w$, the matrix of frame rows is $[B_j\,|\, B_j\sigma^{z_j}(A)]$. Here $\sigma$ is the field Frobenius, and the $\ell$th row of $B_j$ consists of that row's independent variables raised to $p^{z_j-f_{j\ell}}$. Indeed the substitution initially twists the coefficients by $\sigma^{f_{j\ell}}$. Raising the row to the indicated power in characteristic $p$ gives exactly $\sigma^{z_j}$. Each $\det B_j$ is a nonzero polynomial, as is seen by specializing its rows to the coordinate basis. Consequently the reduction of $M_{j,ab}$ is $\pm\det(B_j)\sigma^{z_j}(A_{ab})$. [Polynomial expression in the frame rows](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/WittFrameLocaliserOrders.lean#L559-L568) · [Reduction with the Frobenius positions](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/WittFrameLocaliserOrders.lean#L625-L662)

If $A_{ab}=0$, the reduction of $L_{ab}$ is the nonzero product of powers of $\det B_j$. If $A_{ab}\ne0$, use $(\sigma^{z_j}a)^{Q_j}=\sigma^{z_{j+1}}a$. The product of $(\sigma^{z_j}a)^{Q_j-1}$ telescopes to one since $z_J=z_0+n'$. This proves $w\mid L_{ab}$.

To rule out a second power, fix one frame. At every frame specialize the first $r$ entries of its rows to a permuted coordinate basis, with the last row selecting column $a$. Set all transverse variables to zero except the one for extra column $r+b$ in the last row of the fixed frame, and give it the value $Z$. The distinct frame positions make this a single integral substitution. The exponent on that last row is $p^0=1$. The retained minors are units. Each exchanged minor in the product for $L_{ab}$ has a unit constant because $A_{ab}\ne0$. In the fixed frame it has the form $\pm(u+wZ)$ with $u$ a unit. The linear coefficient in the difference of products is therefore $w$ times a unit. All the other factors are units and $Q_j-1$ is prime to $p$. An integral substitution cannot turn a polynomial divisible by $w^2$ into one with this coefficient. Hence $L_{ab}$ has order exactly one.

The order of a product of integral polynomials is the sum of their orders. Divide out the minimum power from each factor and multiply the nonzero reductions in the residue polynomial ring. This also permits a different testing substitution for each factor. Since $\Delta_0$ has order zero, we obtain

$$
   \operatorname{ord}_w R_{\rm loc}(A)=\#\{(a,b):A_{ab}\ne0\}.
$$

Among the graph planes, exactly $\binom{r(k-r)}{t}(q-1)^t$ of these representatives have order $t$. A bound required at **every** competing plane has to include those with a single nonzero entry.

## A direct scalar check with two rows

Take $p=17$, $r=2$, $k=3$ and $n'=8$. The local ring can be the Witt integers of $\mathbb F_{17^8}$ with $\sqrt{17}$ adjoined. Take $J=1$, $f_{j\ell}=8j+2\ell$, and put the even residues $0,2,4,6$ in the selected set. This satisfies the actual frame definition with $L_1=1$ and $N_1=6$. The two positions strictly between consecutive frames are even, all successive selected positions are two apart, and the second previous even position for each new letter is four away. The two row exponents are $17^2$ and $1$. [Letter, gap and validity tests](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegRing.lean#L23-L58)

For $A=(a,b)^{\mathsf T}$ with integer representatives $0\le a,b<17$, specialize the two rows' retained variables to $(1,1)$ and $(0,1)$, and their transverse variables to $0$ and $1$. Write $Q=17^8$. The retained minor is one. The two exchanged minors after substitution are $b+w-(a+b)^{17^2}$ and $b+w$. The scalar value of the released polynomial is therefore

$$
 [1-(b+w-(a+b)^{17^2})^{Q-1}]\,[1-(b+w)^{Q-1}].
$$

Working modulo $w^4$ suffices to distinguish the orders. Evaluating all 289 choices yields one value of order zero, 32 of order one and 256 of order two. These are the planes with entries in the prime subfield of this example. The proof above covers the full residue field and all valid frames. [Exact scalar check](check_localiser_order.py)

## Unresolved

The source takes $R_{\rm loc}^{c'}$ and uses the off-plane order $c'$ supplied by that factor. The example with one nonzero entry attains this bound for every $c'$. The remaining factors in the actual raw numerator can add further divisibility. The unresolved step is how many independent target directions can be represented after the degree spent on $c'$ copies and on the other factors. [Raw numerator and its factors](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SourceCleaning.lean#L146-L170) · [Matching the prescribed symbol at the selected plane](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SourceCleaning.lean#L275-L286) · [Binary edge interpolation](2026-11-23-edge-separation.md)
