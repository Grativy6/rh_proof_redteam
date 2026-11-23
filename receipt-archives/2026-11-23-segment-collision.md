# A collision at the stated degree and numerical scale

**23 November 2026.** At one fixed instance satisfying the hypotheses of the release's local rank estimate, at least $17^{600}+1$ distinct input polynomials produce the *same nonzero generator*. They have the same degree at every input letter, the same degree at every output slot and the same label. Thus counting their descriptions as independent vectors would give a false rank even at the stated numerical scale. We traced the counted subspace to a stricter set of exponents with a unique division-with-remainder rule. [Rank estimate and numerical hypotheses](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/ValuationLowestDegreeRename.lean#L18-L53) · [Substitution, label and fixed-degree generator](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegRing.lean#L93-L106)

## Fix all the parameters

Put $p=17$, $g=100$, $n'=4g$, $r=2$, $k=10^9$ and $K=k-r$. Take $W$ to be the integers of the unramified extension of $\mathbb Q_p$ of degree $n'$. For $O$ adjoin $w=\sqrt p$ to the integers of the unramified extension of degree $2n'$. Its residue field has $p^{2n'}$ elements and every rational integer unit has a square root in $O$. Use one frame per period, with entries $4gj$ and $4gj+g$ at step $j$. The selected residues are $0,g,2g,3g$. Take $L_1=g-1$ and $N_1=N_s=6$. The six letters in frame zero are
$$u_j=(j-4)g,\qquad j=0,\ldots,5.$$
The first two are old, and the last four are new. All are even. The two selected positions strictly between consecutive frames and every successive selected gap meet the frame tests. The second previous even letter for $u_j$ is $u_{j-2}$ for $2\le j\le5$. [Actual frame tests](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegRing.lean#L23-L58)

Set $a=2p^{12g}$, take degree $a$ at each selected residue, and set $E'=E_0=m_*=0$, $Q=p^{5g}$, $Y=64k$, $C_{\rm La}=C_k=1088$. Each substitution exponent is $T_j=p^{g-u_j}$, so $Q=T_0$ is the largest. The three size inequalities reduce to
$$
 1088\cdot 36\log a\le k,\qquad
 128k^2\cdot 6Y^2\le p^{g-2},\qquad
 32pYk^2\cdot 6Q^2\le a.
$$
The first follows from $\log17<3$ and $\log 2<1$. The others are integer comparisons. Also $N_s\le2|TT|$ and $N_s+r\le K$. At the released value $C_{\rm rk}=1$, the rank prefactor $1-|TT|r^2k/Y$ equals $3/4$. This gives a positive lower bound. The example instantiates the universal local theorem. We have not identified this choice of parameters with a point of the final global family. [Every scale hypothesis](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegmentDegree/NonemptyDvrSettingOfStandard.lean#L31-L47) · [Constants used to obtain the estimate](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegmentDegree.lean#L21-L36)

## Meet the source conditions before identifying the variables

Use only the first two, plane coordinates of the variables, writing $X_{j,c}$ at occurrence $u_j$. For $i=2,\ldots,5$ put $B_i=a/(2T_{i-2})$, an integer, and take the common polynomial
$$
 P=\prod_{i=2}^5
 \det\begin{pmatrix}X_{i-2,1}&X_{i-2,2}\\X_{i-1,1}&X_{i-1,2}\end{pmatrix}^{B_i}.
$$

In `XX'` choose the normal factor $1$ and the intermediate bounds $M(x)=0$. For the prefix preceding $u_i$, both rows of its indicated determinant undergo the same rank-one torus substitution, a conjugate of $\operatorname{diag}(z,1)$. The determinant acquires the factor $z$. Every other included variable is of vector type and contributes only nonnegative Laurent powers. The prefix valuation is thus at least $B_i$. This meets the threshold $\mathrm{Bo}/2=B_i$ and the margin $\lfloor\mathrm{Bo}/(k^2Y)\rfloor$. Every normal degree is zero. Multiplying by monomials in the indicated plane variables preserves all these inequalities. [Torus substitution and valuation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/ObjPol.lean#L84-L110) · [The two factor conditions and degree cut](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegRing.lean#L76-L91)

Under the power substitution, each determinant is nonzero. Its two rows have different residues, so its two terms remain distinct. At each of the four true slots the image of $P$ has degree $a/2+a/(2p^g)$. Indeed a first row contributes $a/2$, while a second row contributes $a/(2p^g)$, with each contribution occurring once per residue.

Write $q=p^{4g}$ and $M=p^{6g}$. For each $0\le h\le M$ multiply $P$ by
$$
 X_{0,1}^h X_{0,2}^{M-h}
 X_{4,1}^{q(M-h)}X_{4,2}^{qh}.
$$
The old letter $u_0$ and the new letter $u_4$ both have residue zero. Their powers satisfy $T_0=qT_4$. Each multiplier therefore has the same image, of degree $MT_0$ in **each** of the two output coordinates at residue zero. Even the two input occurrence degrees, $M$ and $qM$, are fixed as $h$ varies.

Fill the remaining degree at each slot by putting powers of the first plane coordinate at its unique new occurrence. The amounts to fill in output degree are $p^{12g}-3p^{11g}$ at zero and $p^{12g}-p^{11g}$ at the other three slots. Each amount is positive and divisible by the substitution exponent at that occurrence. This is common padding for all $h$. Take the external label to be zero and the unused segment polynomials to be zero. All the proposals now meet the original degree $a$, the support conditions, and the same source bounds. They are linearly independent as input polynomials, since they are distinct monomials times a common nonzero factor. Their image has rank one. [Exact integer and frame check](check_segment_collision.py)

## What the rank proof counts

At a frame position, the same letter can enter the counted monomial once as a new occurrence and once as an old occurrence of the next frame. For a plane coordinate the total exponent takes the form
$$
 \ell+P_j(v)\bigl(d_{\rm new}+Q^c_jd_{\rm old}\bigr).
$$
Here $\ell<P_j(v)$ and $d_{\rm new}<Q^c_j$. Both strict bounds appear in the counted family's definition. Taking remainders first modulo $P_j(v)$ and then modulo $Q^c_j$ recovers the label and both contributions. An old occurrence has no normal variables. The normal factor is supported only on new letters. A top outside the frame has just one new occurrence per period. [Coarse exponents and their strict cut](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegmentDegree/Coarse.lean#L43-L55) · [The counted subspace](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegmentDegree/Coarse.lean#L74-L86) · [Which positions recur](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegmentDegree/LamMZero.lean#L59-L67) · [Decoding all coordinates](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegmentDegree/LamImgApply.lean#L126-L153)

These ratios can be checked without approximation. With $z_j$ the last position of frame $j$, $b_{j-1}$ the first position of its predecessor and $L=\lfloor\log_p\lfloor a/(8Yk^2N_s)\rfloor\rfloor$ at the stated scale, the source's integer logarithm gives $R_j=\max(0,L-z_j+b_{j-1})$. Thus $z_j+R_j=\max(z_j,L+b_{j-1})$. Both sequences inside this maximum increase strictly, and after a period both advance by $n'$. Consequently $Q^c_j=p^{z_{j+1}+R_{j+1}-z_j-R_j}$ and the product over a period is exactly $p^{n'}$. Allowing $d_{\rm new}=Q^c_j$ would already hide one whole old digit. [Integer logarithm and consecutive scales](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegmentDegree/LamMZero.lean#L179-L210) · [Ratios over a full period](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegmentDegree/FrameZeroStrictMono.lean#L47-L89)

The proof transfers this restricted family to the original generator space by multiplication by one common polynomial with nonzero reduction. It selects a basis from the images modulo the uniformizer. At the live count, the local factors also have to be saturated in their ambient coefficient lattices. [Injection into the actual image](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegmentDegree/Coarse.lean#L128-L158) · [Choice from reductions](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegmentDegree/SelIsComplRestrictSupport.lean#L106-L124) · [Why reduction must retain the local rank](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SegmentDegree/LamSatRestrict.lean#L42-L73)

## Unresolved

The equality of these generator images is exact. The counted family has a stricter digit condition, which prevents this collision from inflating its rank. The remaining test concerns the integral saturation of the polynomial spaces defined by several prefix conditions. Passing each condition separately can still lose a power of the prime when their subspaces are combined. [Product-rank test and the selected leading labels](2026-11-23-minor-product-rank.md) · [Public audit key](../RH-PROOF-WORK-KEY.md)
