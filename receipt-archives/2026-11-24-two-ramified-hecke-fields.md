# Two ramified quadratic coefficient fields meet in a single residue

**24 November 2026.** In the actual 15,270-dimensional Hecke calculation there are **four distinct characteristic-zero readings of the simultaneous system isolated modulo 5**. They form two conjugate pairs. Their local coefficient fields are $\mathbb Q_5(\sqrt5)$ and $\mathbb Q_5(\sqrt{10})$. The integral algebra identifies the residues of these pairs and nothing further. At the permitted test prime 29 every one of the four trace differences from the release's target has normalized valuation exactly **one half**. This is the least positive valuation in either field. A single one contributes exactly one unit after the proof's factor two, the independently determined length of the [input group](2026-11-24-an-order-five-class-and-a-hundred-missing-levels.md). [The pointwise trace inequality](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/NumberU3US.lean#L49-L59) · [Reproduction and rank certificate](2026-11-24-one-hecke-line-at-571.md)

## Lifting the four-dimensional block

Take the commuting integral operators at both directions over $2,11,23,29$. Over $\mathbb F_5$ their common generalized eigenspace with the prescribed eigenvalues has dimension four. The idempotent for this local factor lifts to the finite Hecke algebra over the complete ring $\mathbb Z_5$. Its image in the integral lattice is a direct summand of rank four. The idempotent is self-adjoint for the mass pairing because the specified residual eigenvalues are preserved on exchanging the two directions. The determinant of the restricted Gram matrix in the computed basis is $2\bmod5$.

The following presentation comes from applying the integer matrices to this block and reducing modulo 5. Put $x=T_{2}-2$, $y=T_{23}-3$ for the chosen directions and $z=x^2$. The four elements $1,x,y,z$ applied to the last basis vector are independent. Their products satisfy
$$x^2=xy=z,\qquad y^2=4z,\qquad xz=yz=0.$$
The adjoint acts by $x^*=-x+3z$, $y^*=-y+4z$ and $z^*=z$. For example, the two matrices at 2 in the replay basis are
$$\begin{pmatrix}2&0&1&0\\0&2&0&3\\0&0&2&1\\0&0&0&2\end{pmatrix},
\qquad
\begin{pmatrix}2&0&4&3\\0&2&0&2\\0&0&2&4\\0&0&0&2\end{pmatrix}.$$
These are matrices on generalized eigenvectors. They retain a distinction which is invisible on the common eigenline.

A lift of the cyclic vector generates the rank-four lattice over the local Hecke algebra by Nakayama’s lemma. An operator killing this vector kills the whole lattice by commutativity. Thus the image algebra acts as its own regular module. Any additional integral Hecke operator commuting with the tested operators acts on this summand through the same ring. Over characteristic zero the operators at the tested primes are commuting normal operators on a positive definite complex space. Their rational algebra is reduced, hence becomes a product of four copies of $\overline{\mathbb Q}_5$ on this summand after extending scalars. There are four distinct eigensystems, each of multiplicity one. Since 2 is invertible, the plus and minus ranks of the adjoint can be read modulo 5. They are two and two. A permutation of four coordinates with minus rank two has two transpositions and no fixed coordinate.

## Determining the fields without rounding eigenvalues

Let $V$ be the entrywise integer lift of the four computed basis vectors, $W$ the integral diagonal mass matrix, $G=V^tWV$, and $e$ the lifted idempotent. In the true basis $eV$, the Gram matrix and the matrix of pairings with $T(eV)$ agree modulo 25 with $G$ and $V^tWTV$. Indeed $(1-e)V$ is divisible by 5 and is orthogonal to the localized space. Both error terms are quadratic in that vector. Thus
$$G^{-1}V^tWTV\bmod25$$
gives the true local Hecke action to this precision. This is why lifting the coordinates $0,1,2,3,4$ as ordinary integers suffices for the following measurements.

Set $D=T_2-T_{\bar 2}$, with the bar indicating the opposite prime ideal above 2. Its characteristic polynomial is $X^4+c_2X^2+c_0$ since the adjoint interchanges the signs. Integer compression gives $c_2\equiv20\bmod25$ and $c_0\equiv75\bmod125$. For the extra digit of the determinant, $D\bmod5$ has rank two, so all its $3\times3$ minors are divisible by five. Changing any matrix entry by 25 changes the determinant by a multiple of 125. Both displayed congruences therefore have certified precision.

The polynomial of the two squared differences divided by five reduces to
$$Y^2+4Y+3=(Y-4)(Y-2)\quad\bmod5.$$
Hensel’s lemma gives two different units $u_1,u_2\in\mathbb Z_5$ reducing to $4,2$. Each of $X^2-5u_i$ is Eisenstein, and the two unit squareclasses differ. The characteristic-zero algebra is therefore exactly $\mathbb Q_5(\sqrt5)\times\mathbb Q_5(\sqrt{10})$. Each directional difference at 2 has valuation $1/2$. The two directions thus distinguish both conjugate pairs at the very first split prime tested.

There is also an exact answer for the integral order $A$. Its invariant part $A^+$ lies in $\mathbb Z_5^2$ with common residue, since the residual Hecke algebra is local with residue $\mathbb F_5$. The elements $1$ and $D^2=(5u_1,5u_2)$ already generate the entire order of pairs with common residue in $\mathbb Z_5^2$. In the anti-invariant part of the normalized ring take generators $\pi_i$ with $\pi_i^2=5u_i$. Multiplication of anti-invariants, evaluated in the one-dimensional space $\mathfrak m^2$ of $A/5A$, has nondegenerate matrix $\left(\begin{smallmatrix}1&1\\1&4\end{smallmatrix}\right)$ in the anti-invariant adjustments of $x,y$. If an anti-invariant has both $\pi_i$ coordinates divisible by five, its product with every anti-invariant belongs to $25\mathbb Z_5^2\subset5A^+$. Nondegeneracy shows its class in $A^-/5A^-$ vanishes. Thus the map of the two-dimensional anti-invariant spaces modulo five into those of the normalization is injective and hence onto. Nakayama gives equality of the anti-invariant lattices. Altogether
$$A=\{(a,b)\in\mathcal O_{\mathbb Q_5(\sqrt5)}\times\mathcal O_{\mathbb Q_5(\sqrt{10})}:\bar a=\bar b\in\mathbb F_5\}.$$
The ramified fields here are completions at 5. This computation does not prescribe the global degrees of the Hecke fields.

## What the source’s trace test actually reads

At a good split prime let $H=T_p$, $H^*=T_{\bar p}$ and $E=p+\psi(p)(p^2+1)$. In these units the geometric trace difference is $(H-E)/p$. The division by $p$ has valuation zero. We measured the following leading coefficients in the two quadratic fields, ordered by $u_i\bmod5=4,2$.

| $p$ | $((H+H^*)/2-E)/5\bmod5$ | $(H-H^*)^2/5\bmod5$ |
| ---: | --- | --- |
| 2 | $(3,1)$ | $(4,2)$ |
| 11 | $(1,2)$ | $(0,0)$ |
| 23 | $(0,4)$ | $(0,2)$ |
| 29 | $(1,3)$ | $(1,3)$ |
| 37 | $(2,2)$ | $(1,0)$ |
| 71 | $(4,0)$ | $(1,0)$ |
| 79 | $(2,2)$ | $(0,0)$ |

To see how the replay assigns the two entries, either invariant numerator $h$ equals $cD^2$ modulo $5A$ for a unique $c\bmod5$. The element $(h-cD^2)/5$ belongs to $A^+$, so its two normalized residues agree. That common residue is one fourth of its regular trace modulo five, obtained from the compression modulo 25. Adding back $c u_i$ gives the table.

At 11 both anti-invariant parts have valuation at least $3/2$ and both invariant differences have valuation exactly 1. All four candidates therefore give valuation 1 against the actual target $133/11$. At 29 the anti-invariant parts have valuation $1/2$ and the invariant parts have valuation at least 1. All four therefore yield $1/2$ against the target $1+29+1/29$. No cancellation of terms with unequal valuations is possible. The [rank-two form](2026-11-24-the-rank-two-alternative-at-571.md) gave valuation zero at 11. These candidates satisfy a genuinely different numerical test. [Full integer and mod-25 replay](hecke-571/packet.py)

## Unresolved

The integral order and these valuations are independent of the RH source. Their interpretation as arithmetic protection for the same global character needs both the [packet and local-type comparison](2026-11-24-matching-the-unitary-level.md) and the [global residual identification](2026-11-24-global-residual-character-at-571.md). Bounds on the total number and sizes of traces as the fields and twists vary are separate obligations.
