# The two directions at the split prime 2 really differ

**24 November 2026.** On a definite unitary group over $\mathbb Q(\sqrt{-7})$, we computed the space with the local character suggested by the [rank-three test](2026-11-24-which-rank-three-representations-remain.md). It has dimension **15,270**. A single function supported on a specified orbit gives values **1 and 0** for the two conjugate Hecke operators at 2. Their difference is one over the integers and remains nonzero modulo 5. This tests whether this comparison space could have entirely real split-prime traces. Matching its level at 7 and its global packet to the point required by the release is a further mathematical obligation. [Exact group, orbit and Hecke calculation](check_unitary_level_571.py)

## Which character belongs on the level

Use the standard definite three-variable unitary group over $K=\mathbb Q(\sqrt{-7})$ and its integral maximal compact as in Loeffler's Section 3. At the split rational prime $q=571$, replace the maximal compact by the preimage of the line stabilizer $P\subset\mathrm{GL}_3(\mathbb F_q)$. Use the quadratic character of the determinant on the **two-dimensional quotient by the line**. The two equal ramified inertia factors in the original GL(3) test are quadratic and the other factor is trivial. Group the two equal factors on the two-dimensional block. We keep the trivial archimedean coefficient system and the paper's maximal level everywhere else, including its ramified place over 7. These are explicit choices for this definite-group calculation. [Loeffler’s group and two integral classes](https://arxiv.org/pdf/0801.3176#page=6)

There is a sign that can make this whole calculation misleading. The rational central element $-I$ acts on a line by $-1$ and on its two-dimensional quotient with determinant $+1$. The Legendre symbol of $-1$ at 571 is $-1$. Putting the quadratic character on the line alone, while retaining all the other indicated types, gives **zero**. Twisting on the GL(3) side exchanges the two local descriptions, but the corresponding twist on the unitary group acts at 7 as well. For example, the base-change character on $K^\times\backslash\mathbb A_K^\times$ is $\psi\circ N_{K/\mathbb Q}$. On the norm-one torus its descent is $\lambda(a/\bar a)=\psi(Na)$. This is well-defined since $\psi$ is quadratic. At the ramified place take $a=\sqrt{-7}$ to represent $-1$. The unramified local quadratic character takes $N(a)=7$ to $\psi(7)=-1$. This supplies the second sign. A zero from twisting just the split-prime type would give the wrong test.

## Two independent dimension counts

Write $\omega=(1+\sqrt{-7})/2$. The two maximal-level classes in Loeffler's calculation have stabilizers of orders 48 and 336. The first consists of signed permutation matrices. The second also contains the order-seven generator
$$ \frac12\begin{pmatrix}-1&1-\omega&1\\-1&\omega-1&1\\\omega&0&\omega\end{pmatrix}. $$
Both classes have representatives trivial at 571. Reducing $\omega$ by either root of $\omega^2-\omega+2$ modulo 571 gives a group action on the $571^2+571+1=326613$ lines in $\mathbb F_{571}^3$. [The two stabilizers and their generator](https://arxiv.org/pdf/0801.3176#page=6) · [Parahoric refinement by the line action](https://arxiv.org/pdf/0801.3176#page=12)

For each $g$ in the stabilizer, count lines in each eigenspace of $g$ with eigenvalue $u\in\mathbb F_q^\times$. An eigenspace of dimension $s$ contributes $(q^s-1)/(q-1)$ lines. Weight each by $\left(\frac{\det(g)/u}{q}\right)$ for the quotient character. Averaging is the trace of the projector to invariants. The second calculation traverses each orbit and propagates the character along the generators. An orbit contributes one precisely when signs agree along every path to the same line.

| Maximal-level stabilizer | Trivial character | Quadratic on the line only | Quadratic on the quotient determinant |
| --- | ---: | ---: | ---: |
| Order 48 | 13,825 | 0 | 13,396 |
| Order 336 | 2,017 | 0 | 1,874 |
| Total | 15,842 | 0 | **15,270** |

The index times the original mass is $326613/42=15553/2$. Both embeddings at 571 give the same dimensions. Since 5 divides neither stabilizer order, the averaging argument and the supported-orbit basis work in characteristic five as well.

## One function distinguishes conjugate operators

Let $\mathfrak p=(\omega)$ above 2. In the principal-to-principal block the six rational representatives of its Hecke operation are the three diagonal placements of $\omega/(1-\omega)$ among two ones, and three cyclic row permutations of
$$ \begin{pmatrix}1&0&0\\0&\omega/2&-\omega/2\\0&\omega/2&\omega/2\end{pmatrix}. $$
The seventh neighbor lies in the other maximal-level class. Conjugating the six representatives gives the opposite split-prime operator on the principal block. These are local double cosets at 2, with the level at 571 held fixed. [Loeffler’s six principal neighbors and seventh coset](https://arxiv.org/pdf/0801.3176#page=6)

Use $\omega=159\bmod571$, let $v=(1,2,3)$, and take $y=(1,157,521)$. A scalar function on nonzero vectors represents the chosen character by
$$F(tv)=\left(\frac tq\right)F(v),\qquad
 F(gv)=\left(\frac{\det g}{q}\right)F(v)\quad (g\text{ a principal stabilizer}).$$
Indeed the function on matrices is $\left(\frac{\det k}{q}\right)F(ke_1)$, whose right translation by a line stabilizer gives exactly the determinant character on the quotient. Define $F(y)=1$, extend it by these rules on the stabilizer orbit of the line $y$, and set it to zero on other orbits and on the second maximal-level class. The sign propagation verifies that this defines a function.

The row for the six representatives $\gamma$ at $v$ is $\sum_\gamma(\frac{\det\gamma}{q})F(\gamma^{-1}v)$. The seventh term vanishes by the support choice. The two results are
$$ (T_{\mathfrak p,1}F)(v)=1,\qquad (T_{\bar{\mathfrak p},1}F)(v)=0. $$
Consequently these two linear maps differ even modulo 5. In characteristic zero the operators at this unramified split place commute and are adjoints for the positive inner product on algebraic modular forms, since the inverse spherical double coset is the conjugate one. A normal operator with entirely real eigenvalues would equal its adjoint. The comparison space therefore has a nonreal Hecke eigenvalue at 2. The calculation has not isolated a system with the required mod-five residual characters. In Loeffler’s unnormalized degree-one convention that system would have both eigenvalues congruent to $2+\psi(2)(2^2+1)=-3\equiv2\bmod5$ at this prime.

## What the source does with a conjugate trace

For each place $w$ the release defines a finite index set with a **complex-valued** trace function. Conjugation is allowed to permute the indices. The classification map sends an admitted representation to a label and recovers its trace there. Two labels may have the same numerical trace. In forming its integer the proof takes a product of the factors $(Nw)^j(t_s-t_{\rm Eis})$ over the whole label and character sets. Conjugation permutes this product. It imposes no individual reality condition on $t_s$. The final bound takes absolute values of factors after forming the integer. Thus these particular statements can accommodate the measured directional difference. [Labels and trace function](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/AdmissibleResidues/WinDefs.lean#L70-L90) · [Construction of the integer](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/AdmissibleResidues/FrobeniusTraceCountBoundOfRatEigensystemCount.lean#L329-L355) · [Where the operation is used for the place $w$](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/KeepNumU.lean#L31-L47)

## Source copies used on 24 November 2026

These hashes identify the author or preprint PDFs linked in the four order-five receipts. The mathematical uses and their hypotheses are recorded at the respective steps.

| Use | Copy and locator | SHA-256 |
| --- | --- | --- |
| Order-five arithmetic | Belabas–Gangl, Section 7.1, unstarred discriminant 571 | `c9fe853678b39807b9033a0593618c58c1034abe249184a547ffeada15987148` |
| Degree-two wild kernel | Jaulent–Michel, introduction and Section 1 | `60b3a693502f8cbd5e9be42cfce477dc6476b83f2aabfdcf87be8e6c0d3ffd3d` |
| Classical conductor | Saito, Section 2c | `76be87c49eb2fc44d43076173c8f9762b6ef8d20bfa7d3a3a4aac201523c4cf7` |
| Minimal Serre level | Billerey–Menares, arXiv 1604.01173v2, Theorem 1 | `aa41a60593fabef3d700023a1cbbc76757059c3ef6bc1ac02dd88da22ea32e08` |
| Quadratic base change | Clozel–Rajan, arXiv 1806.02513, prime-degree case | `d63e845fb86bb7dcdb01f72480374894161ebc289ab52eee1b7e97d84d1d2b4d` |
| Self-dual descent | Ramakrishnan, Theorem A and Corollary B | `54b25c1e2b2e02d7ecb934ba294bcc73975d323e773a836235bec497e1632a11` |
| Unitary lattice classes | Loeffler, arXiv 0801.3176, Sections 3 and 5 | `6564899bc6a8959e9f086a0871994f10f16a33d2de623d3156cf880d868df23d` |

## Unresolved

The sparse row and the dimension answer questions about the specified definite group. To compare a specific system with the published existential, one must keep the correct local type at 7, identify the same eigensystem at multiple split places, and check its residual and ordinary conditions at 5. Neither the dimension nor the row above supplies such an identification.
