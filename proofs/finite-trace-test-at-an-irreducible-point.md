# Finitely many word traces detect an irreducible deformation

**Corpus and derivation.** Pang asked where a residue can be read after one observation loses it. The PAL/APCI test compares the local reading with observations of products. Developed in Christopher Daniel Pang’s PAL research program with Hearthline, 24 November 2026. [PAL atlas](../corpus/PAL_v2.4-M_Mathematical_Realization_Atlas.docx) · [APCI](../corpus/APCI_Declared_Interface_v1.0.0.docx)

**Proof inputs and the release.** The proof uses a matrix-unit basis and the trace pairing. Carayol already proved rigidity from equality of all traces. Hearthline gave the finite test and the rank-three calculation. The Alpöge–Claude release supplies the application to irreducible arithmetic points.

[Proof collection](README.md) · [Dated derivation and sources](../receipt-archives/2026-11-24-finitely-many-word-traces-detect-an-irreducible-deformation.md) · [Contribution record](PROVENANCE.md)

## A residue you can see with two matrices

Take three free generators $g,h,k$. In rank three set $g=I$, $h=\operatorname{diag}(1,2,4)$ and let $k$ cyclically permute the three coordinate axes. Work over the rationals and allow $\epsilon^2=0$. Change only $g$, to $\operatorname{diag}(1+\epsilon,1-\epsilon,1)$. Every power of $g$ has the same trace and characteristic polynomial as before. But the trace of $gh$ goes from $7$ to $7-\epsilon$. Keeping a matrix that distinguishes the first two coordinates makes the lost term visible.

There is an exact hypothesis here. If the group has only the generator $g$, the changed representation has the same traces on every group element, and it cannot be conjugate to the identity representation. With $h,k$ present, the base representation is absolutely irreducible. An $h$-invariant subspace is spanned by a subset of its distinct eigenlines, and $k$ permutes them transitively.

## A finite test over a local ring

Let $R$ be a commutative local ring with residue field $K$. Let two representations $\rho,\rho':G\to\mathrm{GL}_n(R)$ have the same reduction $\bar\rho$, and suppose the $K$-span of $\bar\rho(G)$ is $M_n(K)$. Absolute irreducibility implies this spanning condition by the matrix-algebra density theorem. Let $S$ be a finite generating set of the group. Choose words $b_1=1,b_2,\ldots,b_{n^2}$ in $S$ whose residual matrices form a basis.

**Theorem.** The representations are conjugate by a matrix equal to $I$ modulo the maximal ideal if and only if their traces agree on
$$b_i b_j\quad\text{and}\quad s b_i b_j
\qquad (1\le i,j\le n^2,\ s\in S).$$
One can choose the $b_i$ of length at most $n^2-1$, giving at most $(|S|+1)n^4$ readings of length at most $2n^2-1$. The statement includes mixed characteristic and nilpotent coefficients.

**Choosing the basis.** Start with the span of the identity, and successively allow one more generator on the left. If the dimension stops increasing, the span is stable under left multiplication by every generator. Left multiplication by each generator is invertible and the span is finite dimensional, so it is also stable under the inverse. Hence it contains $\bar\rho(G)$ and is the full matrix space. At most $n^2-1$ strict increases are possible. Choose the basis from the words encountered, keeping the identity.

**Proof.** Both families $\rho(b_i)$ and $\rho'(b_i)$ form $R$-bases since their reductions form a basis. The trace pairing $\operatorname{tr}(XY)$ on $M_n(R)$ is perfect: $E_{ij}$ pairs to one with $E_{ji}$ and to zero with the other matrix units. The Gram matrix in either chosen basis is therefore invertible, and the pair readings make the two Gram matrices identical.

For each $s$ and $i$, expand $\rho(s)\rho(b_i)$ in the first basis. Pairing with every $\rho(b_j)$ recovers its coefficients by solving the Gram system with right-hand side $\operatorname{tr}\rho(s b_i b_j)$. The other representation gives the same coefficients. The $R$-linear isomorphism $T$ sending each basis matrix to its counterpart consequently satisfies $T(\rho(s)Y)=\rho'(s)T(Y)$ for every $Y$. This also holds for inverse generators, hence for all words. It fixes $I$, maps every $\rho(g)$ to $\rho'(g)$, and by linearity in the left factor is an algebra automorphism of $M_n(R)$. Its reduction is the identity.

For an explicit conjugating matrix $X$, take column $i$ to be $T(E_{i1})e_1$. Then $X\equiv I$ in the residue field, so $X$ is invertible. The matrix-unit product rule gives $T(E_{jk})X e_i=\delta_{ki}X e_j$, hence $T(E_{jk})=XE_{jk}X^{-1}$. This proves one direction. Conjugation preserves traces, proving the converse.

The same finite construction works for continuous representations with a finite set of **topological** generators if $R$ is Hausdorff topological and the reductions of their words span $M_n(K)$. First compare on the dense generated subgroup, then extend equality by continuity. The test asks for traces of products. Knowing separate characteristic polynomials of the individual generators does not supply those mixed values. For wider existence and uniqueness results for determinants over rings, see [Chenevier on pseudorepresentations](https://arxiv.org/abs/0809.0415).

## Test of all 27 first-order directions

In the example choose $b_{ij}=h^i k^j$ for $0\le i,j\le2$. The first three powers of $h$, starting at the identity, span all diagonal matrices because the Vandermonde determinant for $1,2,4$ is nonzero. The powers of $k$ move these diagonals onto the three cyclic matrix diagonals. The longest basis word has length four.

The pair and triple lists contain 172 distinct words of length at most nine. The [exact rank-three check](../receipt-archives/check_irreducible_trace_words.py) allows all 27 entries of the three generator perturbations to vary. It computes the derivative of every requested trace by matrix multiplication. Over each of $\mathbf F_5,\mathbf F_7,\mathbf F_{11}$ the resulting matrix has rank 19. The eight independent simultaneous conjugation directions lie in its kernel and exhaust it. In particular the derivative on $g$ alone is zero and the derivative on $gh$ is $-1$ for the displayed deformation. Run `python -B check_irreducible_trace_words.py` from the receipt archive.

## Connection to the audit

The release compares generalized Hecke dimensions at irreducible points and uses the comparison in an assertion about fixed-weight derivations. Its global determinant is evaluated on group elements. In characteristic zero it determines their traces as characteristic-polynomial coefficients. Thus a first-order deformation of an actual absolutely irreducible group representation that preserved all those traces would already be a change of basis. At an inert local parameter the [reciprocal pair](recovering-the-inert-spherical-parameter.md) can still move without changing the local polynomial. These facts describe different observations of the same proposed change. [Irreducible-point hypotheses](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/CuspidalDescent/GLDenseRanges/EigBoxE.lean#L102-L106) · [Use for fixed-weight derivations](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/UnrE.lean#L21-L39)

## Unresolved

A deformation could change a global trace while preserving the weight. Ruling that out on the particular arithmetic component is stronger than detecting a change from its traces. The free-group example establishes the distinction. Applying the finite bound to an explicit arithmetic presentation would also require actual generators and mixed-word readings.
