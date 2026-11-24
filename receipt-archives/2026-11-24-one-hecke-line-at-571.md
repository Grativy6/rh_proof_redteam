# One Hecke eigenline survives at level 571

**24 November 2026.** The [earlier directed row](2026-11-24-directed-hecke-test-at-level-571.md) gave different answers to the two Hecke operations above 2. We have now applied both operations to the entire 15,270-dimensional space. Seven vectors span the first eigenspace modulo 5. Its intersection with the opposite eigenspace has dimension five. Testing the same vectors at 11, 23 and 29 leaves **exactly one line**. It passes both directions at every split rational prime up to 79, including 71 and 79 where the predicted answer differs from the trivial representation. There are four characteristic-zero eigensystems above it. Their trace differences give a [sharp numerical test](2026-11-24-two-ramified-hecke-fields.md) of the release’s factor two.

The arithmetic input is $\ell=5$, $q=571$, $j=1$ and $\psi=\chi_{-571}$. In the source’s Case I the relevant Selmer group has [order exactly five](2026-11-24-an-order-five-class-and-a-hundred-missing-levels.md). The unitary field is $K=\mathbb Q(\sqrt{-7})$. For a good split prime $p$ the required degree-one Hecke eigenvalue in the unnormalized, integer convention is $p+\psi(p)(p^2+1)\bmod5$. This follows from multiplying the trace of $\{\psi(p)p,1,\psi(p)p^{-1}\}$ by $p$. The congruence is the same in both directions. [Frobenius comparison in the release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/NumberU3US.lean#L30-L45) · [Where the character orbit enters](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/FPropGKU.lean#L150-L172)

## Replay the finite calculation

From the root of the repository run the following with Python 3 and NumPy. The optional matrix export writes two integer Matrix Market files. The independent rank verifier needs a C++17 compiler. On Linux the following commands also check that all 15,270 coordinates were covered.

```sh
python -B receipt-archives/hecke-571/packet.py --minor primary-minor.mtx
c++ -O3 -march=native -fopenmp -std=c++17 receipt-archives/hecke-571/certify_minor.cpp -o certify_minor
OMP_NUM_THREADS=4 ./certify_minor primary-minor.mtx 571
```

The [driver](hecke-571/packet.py) regenerates all the local neighbours and signed actions and checks the supplied [13-vector witness](hecke-571/primary_vectors.json). The witness contains only field elements from 0 through 4. Its decoded SHA-256 is checked before use. Supply `--export-two DIR` to write the two operators at 2. Their file digests are `4beacfe62f7212f7d3bfaa2b4649e80a3d7a8e25092f94ae5f5f238e3fe58f3f` and `7d2e6bcddca52b640d18b2e01d1a5f6f062566c1ad584966573a80f2070745c5`.

## Completing the missing blocks at 2

Loeffler’s two maximal-level classes have stabilizers $\Gamma_0,\Gamma_1$ of orders 48 and 336. In the chosen 2-adic embedding the second lattice is $L_-=\{x\in\mathbb Z_2^3:\sum x_i\equiv0\bmod2\}$. Its dual is $L_+=\mathbb Z_2^3+\frac12\mathbb Z_2{\bf1}$. Write $\omega=(1+\sqrt{-7})/2$ and use the embedding where $\omega$ is a uniformizer. The positive operator has a single neighbor from the principal class to the second class with rational transporter 1. For the opposite direction an explicit transporter is
$$D=I+\omega^{-2}{\bf1}{\bf1}^{t}.$$
It is unitary because its eigenvalue on the constant line is $-\bar\omega^2/\omega^2$ and it fixes the orthogonal plane. It sends $L_-$ into $L_+$, and its determinant has valuation $-2$, so this inclusion is equality. The six principal-to-principal representatives are those of the [first calculation](2026-11-24-directed-hecke-test-at-level-571.md). In the reverse block the seven choices come from the cosets of an order-48 subgroup in $\Gamma_1$. Both $\Gamma_0$ and $D^{-1}\Gamma_0D$ occur this way. Powers $1,\tau,\ldots,\tau^6$ of Loeffler’s element of order seven give a transversal in both cases. There is no second-to-second entry. [Loeffler, Section 3](https://arxiv.org/pdf/0801.3176#page=6) · [Complete assembly](hecke-571/operators.py)

At 571 the fiber is the set of lines in $\mathbb F_{571}^3$, with character $\left(\frac{\det\text{ on the two-dimensional quotient}}{571}\right)$. The coordinate of a function is its value on a line representative, extended by the prescribed signs around its stabilizer orbit. A neighbor represented by $\gamma$ acts by evaluating the destination function at $\gamma^{-1}v$, with its determinant and line-scaling signs. This gives 13,396 supported orbits in the first lattice class and 1,874 in the second. Each directed matrix has **106,024 nonzero integer entries**. With $W_{ii}=336/|\operatorname{Stab}(i)|$ we checked $WT=T_{\rm opp}^tW$ and $TT_{\rm opp}=T_{\rm opp}T$ in every row over the integers.

## The other places

At a split prime with generator $\pi$, the $p^2+p+1$ neighbours of the forward operator are labelled by the image hyperplanes modulo $\pi$. For each stabilizer orbit of planes we find an actual isometry $\gamma=B/\lambda$. With source and destination lattice classes $i,j\in\{0,1\}$ use $\lambda=\bar\pi\,\omega^j\bar\omega^i$. The program checks $B^\dagger B=N(\lambda)I$ and
$$\det B=\pi\bar\pi^2\omega^{i+2j}\bar\omega^{2i+j}.$$
It checks the image plane modulo $\pi$ and the lattice at 2. Explicitly, in the $\omega$-adic embedding use $\alpha=\left(\begin{smallmatrix}1&0&0\\0&1&0\\-1&-1&2\end{smallmatrix}\right)$ and $\alpha_0=I,\alpha_1=\alpha$. The integrality test on $\alpha_i^{-1}\gamma\alpha_j$ uses $\omega=2\bmod4$. Its determinant is a local unit. Everywhere else away from $p$ integrality follows from the denominators and unitarity. At $\pi$ the image has index $p$ by the determinant. This certifies each neighbor and its local direction. Traversing the entire set of planes proves coverage. Interchanging $\pi,\bar\pi$ generates the other operator independently. At 11 the two tables satisfy the integer mass-adjoint identity on all 1,984,669 nonzero positions in each direction. [Split-prime construction](hecke-571/split_neighbors.py)

At an inert prime $p$, label the new self-dual lattice $L'$ by $pL'$ modulo $p^2$. Its primitive vectors reduce to an isotropic line $v$ over $\mathbb F_{p^2}$. For an integral coordinate lift $v_0$ with one coordinate 1, a primitive generator can be written $v_0+p y$ after scaling. Its remaining datum is $s=\langle v_0,y\rangle\bmod p$, subject to $s+\bar s=-\langle v_0,v_0\rangle/p\bmod p$. The other generators are $p v^\perp$. This yields $p$ choices above each of $p^3+1$ isotropic lines. The same integral frame and determinant tests certify isometries, now with leading denominator $p$. At ramified 7 use $\varpi=\sqrt{-7}$ with $\bar\varpi=-\varpi$. The residue lines are the eight points of the isotropic conic in $\mathbb P^2(\mathbb F_7)$. The correction $s$ has seven possibilities since its contribution to the norm modulo $\varpi^2$ cancels. This gives 56 neighbours. The full mass-weighted tables at 5 and 7 are symmetric, on 9,143,223 and 836,823 nonzero positions respectively. [Inert primes](hecke-571/inert_neighbors.py) · [Ramified prime](hecke-571/ramified_neighbors.py)

| Last split prime in the intersection | Required reading modulo 5 | Common eigenspace dimension | Common generalized eigenspace dimension |
| ---: | ---: | ---: | ---: |
| 2 | 2 | 5 | 12 |
| 11 | 3 | 4 | 9 |
| 23 | 3 | 2 | 8 |
| 29 | 1 | 1 | 4 |

The same eigenline then gives $2,3,3,2,4,2$ in both directions at $37,43,53,67,71,79$ respectively. Its support has 12,121 coordinates. At the nonsplit primes $3,5,7$ it gives $4,0,1$ respectively. The [local-parameter calculation](2026-11-24-matching-the-unitary-level.md) identifies the normalization of those readings. By commutation any good Hecke operator preserves the one-dimensional space. This proves there is a single simultaneous residual eigensystem here. To identify its character at untested primes we use the [separate global argument](2026-11-24-global-residual-character-at-571.md).

## Why the finite search is exhaustive

Let $A=T_{\mathfrak p,1}-2I$ at the first prime above 2. The supplied $U$ has 13 independent columns and is $A$-invariant. Direct multiplication gives nullities $7,10,13,13$ for the first four powers of $A|_U$. To rule out any other generalized vector we certify that $[A\mid-U]$ has full row rank. This makes the induced endomorphism on the quotient by $U$ surjective and therefore invertible. The exported square minor has size 15,270 and SHA-256 `6fb63964ca2b784195d7820d0ede52471bc5dc9f88020c129791865d17ac913a`. The omitted column numbers are in the witness.

The [independent verifier](hecke-571/certify_minor.cpp) works in $\mathbb F_5[t]/(t^3+t+1)$. This cubic has no root in $\mathbb F_5$. It multiplies the minor by an invertible diagonal and generates $2n=30540$ exact scalar Krylov moments $u^tB^iv$. Berlekamp–Massey gives recurrence degree $n=15270$ and nonzero constant coefficient 87 in the program’s base-five encoding for seed 571. Seed 7129 gives the same degree and constant coefficient 27. These are positive nonsingularity certificates. Cayley–Hamilton supplies a monic recurrence of degree $n$. A full-degree scalar recurrence from $2n$ terms is its characteristic recurrence, so its nonzero constant term forces the determinant to be nonzero. A failed seed would give no certificate. Changing to $\mathbb F_{125}$ preserves the rank of the original matrix. The initial witness was found separately by [panel row elimination](hecke-571/discover_kernel.cpp) and iterating $A^{-1}U$ via the augmented matrices. Small singular and nonsingular controls and direct substitution of the computed vectors were also checked.

The [run record](hecke-571/verification.json) gives the source-copy hashes, code versions, matrix digests, and the independently checked ranks. All cited results are applied on their stated hypotheses. The large public RH development was not compiled to obtain these numerical or field-theoretic results.

## Unresolved

This finite calculation checks a specific character and twist. Its consequences for the four characteristic-zero candidates, the global Galois residue and the scope of the RH audit are recorded in the [trace calculation](2026-11-24-two-ramified-hecke-fields.md) and the [global comparison](2026-11-24-global-residual-character-at-571.md).
