# A sharp loss inside the jet estimate

**Corpus and derivation.** This result was developed in Christopher Daniel Pang’s PAL research program with Hearthline. Pang’s declared-interface test motivates measuring exactly how many digits of a jet survive an integral change of frame. Hearthline wrote the mathematical argument. [PAL v2.4-M, Mathematical Realization Atlas](../corpus/PAL_v2.4-M_Mathematical_Realization_Atlas.docx) · [APCI v1.0.0, Exact Certification Through a Declared Interface](../corpus/APCI_Declared_Interface_v1.0.0.docx)

**Proof inputs and the release.** The release provides the jet estimate and its formal hypotheses. The one-variable examples and sharp loss are calculated in this audit.

[Proof collection](README.md) · [Dated receipt and supporting checks](../receipt-archives/2026-11-23-jet-loss-and-frames.md) · [Contribution record](PROVENANCE.md)

**23 November 2026.** This test supplies the full local hypotheses of the release’s jet estimate in a one-variable specialization. For infinitely many orders, an integral kernel gives **one whole unit less** divisibility than the leading term suggests. We prove that a loss of one is sharp on this specialization. A separate example shows how checking only frames over a finite residue field can manufacture arbitrarily many apparent extra factors of the prime. The release includes an error term and invokes a polynomial coefficient bound. [The quantified estimate and its error term](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GaussJetBounds/StatementP.lean#L33-L51)

## Exact minimum relative to the leading term

Let $p\ge5$ be prime, $q=p^2$, $\gamma=p/(q-1)$ and $v_p(p)=1$. Put
$$
 L(T)=T+\sum_{j\ge1}p^{-j}T^{q^j},\qquad g=L^{-1}
$$
under composition. For every integral series $U$ and $n\ge1$,
$$
 v_p\big(n![X^n]U(g(X))\big)\ \ge\ \gamma n-1 .
$$
Use $v_p(0)=+\infty$. The constant one cannot be decreased uniformly. Already the fixed integral unit $U(T)=1+T^{q-1}$ gives equality at $n=(q-1)q^h$ for every $h\ge0$. At $p=5$ the first two orders are $24$ and $600$, with valuations $4$ and $124$. The corresponding leading terms are $5$ and $125$.

**Proof.** It suffices to treat $U(T)=T^k$ with $1\le k\le n$, since only finitely many coefficients contribute. By Lagrange inversion, multiplying the coefficient by $n!$ gives a sum of terms
$$
 (-1)^M\,k\,\frac{(n+M-1)!}{\prod_j m_j!}\,p^{-\sum_j j m_j},
 \quad M=\sum_jm_j,\qquad n-k=\sum_j(q^j-1)m_j .
$$
Write $s_p(a)$ for the sum of the base-$p$ digits of $a$. The identity $n+M-1=k-1+\sum_j q^j m_j$ gives $s_p(n+M-1)\le s_p(k-1)+\sum_j s_p(m_j)$. Legendre's factorial formula and $s_p(k-1)=s_p(k)-1+(p-1)v_p(k)$ now bound the valuation of each term below by
$$
 \frac{n-s_p(k)}{p-1}-\sum_j j m_j
 \ \ge\ \gamma n+\frac{k}{q-1}-\frac{s_p(k)}{p-1}.
$$
The second inequality uses $j\le(q^j-1)/(q-1)$. In the base-$p$ expansion of $k$ the contribution of its $i$th digit $d_i$ to $s_p(k)/(p-1)-k/(q-1)$ is $d_i(p+1-p^i)/(q-1)$. Only the first two places make a positive contribution, and their total is at most one.

For equality let $k=q-1$, $n=kq^h$, $m_1=q^h-1$ and all other $m_j=0$. Adding $k-1$ to $qm_1$ gives no carries. The two digit bounds are equalities. Every other partition of $n-k$, if present, uses some $j\ge2$, and then $j<(q^j-1)/(q-1)$. Thus this is the unique term of smallest valuation, which proves the equality without a numerical approximation.

## Does the example meet the actual local hypotheses?

Take an orbit of length two, with one top site. Let $\beta=0$ and choose one of the series variables at that site. Set the full kernel to $1+g(X)^{q-1}$ in that variable. In orbit length two the site's height-two logarithm uses that same variable at each Frobenius-square step. Substitution by $L$ returns $1+X^{q-1}$. Thus the factor called $U$ is integral, and all the difference, torus and coefficient-field conditions for $\beta$ hold. Take $K_0=\mathbb Q_p$ and take the prescribed root of unity in $\mathbb C_p$. [Logarithm and admissibility conditions](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GaussJetBounds/Statement.lean#L68-L96) · [Factorization and integral remainder](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/Divisibility/ProductZerothFirstParts.lean#L182-L205)

At the top site choose a one-row Young diagram of length $n$ and use an empty diagram at the other site. Choose the first target column for every size-one minor. Take $a=n$, any even $N_0\ge2\lceil\log_p n\rceil+4$, and $N_1=N_0+1$. These choices satisfy the dimension and size conditions. The coefficient of the $n$th power of the first frame entry in the jet polynomial is exactly $n![X^n]U(g(X))$. There are no ordinary-row degrees and the incoming capacity is zero. The printed leading exponent is $\sum_{j\ {\rm odd},\,j\ge1}n/p^j=\gamma n$. The source subtracts $2N_0N_1(\log_p n+1)$. Our example breaks the estimate with its error removed, including at orders where the leading exponent is already an integer. It stays within the printed estimate. [Local objects](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/DataJet.lean#L17-L32) · [Minor and ordinary derivative](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/Divisibility/ProductZerothFirstParts.lean#L82-L102) · [Strict rank condition](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/Divisibility/ProductZerothFirstParts.lean#L128-L138) · [Capacity and top term](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/Divisibility/ProductZerothFirstParts.lean#L154-L180) · [Actual loss](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GaussJetBounds/StatementP.lean#L44-L51)

## Can all arithmetic frames conceal a bad coefficient?

Let the unramified field in which the frames are sampled have residue cardinality $Q=p^f$. Put $D(X,Y)=X^QY-XY^Q$. Every integral pair gives a value divisible by $p$, but $[X^QY]D=1$. At $(1,p)$ the valuation is exactly one. This row can be completed to an invertible integral frame.

This is also an example made from the permitted jet data. At the same top site take two variables in one target column and put $U=1+D^m$ on them, with $\beta=0$. The inverse Honda substitutions have linear term the identity, so the degree $n=m(Q+1)$ part of the resulting kernel is $D^m$. Choose a one-row diagram of that length and select the same target column in each minor, with the dimension choices above. The complete degree-$n$ directional derivative in the frame $\mathbf Y$ is
$$
 n!\,D(Y_1,Y_2)^m .
$$
Its least coefficient valuation is $v_p(n!)$. Its least value valuation over all the integral frames in this field is $v_p(n!)+m$. This discrepancy is unbounded as $m$ varies.

The release reads the polynomial over a **Gauss-norm extension** of $\mathbb C_p$. For indeterminates $Y_i$, set the norm of a polynomial to the maximum of its coefficient norms. Normalizing each nonzero polynomial by a coefficient of largest norm and reducing proves multiplicativity, because the residue polynomial ring is a domain. The norm therefore extends to the field of fractions. Evaluation at the indeterminates reads the coefficient maximum exactly. The proof raises some indeterminates to positive powers. This preserves the norm since the resulting map on exponent vectors is injective. The coefficient-field inclusion is isometric. Only the established formal-series relations are transported, and the substitutions have zero constant term. Each coefficient reads finitely many input coefficients. [Construction of the extension](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GaussJetBounds/GaussJetProofs/GField.lean#L230-L247) · [Data transported and the frame polynomial](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GaussJetBounds/FrameJetEval.lean#L10-L37) · [Transport of the hypotheses](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L163-L196) · [Where the coefficient is recovered](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GaussJetBounds/GaussJetProofs/ThmAGaussOf.lean#L37-L55)

For one fixed polynomial over $\mathbb C_p$ there is a further hand check. After normalizing by a maximal coefficient, choose a finite residue extension containing its reduced coefficients and having more elements than each individual variable degree. A nonzero reduced polynomial cannot vanish at every tuple over that field, by induction using the univariate root bound. Multiplying first by the frame determinant, and increasing the field size accordingly, also enforces invertibility. This degree-dependent check explains why a fixed physical residue field failed in the preceding example.

## One longer Frobenius link

The flow term in the printed bound also distinguishes genuinely different orders. On a four-site cycle set the ordinary-row capacities to $(p^3M,0,0,M)$ with $M>0$. An edge of odd length $j$ carrying $x$ consumes $p^jx$ at its source and $x$ at its target. The length-three edge from site 0 to site 3 can carry $M$. Every usable edge touches site 3 and costs at least its own flow there, so $M$ is the maximum. If only the directed one-step edges were kept, the sole usable edge would run from 3 to 0 and could carry just $M/p$. The lower-bound term $\gamma\sum D-\mathrm{maxFlow}(D)$ would then be overstated by $M(1-1/p)$. Positive small capacities at the other sites also allow a growing difference: replacing each zero by $c$ bounds the total one-step flow by $M/p+c(1+2/p)$.

The local definition includes both odd lengths on this cycle. The second-embedding bound uses that full flow functional with capacities determined by the proof’s weights. We did not identify the sparse test capacities with those global weights. [Odd edges, their costs and the objective](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/IncomingBounds/IncomingBound.lean#L12-L32) · [Occurrence in the second-embedding estimate](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/OrbitBoundOverSecondEmbeddingAnyBasePoint.lean#L32-L45)

## Reproduce the calculation

Run `python receipt-archives/check_honda_jet_loss.py`. It compares Lagrange inversion with repeated application of the invariant differential operator $(L'(T))^{-1}d/dT$ using exact arithmetic. The proof above covers all orders. The script gives a finite check of both computations.

## Unresolved

These examples satisfy the local formal-series hypotheses. Their realization as a prescribed global theta kernel is a further question. The released coefficient estimate survives both tests. The next quantitative issue is how the error and the longer Frobenius links are accounted for when local divisibility is summed over the selected primes. [CM coordinate and its actual normalization](../receipt-archives/2026-11-23-height-two-coordinate.md) · [Audit key](../receipt-archives/../RH-PROOF-WORK-KEY.md)
