# The degree required to distinguish one lattice edge

**Corpus and derivation.** This result was developed in Christopher Daniel Pang’s PAL research program with Hearthline. Pang’s audit asks how much precision a fixed observation can spend to distinguish competing inputs. Hearthline wrote the mathematical argument. [PAL v2.4-M, Mathematical Realization Atlas](../corpus/PAL_v2.4-M_Mathematical_Realization_Atlas.docx) · [APCI v1.0.0, Exact Certification Through a Declared Interface](../corpus/APCI_Declared_Interface_v1.0.0.docx)

**Proof inputs and the release.** The release supplies its source lattice, local rank predicate and Frobenius coordinates. The binary degree bound and its equality examples are independently counted here.

[Proof collection](README.md) · [Dated receipt and supporting checks](../receipt-archives/2026-11-23-edge-separation.md) · [Contribution record](PROVENANCE.md)

**23 November 2026.** We tested the edge-isolation requirement identified in the [four-operator calculation](../receipt-archives/2026-11-23-correlated-places.md). For a binary form of degree $d$ in one Frobenius factor, a vector can gain at most $\lfloor d/q\rfloor$ extra powers of the uniformizer on **every** competing edge, where $q$ is the residue field size of the source lattice. The bound is sharp. At $q=289$ this gives a concrete instance in which the release's local rank predicate fails for every positive claimed rank, even in degree 4,045. We then tested the same obstruction with two active Frobenius factors. The second factor can lower the cost of distinguishing one edge from 289 degrees to 33. [The rank predicate under test](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean#L200-L220)

## Match the source lattices

Let $p\ge5$, let $n'$ be even and positive, and put $q=p^{n'}$. Take $W$ to be the integers of the unramified extension of $\mathbb Q_p$ of degree $n'$. For the coefficient ring $O$, take the integers of the unramified extension of degree $2n'$ and adjoin $w$ with $w^2=p$. Then $w$ is a uniformizer. The source Frobenius acts on $\mathbb F_q$ by $t\mapsto t^p$. These rings even meet the stronger local setting in the release. Each integer unit has a square root in $O$ by reduction and lifting, and powers of $p$ have square roots from $w$. [Coefficient and residue-field requirements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean#L12-L35)

Use rank-two source lattices, $r=1$, weight $(d,0)$ in slot zero and weight zero in every other slot. The coefficient space consists of homogeneous binary forms of degree $d$. The column degrees in the source definition are $(d,0)$, so only the first polynomial column occurs. The invariance under adding the first column to the second is then automatic. The determinant twist has exponent zero. On a given lattice the integral forms are exactly those whose coefficients are integral after substitution in a basis. [Polynomial representation](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GradedWeylDivisibility/StatementA.lean#L14-L32) · [Lattice membership in a basis](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GradedWeylDivisibility/StatementD.lean#L126-L138) · [Frobenius factors and weights](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean#L65-L89)

Choose a basis of a fixed source $W^2$. Its outgoing edges correspond to the $q+1$ lines $\ell$ in $\mathbb P^1(\mathbb F_q)$, by taking the inverse image of a line between $W^2$ and $p^{-1}W^2$. The intermediate coefficient lattice at that edge is $w^{-1}O a+O b$ for a lifted basis with $a$ spanning $\ell$ in the residue field. Write $h_\ell(H)$ for the minimum $w$-valuation of the coefficients of the nonzero form $H$ in this lattice's basis. This is exactly its order relative to the release's `HLe`. A basis change over $O$ preserves that order in both directions. [Edges and intermediate lattices](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean#L100-L125)

## A sharp bound on the extra divisibility

Move the chosen line to $\infty=[0:1]$. A common scalar shifts all $h_\ell$ equally, so write the form after scaling as $H=w^d A$, where $A$ has integral coefficients and at least one unit coefficient. Thus $h_\infty(H)\ge0$. For each finite $t\in\mathbb F_q$, use its Teichmüller lift $[t]$. The complete polynomial in the competing chart is

$$
 H(w^{-1}U,[t]w^{-1}U+V)=A(U,[t]U+wV).
$$

Write $a(T)=A(1,T)$. The coefficient of $U^{d-j}V^j$ is $w^j a^{[j]}([t])$, where $a^{[j]}(t)$ means the coefficient of $Z^j$ in $a(t+Z)$. Suppose the gain over the selected edge is at least $c\ge1$ at every competitor. Then all these coefficients have valuation at least $h_\infty(H)+c\ge c$. For $j<c$, reduction gives $\bar a^{[j]}(t)=0$. Thus every one of the $q$ distinct finite points is a root of multiplicity at least $c$ of the same polynomial $\bar a$. This polynomial is nonzero because $A$ is homogeneous and primitive. Counting roots with multiplicities yields $qc\le d$.

For equality put $c=\lfloor d/q\rfloor$ and take

$$
 A(X,Y)=Y^{d-qc}\left(\prod_{t\in\mathbb F_q}(Y-[t]X)\right)^c.
$$

At infinity the coefficient of $V^d$ in $A(wU,V)$ is one. At the competitor $t$, the factor $Y-[t]X$ contributes $wV$ in the displayed chart. Every competitor therefore gains at least $c$, and the degree bound gives equality for the minimum. This calculation uses coefficients on whole lattices, including the transverse variable $V$.

## Consequence for the actual local rank predicate

For each candidate generator $F_i$ in `LPprimeAt`, return to its own source lattice and selected edge $e_i$. Write $H_i=w^{A_r}F_i$, where $A_r$ is the exponent `Ar`. The off-edge condition puts $H_i$ in $w^{c_*}HLe(e')$ on every competing edge. The sharp bound forces $H_i\in w^{c_*-\lfloor d/q\rfloor}HLe(e_i)$. Zero generators satisfy this as well. On the target side $w^{A_r}G$ belongs to the dual of $HLe(e_i)$. Since $p^{A_r}=w^{2A_r}$, the release's pairing is the evaluation of $w^{A_r}G$ on $H_i$. Every entry, including every integral combination allowed in `GoodRankK`, lies in $w^{c_*-\lfloor d/q\rfloor}O$. A positive rank would require an entry equal to $p^D=w^{2D}$. Hence

$$
   \kappa<1 \quad\Longrightarrow\quad d\ge q(c_*-2D)
$$

when the local predicate holds here. The source and target lattices may be subject to further cuts at level $t$. Those cuts only restrict the witnesses. [Paired lattices and normalization](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean#L131-L143) · [All competing edges, target lattice and integral coefficients](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean#L188-L220)

Take $p=17$, $n'=2$, $D=1$, $c_*=16$ and $d=4045$. The largest possible gain is 13. Every matrix entry is divisible by $w^3$, while the required diagonal entry is $17=w^2$. This rules out **every** $\kappa<1$ for every $t$. For $\kappa\ge1$ the predicate admits the empty rank-zero witness. [Zero-rank branch](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/LatticeCountPrimeMonoLevel.lean#L131-L139)

## What a second Frobenius slot changes

Keep the same field and use two polynomial factors. Write their coordinates as $(X_0,Y_0)$ and $(X_1,Y_1)$. A finite line gives points $(1,t)$ and $(1,t^{17})$ at the two slots. Consider the form of bidegree $(17,16)$

$$
 A=Y_0\left(Y_0^{16}Y_1^{16}-X_0^{16}X_1^{16}\right).
$$

At each finite line it reduces to $t(t^{288}-1)=0$. At infinity it takes the value one. In each chart put back the transverse variables with their factor of $w$ as above. The surviving term modulo $w$ is precisely that residue value times the leading monomial. The form $w^{33}A$ gains one power of $w$ on all 289 competitors and has order zero at the chosen edge. The odd slot uses the release's reversed, negated weight convention, so the native input there is $(0,-16)$. [Odd-slot reversal](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean#L59-L79)

Total degree 33 is minimal for a primitive integral bihomogeneous form with a unit value at the selected residue point and zero values at all the others. In bidegree $(a,b)$ only the all-$Y$ monomial survives at infinity. On the finite chart it has exponent $a+17b$. At zero the constant coefficient must vanish. On $\mathbb F_{289}^{\times}$, distinct exponents modulo 288 give linearly independent functions. A positive lower exponent $i+17j$ must therefore coincide modulo 288 with the highest exponent, with $i\le a$, $j\le b$. Equivalently $(a-i)+17(b-j)$ is a positive multiple of 288. Replace 17 copies in either coordinate of this difference by one in the other. Each replacement preserves its residue modulo 288 and reduces its total size by 16. The terminal nonzero digits lie between 0 and 16, and the only such pair giving zero residue is $(16,16)$. The initial difference thus consumes at least 32 units of degree, with at least one further unit required by $i+17j>0$. The [finite-field check](../receipt-archives/check_edge_separation.py) tests every line and all bidegrees up to the minimum.

For unevenly spaced active slots $0=s_0<\cdots<s_{h-1}<n'$, set $s_h=n'$ and $P_j=p^{s_{j+1}-s_j}$. The same argument gives the exact minimum total degree $1+\sum_j(P_j-1)$ for this leading residue-value test. The finite exponent of the highest term is $\sum d_jp^{s_j}$. To collide with a lower positive exponent, its digit difference must be a positive multiple of $q-1$. Carrying $P_j$ copies at slot $j$ into one at the next slot, cyclically, leaves that residue fixed and decreases the sum of the digits. A positive terminal digit string has value at most $q-1$, with equality only at the digits $P_j-1$. One additional unit is needed for the positive lower exponent. Equality is achieved by $Y_0(\prod_jY_j^{P_j-1}-\prod_jX_j^{P_j-1})$, since $\sum_j p^{s_j}(P_j-1)=q-1$. Raising this form to the $c$th power gives a gap of at least $c$ at all competitors. This last construction gives an upper bound on the degree needed at higher order.

## Unresolved

The rank-one edge theorem used for larger primes requires at least two even top positions and a polynomial matrix size of at least five. The other prime branch uses $r\ge2$. The binary one-slot obstruction genuinely falsifies the local predicate for the stated inputs. The selected global inputs have additional active slots. Even two slots can share the work of separation as the calculation shows. The open question is how many independent target directions survive the required order on all competing edges **with the release's actual degrees, Frobenius gaps and permitted loss**. [Large-prime hypotheses](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/ProjectionLemmaBaseLevel.lean#L40-L57) · [Counting the even top positions](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/ObjSeg.lean#L294-L303) · [Other prime range](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/Joints.lean#L2016-L2035) · [Use of both local results](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/Joints.lean#L2097-L2127) · [Public audit key](../receipt-archives/../RH-PROOF-WORK-KEY.md)
